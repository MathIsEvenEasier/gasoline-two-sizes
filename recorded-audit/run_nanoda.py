"""Independent, bounded Nanoda replay. Invoked only by the Azure Lean driver."""
import collections
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import urllib.request


TARGETS = ['Gasoline.assignment_to_fraction', 'Gasoline.fraction_to_assignment', 'Gasoline.normalization', 'Gasoline.reach_iff', 'Gasoline.prefix_lower', 'Gasoline.prefix_attained', 'Gasoline.Integer.score_formula', 'Gasoline.Integer.approximation', 'Gasoline.Integer.compared_to_schedule', 'Gasoline.Integer.ratio_bound', 'Gasoline.Integer.run_realizable', 'Gasoline.Integer.exact_ratio_witness']
ALLOWED = ['propext', 'Quot.sound', 'Classical.choice']


def require(value, message):
    if not value:
        raise RuntimeError(message)


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def inspect_export(path):
    names, axioms, declarations, unsafe = {0: ''}, [], set(), []
    counts = collections.Counter()
    with path.open() as stream:
        for line in stream:
            row = json.loads(line)
            if 'in' in row:
                item = row.get('str', row.get('num'))
                if item is not None:
                    prefix = names[item['pre']]
                    names[row['in']] = prefix + ('.' if prefix else '') + str(item.get('str', item.get('i')))
            for kind in ('axiom', 'def', 'thm', 'opaque', 'quot', 'inductive'):
                if kind not in row:
                    continue
                counts[kind] += 1
                item = row[kind]
                items = ([item] if kind != 'inductive' else
                         item['types'] + item['ctors'] + item['recs'])
                for entry in items:
                    name = names[entry['name']]
                    declarations.add(name)
                    if kind == 'axiom':
                        axioms.append(name)
                    if entry.get('isUnsafe') or entry.get('isPartial') or entry.get('safety') in ('unsafe', 'partial'):
                        unsafe.append(name)
    require(set(axioms) <= set(ALLOWED), 'Unapproved axiom in export: ' + repr(axioms))
    require(not unsafe, 'Unsafe or partial declarations in export')
    return axioms, declarations, dict(counts)


def audit_nanoda(lean, command, root):
    require(Path('/run/mathiseasy-azure-verified').is_file(), 'Azure supervisor required')
    pins = json.loads((root / 'tool-pins.json').read_text())
    tools = Path('/opt/pinwheel-nanoda-tools')
    tools.mkdir(exist_ok=True)
    os.environ['PATH'] = str(Path(lean).parent) + ':' + os.environ['PATH']
    os.environ['CARGO_BUILD_JOBS'] = '2'
    # Stack space is an execution resource; no checker source or rule is changed.
    _, stack_hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (512 * 1024**2, stack_hard))

    def stage(args, name, timeout=300, cwd=root, expected_zero=True, export=False):
        print('NANODA ' + name, flush=True)
        old = Path.cwd()
        try:
            os.chdir(cwd)
            code, seconds = command(args, str(root / ('nanoda-' + name + ('.ndjson' if export else '.log'))), timeout,
                                    str(root / ('nanoda-' + name + '-stderr.log')) if export else None)
        finally:
            os.chdir(old)
        if expected_zero:
            require(code == 0, 'Nanoda stage failed: ' + name + ' (exit ' + str(code) + ')')
        return code, seconds

    installer = tools / 'rustup.sh'
    urllib.request.urlretrieve('https://sh.rustup.rs', installer)
    stage(['sh', str(installer), '-y', '--profile', 'minimal', '--default-toolchain', pins['rust']], 'rust-install', 300)
    os.environ['PATH'] = str(Path.home() / '.cargo/bin') + ':' + os.environ['PATH']
    rust_version = subprocess.check_output(['rustc', '--version'], text=True).strip()
    require(rust_version.startswith('rustc ' + pins['rust'] + ' '), 'Rust version mismatch')
    for name, repo in [('exporter', 'leanprover/lean4export'), ('nanoda', 'ammkrn/nanoda_lib')]:
        dest = tools / name
        stage(['git', 'init', str(dest)], name + '-init')
        stage(['git', '-C', str(dest), 'remote', 'add', 'origin', 'https://github.com/' + repo + '.git'], name + '-remote')
        stage(['git', '-C', str(dest), 'fetch', '--depth', '1', 'origin', pins[name]], name + '-fetch')
        stage(['git', '-C', str(dest), 'checkout', '--detach', 'FETCH_HEAD'], name + '-checkout')
        got = subprocess.check_output(['git', '-C', str(dest), 'rev-parse', 'HEAD'], text=True).strip()
        require(got == pins[name], 'Tool revision mismatch')
    (tools / 'exporter/lean-toolchain').write_text('leanprover/lean4:v' + pins['lean'] + '\n')
    stage([str(Path(lean).parent / 'lake'), 'build'], 'exporter-build', 300, tools / 'exporter')
    stage(['cargo', 'build', '--release', '--locked'], 'checker-build', 300, tools / 'nanoda')
    for name in ('exporter', 'nanoda'):
        args = ['git', '-C', str(tools / name), 'diff', 'HEAD', '--', '.']
        if name == 'exporter':
            args.append(':!lean-toolchain')
        require(not subprocess.check_output(args), 'Checker/exporter sources modified')
    exporter = tools / 'exporter/.lake/build/bin/lean4export'
    checker = tools / 'nanoda/target/release/nanoda_bin'
    config = {'use_stdin': False, 'permitted_axioms': ALLOWED,
              'unpermitted_axiom_hard_error': True, 'unsafe_permit_all_axioms': False,
              'num_threads': 1, 'nat_extension': True, 'string_extension': True,
              'print_success_message': True, 'print_axioms': True,
              'unknown_pp_declar_hard_error': True, 'pp_to_stdout': True,
              'pp_options': {'proofs': False, 'notation': False, 'width': 100}}

    # First check a real tiny proof, then change its claimed type to False.
    (root / 'NanodaControl.lean').write_text(
        'def NanodaControl.falseType : Prop := False\n'
        'theorem NanodaControl.probe : True := True.intro\n')
    stage([lean, '-o', 'NanodaControl.olean', 'NanodaControl.lean'], 'control-compile')
    stage([str(exporter), 'NanodaControl', '--', 'NanodaControl.falseType', 'NanodaControl.probe'], 'control-export', export=True)
    good_export = root / 'nanoda-control-export.ndjson'
    good_config = dict(config, export_file_path=good_export.name, pp_declars=['NanodaControl.probe'])
    (root / 'nanoda-control-good.json').write_text(json.dumps(good_config, indent=2) + '\n')
    stage([str(checker), 'nanoda-control-good.json'], 'control-good')
    rows = [json.loads(line) for line in good_export.read_text().splitlines()]
    name_map, false_expr, changed = {0: ''}, None, False
    for row in rows:
        if 'in' in row:
            item = row.get('str', row.get('num'))
            if item is not None:
                pre = name_map[item['pre']]
                name_map[row['in']] = pre + ('.' if pre else '') + str(item.get('str', item.get('i')))
        if 'def' in row and name_map[row['def']['name']] == 'NanodaControl.falseType':
            false_expr = row['def']['value']
    require(false_expr is not None, 'Control False expression missing')
    for row in rows:
        if 'thm' in row and name_map[row['thm']['name']] == 'NanodaControl.probe':
            row['thm']['type'] = false_expr
            changed = True
    require(changed, 'Control theorem missing')
    bad_export = root / 'nanoda-control-bad.ndjson'
    bad_export.write_text(''.join(json.dumps(row) + '\n' for row in rows))
    (root / 'nanoda-control-bad.json').write_text(json.dumps(dict(good_config, export_file_path=bad_export.name), indent=2) + '\n')
    bad_code, _ = stage([str(checker), 'nanoda-control-bad.json'], 'control-bad', 60, expected_zero=False)
    require(bad_code in (1, 101), 'Corrupted proof was not rejected normally')

    # Export only the target theorems and their complete transitive dependencies.
    stage([str(exporter), 'Result', '--', *TARGETS], 'proof-export', 300, export=True)
    proof = root / 'nanoda-proof-export.ndjson'
    axioms, declarations, counts = inspect_export(proof)
    require(set(TARGETS) <= declarations, 'Export omits a requested target')
    (root / 'nanoda-proof-config.json').write_text(json.dumps(dict(config, export_file_path=proof.name, pp_declars=TARGETS), indent=2) + '\n')
    _, seconds = stage([str(checker), 'nanoda-proof-config.json'], 'proof-check', 1200)
    log = (root / 'nanoda-proof-check.log').read_text()
    match = re.search(r'Checked (\d+) declarations with no errors', log)
    require(match is not None, 'Missing Nanoda success marker')
    result = {'status': 'PASS', 'targets': TARGETS, 'tool_pins': pins,
              'rust_version': rust_version, 'export_axioms': axioms,
              'export_counts': counts, 'export_bytes': proof.stat().st_size,
              'export_sha256': digest(proof), 'unsafe_or_partial_declarations': [],
              'checked_declarations': int(match[1]), 'checker_seconds': seconds,
              'source_unmodified': True, 'exporter_changes': ['lean-toolchain'],
              'control_rejected': True, 'control_exit_code': bad_code,
              'tool_sha256': {'exporter': digest(exporter), 'nanoda': digest(checker)},
              'checker_config': config, 'formal_statement_independently_reviewed': False}
    # Keep a compact reproducible export in the returned archive, not a duplicate.
    with proof.open('rb') as source, gzip.open(root / 'nanoda-proof-export.ndjson.gz', 'wb', compresslevel=6) as dest:
        shutil.copyfileobj(source, dest)
    proof.unlink()
    result['export_gzip_sha256'] = digest(root / 'nanoda-proof-export.ndjson.gz')
    (root / 'nanoda-report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result
