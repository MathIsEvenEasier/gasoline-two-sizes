"""Clean Azure build, axiom audit, negative control, and independent Nanoda replay."""
import hashlib,json,os,pathlib,re,shutil,subprocess,tarfile,time,urllib.request
ROOT=pathlib.Path(__file__).resolve().parent
assert pathlib.Path('/run/mathiseasy-azure-verified').is_file()
os.chdir(ROOT);start=time.monotonic()
report={'status':'RUNNING','location':'Azure','modules':[],'nanoda_verified':False}
modules=['Assignment','Reachability','IntegerModel','Rounding','Normalization','Sharpness','Schedules','Ties','Result']
def digest(p):return hashlib.file_digest(pathlib.Path(p).open('rb'),'sha256').hexdigest()
def command(args,log,timeout,stderr=None):
 remaining=1950-(time.monotonic()-start)
 if remaining<1:raise RuntimeError('Overall audit deadline reached')
 began=time.monotonic()
 with open(log,'w') as out:
  if stderr:
   with open(stderr,'w') as err:p=subprocess.run(args,stdout=out,stderr=err,timeout=min(timeout,remaining))
  else:p=subprocess.run(args,stdout=out,stderr=subprocess.STDOUT,timeout=min(timeout,remaining))
 return p.returncode,round(time.monotonic()-began,3)
def stage(args,name,timeout=300):
 print(name,flush=True);code,sec=command(args,str(ROOT/(name+'.log')),timeout)
 if code:raise RuntimeError(name+' failed with exit '+str(code))
 return sec
try:
 release=json.loads((ROOT/'linux-release.json').read_text());archive=pathlib.Path('/opt/lean.tar.zst')
 urllib.request.urlretrieve(release['browser_download_url'],archive)
 assert digest(archive)==release['digest'].split(':')[1]
 stage(['tar','--zstd','-xf',str(archive),'-C','/opt'],'lean-extract')
 lean='/opt/lean-4.34.0-linux/bin/lean';os.environ['PATH']=str(pathlib.Path(lean).parent)+':'+os.environ['PATH']
 project=pathlib.Path('/opt/gasoline-proof')
 stage(['git','init',str(project)],'mathlib-init')
 stage(['git','-C',str(project),'remote','add','origin','https://github.com/leanprover-community/mathlib4.git'],'mathlib-remote')
 stage(['git','-C',str(project),'fetch','--depth','1','origin','5ed2965256430c3649e86755f9576b54eca72435'],'mathlib-fetch')
 stage(['git','-C',str(project),'checkout','--detach','FETCH_HEAD'],'mathlib-checkout')
 os.chdir(project)
 stage(['lake','exe','cache','get','Mathlib/Basic/Real/Basic.lean','Mathlib/Tactic.lean'],'mathlib-cache',600)
 envpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
 os.environ['LEAN_PATH']=str(ROOT)+':'+':'.join(str(project/pathlib.Path(p)) if not pathlib.Path(p).is_absolute() else p for p in envpath.split(':'))
 os.chdir(ROOT)
 report['tool_pins']=json.loads((ROOT/'pins.json').read_text())
 report['lean_binary_sha256']=digest(lean)
 report['source_sha256']={m+'.lean':digest(ROOT/(m+'.lean')) for m in modules}
 for m in modules:
  source=(ROOT/(m+'.lean')).read_text()
  assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'/\-.*?\-/|--[^\n]*','',source,flags=re.S))
  sec=stage([lean,'-j1','-M8000','-DwarningAsError=true','-DElab.async=false','-o',m+'.olean',m+'.lean'],m,120)
  report['modules'].append({'name':m,'exit_code':0,'seconds':sec})
 from run_nanoda import TARGETS,ALLOWED,audit_nanoda
 log=(ROOT/'Result.log').read_text();report['axioms']={}
 for target in TARGETS:
  match=re.search("'"+re.escape(target)+r"' depends on axioms: \[([^\]]*)\]",log)
  assert match,'Missing axiom audit: '+target
  axioms=[a.strip() for a in match[1].split(',') if a.strip()]
  assert set(axioms)<=set(ALLOWED),'Unexpected axiom'
  report['axioms'][target]=axioms
 (ROOT/'Corrupt.lean').write_text('import Result\nexample : False := by exact True.intro\n')
 code,_=command([lean,'Corrupt.lean'],str(ROOT/'Corrupt.log'),30)
 assert code!=0 and 'error:' in (ROOT/'Corrupt.log').read_text()
 report['negative_control_rejected']=True
 stage(['python3','tie_scan.py'],'tie-scan',60)
 report['nanoda']=audit_nanoda(lean,command,ROOT)
 report['nanoda_verified']=True
 report['status']='PASS'
except Exception as e:
 report['status']='FAIL';report['error']=str(e)
finally:
 report['seconds']=round(time.monotonic()-start,3)
 (ROOT/'formal-audit.json').write_text(json.dumps(report,indent=2)+'\n')
 with tarfile.open(ROOT/'formal-artifacts.tgz','w:gz') as out:
  for p in ROOT.iterdir():
   if p.suffix in {'.lean','.olean','.log','.json','.gz'} and p.name not in {'formal-artifacts.tgz'}:
    out.add(p,arcname=p.name,recursive=False)
 print(json.dumps(report),flush=True)
raise SystemExit(0 if report['status']=='PASS' else 1)
