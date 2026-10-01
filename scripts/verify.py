"""Replay the fixed public cases using two independent exact implementations."""
import json
from pathlib import Path
from fast_algorithm import solve
from oracle import iterative_rounding, capacity

root = Path(__file__).resolve().parent.parent
fixtures = json.loads((root/'site/fixtures.json').read_text())
scores = 0
for item in fixtures:
    x, y, policy = item['x'], item['y'], item['policy']
    if policy != 'original':
        x = sorted(x, reverse=policy == 'large')
    fast, independent = solve(x, y, True), iterative_rounding(x, y, True)
    assert fast['order'] == independent['order'] == item['expected']['order']
    expected_steps = [
        {**step, 'candidate_values': {int(k): v for k, v in step['candidate_values'].items()}}
        for step in item['expected']['steps']
    ]
    assert fast['steps'] == independent['steps'] == expected_steps
    assert fast['initial_lp'] == item['expected']['initial_lp']
    assert fast['capacity'] == item['expected']['capacity']
    assert fast['capacity'] == independent['capacity'] == capacity(fast['order'], y)
    scores += sum(len(step['candidate_values']) for step in fast['steps'])
print(json.dumps({'status': 'PASS', 'fixed_cases': len(fixtures), 'candidate_scores': scores}))
