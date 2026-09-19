"""Check exact preservation of every source already compiled in goal round 2."""
from pathlib import Path
import json
import subprocess

baseline = '8d79137'
paths = subprocess.check_output(
    ['git', 'ls-tree', '-r', '--name-only', baseline, 'ProvenHashes'],
    text=True).splitlines()
checked = []
for name in paths:
    if not name.endswith('.lean'):
        continue
    original = subprocess.check_output(['git', 'show', f'{baseline}:{name}'])
    assert Path(name).read_bytes() == original, name
    checked.append(name)
root = subprocess.check_output(['git', 'show', f'{baseline}:ProvenHashes.lean'])
assert Path('ProvenHashes.lean').read_bytes().startswith(root)
print(json.dumps({'result': 'PASS', 'baseline_commit': baseline,
                  'preserved_source_modules': len(checked),
                  'root_imports_preserved': True}, indent=2))
