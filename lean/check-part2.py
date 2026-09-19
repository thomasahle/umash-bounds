"""Check preserved parent sources and successful per-declaration build records."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

parent = 'a478643'
pattern = r'^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+(\w+)'
old_paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', parent,
                                     'ProvenHashes'], text=True).splitlines()
old_names = set()
for name in old_paths:
    if not name.endswith('.lean'):
        continue
    original = subprocess.check_output(['git', 'show', f'{parent}:{name}'], text=True)
    current = Path(name).read_text()
    namespace = re.search(r'^namespace (\S+)', original, re.M).group(1)
    old_names.update(namespace+'.'+n for n in re.findall(pattern, original, re.M))
    if name == 'ProvenHashes/UMASHConstants.lean':
        prefix = original.rsplit('end ProvenHashes.UMASH', 1)[0]
        assert current.startswith(prefix), name
    else:
        assert current == original, name
new_names = set()
for path in Path('ProvenHashes').glob('*.lean'):
    source = path.read_text()
    namespace = re.search(r'^namespace (\S+)', source, re.M).group(1)
    new_names.update(namespace+'.'+n for n in re.findall(pattern, source, re.M))
new_names -= old_names
entries = json.loads(Path('Part2Checkpoints.json').read_text())
checked = set()
for entry in entries:
    log = Path(entry['log'])
    assert log.exists(), log
    assert hashlib.sha256(log.read_bytes()).hexdigest() == entry['log_sha256'], log
    assert 'Build completed successfully' in log.read_text(), log
    checked.add(entry['checkpoint'])
missing = {n for n in new_names if n.rsplit('.', 1)[1] not in checked}
assert not missing, sorted(missing)
print(json.dumps({'result': 'PASS', 'parent_commit': parent,
                  'preserved_parent_declarations': len(old_names),
                  'new_declarations_with_build_records': len(new_names),
                  'successful_checkpoints': len(entries),
                  'missing_checkpoints': sorted(missing)}, indent=2))
