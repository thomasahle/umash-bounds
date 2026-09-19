"""Package exactly the successful build logs referenced by the checkpoint manifest."""
from pathlib import Path
import hashlib
import json
import tarfile

entries = json.loads(Path('Part2Checkpoints.json').read_text())
paths = {}
for entry in entries:
    path = Path(entry['log'])
    assert not path.is_absolute() and '..' not in path.parts, path
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == entry['log_sha256'], path
    assert b'Build completed successfully' in raw, path
    paths[str(path)] = path
archive = Path('handoff-checkpoint-logs.tar.gz')
temporary = archive.with_suffix('.tmp')
with tarfile.open(temporary, 'w:gz') as target:
    for name, path in sorted(paths.items()):
        target.add(path, arcname=name)
temporary.replace(archive)
print(json.dumps({'result': 'PASS', 'checkpoints': len(entries),
                  'unique_logs': len(paths), 'archive': str(archive),
                  'sha256': hashlib.sha256(archive.read_bytes()).hexdigest()}, indent=2))
