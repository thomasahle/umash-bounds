"""Append a staged module one declaration at a time, retaining each successful build."""
from pathlib import Path
import re
import subprocess
import sys

stage = Path(sys.argv[1])
module = sys.argv[2]
path = Path(module.replace('.', '/') + '.lean')
source = stage.read_text()
chunks = source.split('-- CHECKPOINT\n')
assert chunks[-1].strip() == 'end ProvenHashes.UMASH'
previous = path.read_text() if path.exists() else ''
for number in range(1, len(chunks)):
    candidate = '-- CHECKPOINT\n'.join(chunks[:number]) + '-- CHECKPOINT\n\nend ProvenHashes.UMASH\n'
    if previous.startswith(candidate.rsplit('end ProvenHashes.UMASH', 1)[0]):
        continue
    assert not previous or candidate.startswith(previous.rsplit('end ProvenHashes.UMASH', 1)[0].rstrip()), 'Already compiled prefix changed'
    name = re.findall(r'^(?:theorem|lemma)\s+(\w+)', chunks[number-1], re.M)[-1]
    path.write_text(candidate)
    result = subprocess.run(['bash', 'build-part2.sh', name, module])
    if result.returncode:
        if previous:
            path.write_text(previous)
        else:
            path.unlink()
        sys.exit(result.returncode)
    previous = candidate
