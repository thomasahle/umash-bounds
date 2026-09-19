"""Build every new lemma prefix on the Xeon, retaining all checkpoint logs.

Usage: python3 check_round2.py ProvenHashes/UMASHCarryless.lean [first_checkpoint]
The original source is restored on failure as well as success.
"""
from pathlib import Path
import subprocess
import sys

path = Path(sys.argv[1])
first = int(sys.argv[2]) if len(sys.argv) > 2 else 1
source = path.read_text()
prefix = ''
Path('logs/round2').mkdir(parents=True, exist_ok=True)
try:
    for i, piece in enumerate(source.split('-- CHECKPOINT')[:-1], 1):
        prefix += piece
        if i < first:
            continue
        path.write_text(prefix + '\nend ProvenHashes.UMASH\n')
        log = Path('logs/round2') / (path.stem + '-checkpoint-' + str(i) + '.txt')
        with log.open('w') as out:
            result = subprocess.run(['bash', 'build-umash.sh',
                '.'.join(path.with_suffix('').parts)], stdout=out, stderr=out)
        print(str(log), result.returncode, flush=True)
        if result.returncode:
            print(log.read_text(), flush=True)
            raise SystemExit(result.returncode)
finally:
    path.write_text(source)
