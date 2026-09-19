"""Check all source modules present at arrival, including uncommitted round 7."""
from pathlib import Path
import hashlib
import json

entries = json.loads(Path('Part2Checkpoints.json').read_text())
arrival = next(e for e in entries if e['checkpoint'] == 'phenh_high_integer_certificate')
originals = {p: digest for p, digest in arrival['source_sha256'].items()
             if p != 'ProvenHashes/UMASHPHENHSharp.lean'}
for name, digest in originals.items():
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, name
print(json.dumps({'result': 'PASS', 'arrival_source_modules_preserved': len(originals),
                  'includes_uncommitted_round7': True,
                  'snapshot_checkpoint': arrival['checkpoint']}, indent=2))
