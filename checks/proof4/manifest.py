#!/usr/bin/env python3
import os,json,hashlib,platform,resource
from pathlib import Path
assert platform.system()=='Linux'
files=[p for p in Path('checks').glob('*') if p.suffix in ('.py','.cpp','.h','.json','.sh','.md') and p.name!='manifest.json']
files += [Path('PROOF4.md'),Path('PROGRESS.md')]
inputs=[Path(s) for s in (
    'PROOF.md','PROOF2.md','PROOF3.md',
    'VERDICT.md','UMASHObligations.lean',
    'umash-enh-verify/VERDICT.md',
    'https://github.com/backtrace-labs/umash/blob/master/umash.pdf','https://github.com/backtrace-labs/umash/blob/master/umash_reference.py')]
assert all(p.is_file() for p in files+inputs)
def hashes(paths):
    return {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}
out=dict(host=platform.node(),python=platform.python_version(),affinity=sorted(os.sched_getaffinity(0)),niceness=os.nice(0),
         address_space_limit=resource.getrlimit(resource.RLIMIT_AS),OMP_NUM_THREADS=os.getenv('OMP_NUM_THREADS'),
         sha256=hashes(files),imported_input_sha256=hashes(inputs))
assert out['affinity']==list(range(40,48)) and out['niceness']>=10
assert out['address_space_limit'][0]<=32_000_000_000
Path('checks/manifest.json').write_text(json.dumps(out,indent=2)+'\n')
