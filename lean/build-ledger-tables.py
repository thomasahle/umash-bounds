"""Build independent checked tables within this lane's fixed CPU affinity."""
from concurrent.futures import ThreadPoolExecutor
import subprocess
import sys

def build(s):
    for label in ('HighData', 'HighPrepared'):
        command = ['python3', 'build-round6-stage.py',
                   f'Round7{label}{s}.stage.lean', f'ProvenHashes.UMASH{label}{s}']
        subprocess.run(command, check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(f'TABLE {s} CHECKED', flush=True)

workers = int(sys.argv[1]) if len(sys.argv) > 1 else 4
with ThreadPoolExecutor(max_workers=workers) as executor:
    list(executor.map(build, range(1, 16)))
