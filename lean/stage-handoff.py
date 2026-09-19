"""Build a staged Lean file one theorem at a time, stopping on the first failure."""
from pathlib import Path
import re
import subprocess
import sys

source, module, start = sys.argv[1], sys.argv[2], int(sys.argv[3])
text = Path(source).read_text()
parts = text.split('-- CHECKPOINT')
namespace = re.search(r'^namespace (\S+)', text, re.M).group(1)
target = Path(module.replace('.', '/') + '.lean')
for count in range(start + 1, len(parts)):
    prefix = '-- CHECKPOINT'.join(parts[:count]) + '-- CHECKPOINT\n'
    target.write_text(prefix + '\nend ' + namespace + '\n')
    theorem = re.findall(r'^theorem (\w+)', prefix, re.M)[-1]
    print('Checking ' + theorem, flush=True)
    subprocess.run(['bash', 'build-handoff.sh', theorem, module], check=True)
    print('CHECKED ' + str(count) + ' ' + theorem, flush=True)
