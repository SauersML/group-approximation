#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=6G
#SBATCH --time=00:10:00
#SBATCH --job-name=bhf54-combo
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-54/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-54
python3 -c "import ast; [ast.parse(open(f).read()) for f in ('ore.py','spineG.py','revlib.py','spinecheck.py','gen.py','tdlib.py','sclog.py')]; print('syntax ok')"
for job in "spinecheck.py 240" "sclog.py 230"; do
set -- $job
echo "=== $1"
python3 - "$1" "$2" <<'PY'
import threading, sys, runpy
sys.setrecursionlimit(100000)
threading.stack_size(1 << 28)
script, tl = sys.argv[1], sys.argv[2]
sys.argv = [script, tl]
t = threading.Thread(target=lambda: runpy.run_path(script, run_name="__main__"))
t.start(); t.join()
PY
done
