#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=4G
#SBATCH --time=00:12:00
#SBATCH --job-name=bhf54-rev2
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-54/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-54
python3 -c "import ast; [ast.parse(open(f).read()) for f in ('revlib.py','rev2.py')]; print('syntax ok')"
python3 - <<'PY'
import threading, sys, runpy
sys.setrecursionlimit(200000)
threading.stack_size(1 << 28)
sys.argv = ["rev2.py", "540", "14"]
t = threading.Thread(target=lambda: runpy.run_path("rev2.py", run_name="__main__"))
t.start(); t.join()
PY
