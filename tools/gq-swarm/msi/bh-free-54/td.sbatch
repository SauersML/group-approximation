#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=4G
#SBATCH --time=00:10:00
#SBATCH --job-name=bhf54-td
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-54/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-54
python3 -c "import ast; [ast.parse(open(f).read()) for f in ('gen.py','td.py')]; print('syntax ok')"
python3 - <<'PY'
import threading, sys, runpy
sys.setrecursionlimit(100000)
threading.stack_size(1 << 28)
sys.argv = ["td.py", "520"]
t = threading.Thread(target=lambda: runpy.run_path("td.py", run_name="__main__"))
t.start(); t.join()
PY
