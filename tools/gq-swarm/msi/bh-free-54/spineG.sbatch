#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=6G
#SBATCH --time=00:09:00
#SBATCH --job-name=bhf54-spineG
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-54/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-54
python3 -c "import ast; [ast.parse(open(f).read()) for f in ('ore.py','spineG.py')]; print('syntax ok')"
python3 - <<'PY'
import threading, sys, runpy
sys.setrecursionlimit(100000)
threading.stack_size(1 << 28)
sys.argv = ["spineG.py", "440", "10"]
t = threading.Thread(target=lambda: runpy.run_path("spineG.py", run_name="__main__"))
t.start(); t.join()
PY
