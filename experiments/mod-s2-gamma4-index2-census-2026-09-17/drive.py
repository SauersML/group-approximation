#!/usr/bin/env python3
"""Run index2.py one orbit per process (memory), collecting results.

usage: drive.py OUTDIR orbit [orbit ...]
Each orbit k writes OUTDIR/orbit-k.json and OUTDIR/orbit-k.log.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
out = sys.argv[1]
for k in sys.argv[2:]:
    js = os.path.join(out, f"orbit-{k}.json")
    if os.path.exists(js):
        continue
    with open(os.path.join(out, f"orbit-{k}.log"), "w") as log:
        subprocess.run([sys.executable, os.path.join(HERE, "index2.py"), js, k],
                       stdout=log, stderr=subprocess.STDOUT, check=False)
