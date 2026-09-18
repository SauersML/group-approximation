# Re-run the finiteness certificate with a larger cap on the classes that survived the pipeline SAT
# (both images uncertified at cap 4000, or one uncertified).  usage: bigcap.py census.json cap idx...
import sys, json
from lo_census import load, finite_image
path, cap = sys.argv[1], int(sys.argv[2]); want = set(map(int, sys.argv[3:]))
for i, G in load(path):
    if i in want:
        print(json.dumps(dict(census=path, idx=i, cap=cap, finH=finite_image(G, True, cap), finV=finite_image(G, False, cap))), flush=True)
