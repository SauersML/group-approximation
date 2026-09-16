import sys, ast, time
from fastsat import solve
# usage: follow.py nS nM scanfile n budget [start] [stop] [filter]
nS, nM = int(sys.argv[1]), int(sys.argv[2])
fname = sys.argv[3]; n = int(sys.argv[4]); budget = int(sys.argv[5])
start = int(sys.argv[6]) if len(sys.argv) > 6 else 0
stop = int(sys.argv[7]) if len(sys.argv) > 7 else 10**9
filt = sys.argv[8] if len(sys.argv) > 8 else 'Y'
rows = []
for line in open(fname):
    if not line.startswith('('): continue
    i = line.index(')'); Tf = ast.literal_eval(line[:i+1])
    rest = line[i+1:].strip(); j = rest.index(')'); Tr = ast.literal_eval(rest[:j+1])
    res = rest[j+1:].split()[0]
    if filt in res: rows.append((Tf, Tr, res))
stats = {}
t0 = time.time()
for idx, (Tf, Tr, res) in enumerate(rows[start:stop]):
    ok, _, _ = solve(nS, nM, Tf, Tr, n, budget=budget)
    c = 'Y' if ok else ('N' if ok is False else '?')
    key = res + c
    stats[key] = stats.get(key, 0) + 1
    if c != 'Y' or key.count('Y') < key.count('Y'):
        print(Tf, Tr, res + c, 'NONMONO' if 'YN' in key else '', flush=True)
print(len(rows), stats, time.time() - t0, flush=True)
