import sys, json
from chern_component_sat import run
N = int(sys.argv[1]); m = int(sys.argv[2])
out = []
for beta in range(0, 2*N+1):
    d = 0
    while True:
        ok, _, _ = run(N, d, m, budget=beta)
        if ok: break
        d += 1
    out.append((beta, d, max(0, N - beta//2)))
    print(json.dumps({'N': N, 'm': m, 'beta': beta, 'min_depth': d, 'guess': max(0, N - beta//2)}), flush=True)
