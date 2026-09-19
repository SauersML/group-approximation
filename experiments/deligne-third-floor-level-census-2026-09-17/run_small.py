import sys
import time
from defect import mu, defect_of
from gsets import lines, lagrangians, vectors

pt = [[0] for _ in range(5)]
SETS = {
    'pt': lambda: pt,
    'P3F2': lambda: lines(2)[1],
    'LagF2': lambda: lagrangians(2)[1],
    'P3F3': lambda: lines(3)[1],
    'LagF3': lambda: lagrangians(3)[1],
    'F3^4-0': lambda: vectors(3)[1],
    'P3F5': lambda: lines(5)[1],
    'LagF5': lambda: lagrangians(5)[1],
}

if __name__ == "__main__":
    names = sys.argv[1].split(',')
    theta = eval(sys.argv[2]) if len(sys.argv) > 2 else 1 / 3
    tl = float(sys.argv[3]) if len(sys.argv) > 3 else 300
    for name in names:
        X = SETS[name]()
        t = time.time()
        u, l, a = mu(X, theta, time_limit=tl)
        d = defect_of(X, theta, a) if a is not None else None
        print(f"{name} |X|={len(X[0])} theta={theta:.6f} upper={u} dual={l} "
              f"1/upper={1/u if u else None} recheck={d} secs={time.time()-t:.1f}", flush=True)
