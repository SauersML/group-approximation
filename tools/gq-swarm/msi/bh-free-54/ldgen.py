# LD_gen: D in O_E(Delta), N a node (in M_E) that is a union of >=2 but not all pieces of D:
# is D|_N hierarchical in N's frame?  Also: greedy hyperplane resolution in rank r = 4, 5, 6.
import sys, json, time, random, itertools
from fractions import Fraction
from ore import *
N = int(sys.argv[1]); t0 = time.time()
def is_node(T, memo_n={}):
    # T in M_E  iff  permutation, or two rows comparable and the reduced matrix is a node
    rows = tuple(tuple(v[k] for v in T) for k in range(3))
    key = tuple(sorted(T))
    if key in memo_n: return memo_n[key]
    if sorted(T) == sorted(DELTA): memo_n[key] = True; return True
    res = False
    for i in range(3):
        for j in range(3):
            if i != j and all(rows[i][c] >= rows[j][c] for c in range(3)):
                newT = [list(v) for v in T]
                for v in newT: v[i] -= v[j]
                if is_node(tuple(tuple(v) for v in newT)): res = True; break
        if res: break
    memo_n[key] = res; return res
def w(p): return Fraction(1, sum(p[0]) * sum(p[1]) * sum(p[2]))
tested = viol = 0; ex = None
for D in up(frozenset([DELTA]), N):
    if len(D) < 3: continue
    Dl = list(D); V = sorted(set(v for t in Dl for v in t))
    for T in itertools.combinations(V, 3):
        if abs(det(*T)) != 1: continue
        T = tri(*T)
        if T in D: continue
        inT = frozenset(p for p in Dl if all(inside(x, T) for x in p))
        if len(inT) < 2 or len(inT) == len(Dl): continue
        if sum(w(p) for p in inT) != w(T): continue
        if not is_node(T): continue
        tested += 1
        if not hier(T, inT):
            viol += 1
            if ex is None: ex = {"D": [list(map(list, t)) for t in sorted(D)], "N": list(map(list, T))}
out = {"N": N, "LD_gen_instances": tested, "violations": viol, "example": ex, "secs": round(time.time() - t0, 1)}
# greedy hyperplane resolution in rank r: split the crossed edge maximizing |l_i|+|l_j|
def resolve(lam, depth, cap):
    P = [k for k in range(len(lam)) if lam[k] > 0]; Q = [k for k in range(len(lam)) if lam[k] < 0]
    if not P or not Q: return 1, depth, True
    if depth > cap: return 1, depth, False
    i, j = max(((a, b) for a in P for b in Q), key=lambda e: abs(lam[e[0]]) + abs(lam[e[1]]))
    l1 = list(lam); l1[j] = lam[i] + lam[j]
    l2 = list(lam); l2[i] = lam[i] + lam[j]
    n1, d1, ok1 = resolve(l1, depth + 1, cap); n2, d2, ok2 = resolve(l2, depth + 1, cap)
    return n1 + n2, max(d1, d2), ok1 and ok2
rnd = random.Random(11); hyper = {}
for r in (4, 5, 6):
    fails = 0; worst = 0; cnt = 0
    for _ in range(300):
        lam = [rnd.randint(-12, 12) for _ in range(r)]
        if not (any(x > 0 for x in lam) and any(x < 0 for x in lam)): continue
        n, d, ok = resolve(lam, 0, 60); cnt += 1
        if not ok: fails += 1
        else: worst = max(worst, d)
    hyper[r] = {"forms": cnt, "not_resolved_within_depth_60": fails, "max_depth_when_resolved": worst}
out["greedy_hyperplane"] = hyper; out["secs_total"] = round(time.time() - t0, 1)
print(json.dumps(out))
