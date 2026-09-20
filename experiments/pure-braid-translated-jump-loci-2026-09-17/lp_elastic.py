"""Where does the lowest-vertex assignment of a certificate break on a twist hyperplane?
Elastic version of lp_cone.py: minimise the total violation sum s_r of the constraints
row_r . x >= 1 - s_r, s_r >= 0, subject to sum a = 0 and c_A = 0.  The rows with s_r > 0 at
the optimum (L1 relaxations tend to be sparse) indicate the cells whose lowest vertex
must change on the hyperplane.  Prints those cells, grouped by their block structure.
Usage: python3 lp_elastic.py cert.json 'A_json_list'"""
import sys, json, itertools, collections
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, hstack, identity, csr_matrix
from fast_morse import Salvetti

def main():
    cert = json.load(open(sys.argv[1]))
    zeroA = [tuple(sorted(A)) for A in json.loads(sys.argv[2])]
    n, K = cert["n"], cert["K"]
    S = Salvetti(n); P = S.P
    a0 = np.array([float(x) * K for x in cert["a"]]); eta0 = np.array(cert["eta"], dtype=float)
    npair, N = len(P), len(S.ch)
    rows, info = [], []
    for k, (ci, F) in enumerate(S.cells):
        st = S.stars[F]
        sep = (S.side[st] != S.side[ci]).astype(float)
        f = sep @ a0 + eta0[st]
        j = int(np.argmin(f)); v = st[j]
        for t, D in enumerate(st):
            if D == v:
                continue
            r = np.zeros(npair + N); r[:npair] = sep[t] - sep[j]; r[npair + D] += 1; r[npair + v] -= 1
            rows.append(r); info.append((k, int(v), int(D)))
    R = csr_matrix(np.array(rows))
    M = len(rows)
    A_ub = hstack([-R, -identity(M)]).tocsr()
    b_ub = -np.ones(M)
    eqs = [np.concatenate([np.ones(npair), np.zeros(N)])]
    for A in zeroA:
        e = np.zeros(npair + N)
        for p in itertools.combinations(A, 2):
            e[P.index(p)] = 1
        eqs.append(e)
    e0 = np.zeros(npair + N); e0[npair] = 1; eqs.append(e0)
    A_eq = hstack([csr_matrix(np.array(eqs)), csr_matrix((len(eqs), M))]).tocsr()
    c = np.concatenate([np.zeros(npair + N), np.ones(M)])
    bounds = [(None, None)] * (npair + N) + [(0, None)] * M
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=np.zeros(len(eqs)), bounds=bounds, method="highs")
    print("status", res.status, "total violation", round(res.fun, 4))
    s = res.x[npair + N:]
    viol = [(info[r], s[r]) for r in range(M) if s[r] > 1e-7]
    print("violated rows", len(viol))
    bytype = collections.Counter()
    for (k, v, D), val in viol:
        ci, F = S.cells[k]
        typ = tuple(sorted(tuple(sorted(B)) for B in F if len(B) > 1))
        bytype[typ] += 1
    for typ, cnt in bytype.most_common(20):
        print("  nontrivial blocks", typ, "violations", cnt)
    for (k, v, D), val in viol[:15]:
        ci, F = S.cells[k]
        print("   cell base", S.ch[ci], "blocks", [sorted(B) for B in F], "low", S.ch[v], "vs", S.ch[D], round(val, 3))

if __name__ == "__main__":
    main()
