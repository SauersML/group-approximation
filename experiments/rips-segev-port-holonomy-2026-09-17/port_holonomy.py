#!/usr/bin/env python3
"""Port holonomy is tautological and support rigidity is covering-relative: tests on the (x_4 x_1)^21 face.

Node: rips-segev-port-holonomy-is-tautological-and-f2-blind.

Setting of rips-segev-single-copy-port-equations-are-always-solvable (lines of rows 1..42, In = {0, I1, I2, C},
Out = {0, C, O1, O2}, (I1, I2, O1, O2, C) = 10^(5r-4), ..., 10^(5r)).  The face (x_4 x_1)^21 has long lines L_t
(row 2t+1; in x_1 at I1, out x_4 at O2) and middle lines M_t (row 2t+2; in x_4 at 0, out x_1 at 0).

For each field F_p (p = 2, 3, 10007) and each pair (u, w) (witness pair; three open-regime random pairs):
  1. realize the face: random nonzero edge values c(e), f_T with (f_T w)(exit) = c(e_out), (f_T u)(entry) = -c(e_in);
  2. HOLONOMY: the transfer ratios rho_T = Q_T(exit) / P_T(entry), computed from the realized polynomials, have
     product (-1)^42 = 1 around the face (Theorem A: an identity, not a constraint); over F_2 every rho_T is 1;
  3. FACE-COPY RIGIDITY IS EMPTY: for every face line, the pairs (P on In, Q on Out) with P w = Q u form the zero
     space, so relative to the face copy alone no face coset has a nonzero Rep_T and no ratio is fixed;
  4. ESCAPE COVERING: adding one copy with a line starting at each escaped point z (position 0 is in In and in
     Out) makes every support condition hold, so f_T is in Rep_T; adding the same copies shifted by s makes
     f_T and t^s f_T both lie in Rep_T, so dim Rep_T >= 2 (Theorem B);
  5. INTRINSIC SPACE: a kernel basis of {h : supp(h u) in supp P_T, supp(h w) in supp Q_T}, with h restricted to
     shifts in (supp P_T - supp u) union (supp Q_T - supp w) (a subspace, so its dimension is a lower bound);
     every basis vector is checked to lie in the space; the transfer ratio is 'rigid' on it iff the entry
     functional h -> (h u)(entry) and exit functional h -> (h w)(exit) are proportional there, else 'free'.
     The (dim, rigid/free) histogram over the 42 face cosets is reported.
Exit status 0 iff every check in 2-5 passes.  Runtime about one minute wall (about 10 s CPU).
"""
import random
import sys

random.seed(20260918)


def positions(r):
    I1, I2, O1, O2, C = (10 ** (5 * r - 4), 10 ** (5 * r - 3), 10 ** (5 * r - 2), 10 ** (5 * r - 1), 10 ** (5 * r))
    return [0, I1, I2, C], [0, C, O1, O2]


def mul(f, g, p):
    h = {}
    for i, a in f.items():
        for j, b in g.items():
            h[i + j] = (h.get(i + j, 0) + a * b) % p
    return {e: c for e, c in h.items() if c}


def rank_solve(rows, rhs, p):
    """Gauss-Jordan mod p on sparse rows (dict col -> val).  Returns (rank, one solution or None)."""
    m = [dict(r) for r in rows]
    b = list(rhs)
    piv = []
    for i in range(len(m)):
        for (pr, pc) in piv:
            c = m[i].get(pc, 0)
            if c:
                for col, val in m[pr].items():
                    m[i][col] = (m[i].get(col, 0) - c * val) % p
                b[i] = (b[i] - c * b[pr]) % p
        m[i] = {c: v for c, v in m[i].items() if v}
        if m[i]:
            pc = next(iter(m[i]))
            inv = pow(m[i][pc], p - 2, p)
            m[i] = {c: v * inv % p for c, v in m[i].items()}
            b[i] = b[i] * inv % p
            for (pr, _) in piv:
                c = m[pr].get(pc, 0)
                if c:
                    for col, val in m[i].items():
                        m[pr][col] = (m[pr].get(col, 0) - c * val) % p
                    m[pr] = {cc: v for cc, v in m[pr].items() if v}
                    b[pr] = (b[pr] - c * b[i]) % p
            piv.append((i, pc))
        elif b[i] % p:
            return len(piv), None
    rank_solve.last = (m, piv)
    return len(piv), {pc: b[pr] for (pr, pc) in piv if b[pr]}


def realize(In, Out, u, w, vec, p):
    """f with (f u)(In[j]) = vec[j], (f w)(Out[j]) = vec[4 + j]; f supported on the relevant shifts."""
    shifts = sorted({q - x for q in In for x in u} | {q - y for q in Out for y in w})
    rows = [{s: u[q - s] for s in shifts if (q - s) in u} for q in In]
    rows += [{s: w[q - s] for s in shifts if (q - s) in w} for q in Out]
    return rank_solve(rows, vec, p)[1]


def face_rep_dim(In, Out, u, w, p):
    """dim {(P on In, Q on Out) : P w - Q u = 0}.  Contains Rep_T of a clean face-copy coset."""
    cols = [('P', q) for q in In] + [('Q', q) for q in Out]
    eqs = {}
    for j, (kind, q) in enumerate(cols):
        src = w if kind == 'P' else u
        sgn = 1 if kind == 'P' else -1
        for e, c in src.items():
            eqs.setdefault(q + e, {})
            eqs[q + e][j] = (eqs[q + e].get(j, 0) + sgn * c) % p
    rows = [{j: v for j, v in r.items() if v} for r in eqs.values()]
    rk, _ = rank_solve(rows, [0] * len(rows), p)
    return len(cols) - rk


def intrinsic_dim(Pset, Qset, u, w, p):
    """Lower bound for dim {h : supp(h u) in Pset, supp(h w) in Qset}: h restricted to the natural shifts."""
    shifts = sorted({x - e for x in Pset for e in u} | {x - e for x in Qset for e in w})
    idx = {s: i for i, s in enumerate(shifts)}
    eqs = {}
    for s in shifts:
        for e, c in u.items():
            if s + e not in Pset:
                r = eqs.setdefault(('u', s + e), {})
                r[idx[s]] = (r.get(idx[s], 0) + c) % p
        for e, c in w.items():
            if s + e not in Qset:
                r = eqs.setdefault(('w', s + e), {})
                r[idx[s]] = (r.get(idx[s], 0) + c) % p
    rows = [{j: v for j, v in r.items() if v} for r in eqs.values()]
    rank_solve(rows, [0] * len(rows), p)
    m, piv = rank_solve.last
    pcols = {pc for (_, pc) in piv}
    basis = []
    for fc in range(len(shifts)):
        if fc in pcols:
            continue
        h = {shifts[fc]: 1}
        for (pr, pc) in piv:
            v = m[pr].get(fc, 0)
            if v:
                h[shifts[pc]] = (-v) % p
        basis.append(h)
    return basis


def run_case(name, u, w, p):
    u = {e: c % p for e, c in u.items() if c % p}
    w = {e: c % p for e, c in w.items() if c % p}
    rows = {}
    for t in range(21):
        rows[('L', t)] = 2 * t + 1
        rows[('M', t)] = 2 * t + 2
    # face edges (src, out index in Out, dst, in index in In): x_4 = O2 -> 0, x_1 = 0 -> I1
    edges = []
    for t in range(21):
        edges.append((('L', t), 3, ('M', t), 0))
        edges.append((('M', t), 0, ('L', (t + 1) % 21), 1))
    c = {e: random.randrange(1, p) for e in edges}
    vec = {ln: [0] * 8 for ln in rows}
    entry, exit_ = {}, {}
    for e in edges:
        s, oi, d, ii = e
        vec[s][4 + oi] = c[e]
        vec[d][ii] = (-c[e]) % p
        exit_[s], entry[d] = oi, ii
    ok = True
    # 3. face-copy rigidity is empty
    nonzero_rep = [ln for ln in rows if face_rep_dim(*positions(rows[ln]), u, w, p)]
    ok &= not nonzero_rep
    f = {}
    for ln in rows:
        f[ln] = realize(*positions(rows[ln]), u, w, vec[ln], p)
        if f[ln] is None:
            print(f"  [{name}] FAIL: {ln} not realizable")
            return False
    # 2. holonomy from the realized polynomials
    prod, ratios = 1, []
    for ln in rows:
        In, Out = positions(rows[ln])
        P, Q = mul(f[ln], u, p), mul(f[ln], w, p)
        a, b = Q.get(Out[exit_[ln]], 0), P.get(In[entry[ln]], 0)
        ok &= a != 0 and b != 0
        rho = a * pow(b, p - 2, p) % p
        ratios.append(rho)
        prod = prod * rho % p
    ok &= prod == pow(-1, 42, p) % p
    if p == 2:
        ok &= all(r == 1 for r in ratios)
    # 4. escape covering and shifted copies; 5. intrinsic dimension
    dims = []
    s = 7 * 10 ** 300
    for ln in rows:
        In, Out = positions(rows[ln])
        P, Q = mul(f[ln], u, p), mul(f[ln], w, p)
        esc = (set(P) - set(In)) | (set(Q) - set(Out))
        A = set(In) | esc          # each escaped z starts a new copy's line: 0 in In and in Out
        D = set(Out) | esc
        ok &= set(P) <= A and set(Q) <= D
        A2, D2 = A | {x + s for x in A}, D | {x + s for x in D}
        ok &= {x + s for x in P} <= A2 and {x + s for x in Q} <= D2 and set(P) <= A2
        basis = intrinsic_dim(set(P), set(Q), u, w, p)
        for h in basis:          # every basis vector really lies in the intrinsic space
            ok &= set(mul(h, u, p)) <= set(P) and set(mul(h, w, p)) <= set(Q)
        # transfer ratio is rigid on the space iff the entry and exit functionals are proportional there
        lin = [(mul(h, u, p).get(In[entry[ln]], 0), mul(h, w, p).get(Out[exit_[ln]], 0)) for h in basis]
        free = any((x1 * y2 - x2 * y1) % p for (x1, y1) in lin for (x2, y2) in lin)
        dims.append((len(basis), 'free' if free else 'rigid'))
    hist = {d: dims.count(d) for d in sorted(set(dims))}
    distinct = len(set(ratios))
    print(f"  [{name}] p={p}: |supp u|={len(u)} |supp w|={len(w)}; face lines with nonzero face-copy Rep: "
          f"{len(nonzero_rep)}; holonomy product={prod} (=(-1)^42); distinct transfer ratios={distinct}; "
          f"escape covering and shifted covering ok={ok}; (intrinsic dim, transfer ratio) counts {hist}")
    return ok


def main():
    allok = True
    for p in (2, 3, 10007):
        print(f"field F_{p}")
        if p == 2:
            u, w = {0: 1}, {0: 1, 1: 1}
        else:
            u, w = {0: 1, 1: 2}, {0: 3, 1: 1}
        allok &= run_case("witness {1,a,b,ab}", u, w, p)
        for k in range(3):
            pool = [0, 1, 7] + [10 ** (5 * r - 4) for r in range(1, 14)] + [10 ** (5 * r) for r in range(1, 14)]
            u = {e: random.randrange(1, p) for e in random.sample(pool, 9)}
            w = {e: random.randrange(1, p) for e in random.sample(pool, 8)}
            allok &= run_case(f"open random {k}", u, w, p)
    print("ALL CHECKS PASS" if allok else "SOME CHECK FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
