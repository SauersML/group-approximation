#!/usr/bin/env python3
"""One-copy port systems are solvable: realize the (x_4 x_1)^21 face of the gamma = 42 graph.

Node: rips-segev-single-copy-port-equations-are-always-solvable.

For a line i of Steenbock's graph Gamma (row r), put In_i = {0, I1, I2, C} and Out_i = {0, O1, O2, C}, with
(I1, I2, O1, O2, C) = (10^{5r-4}, ..., 10^{5r}).  The port map is
    Phi_i(f) = ( (f u)(p) for p in In_i , (f w)(q) for q in Out_i )  in k^8.
Its image is Dep_i^perp, where Dep_i = {(A, B) : A^v u + B^v w = 0}, A on In_i, B on Out_i, and ^v is t -> 1/t.
Only shifts s with p - s in supp u or q - s in supp w give nonzero columns, so the finite matrix on those shifts
has rank 8 - dim Dep_i exactly.

The script, over F_p for several p:
  1. builds the 42 lines of the face (long lines l_t: in x_1 at I1, out x_4 at O2; middle lines m_t: in x_4 at 0,
     out x_1 at 0), with distinct rows; adds a private neighbour line for every non-face edge of a line with
     Dep != 0 that must carry a value;
  2. for several (u, w) (open-regime random pairs, a witness-support pair, and an adversarial pair that makes one
     face line dependent) finds f_i with Phi_i(f_i) = the prescribed port vector;
  3. checks every b-edge equation Q_l(p) = c(e) = -P_k(p') of the modelled copy, with every other line inactive,
     every face port nonzero, and records how many cosets are pure and how many support points escape the copy;
  4. checks that at most one row among 1..60 has Dep != 0 (Lemma 3 of the proof).
The witness pair (a) is a known non-zero-divisor, so the solvable local system there is a calibration: the
local system cannot see regularity even where it is proved.
Exit status 0 iff every check passes.  Runtime about 2 s.
"""
import random
import sys

random.seed(20260918)


def positions(r):
    I1, I2, O1, O2, C = (10 ** (5 * r - 4), 10 ** (5 * r - 3), 10 ** (5 * r - 2), 10 ** (5 * r - 1), 10 ** (5 * r))
    In = [0, I1, I2, C]     # targets of x_4, x_1, x_2, x_3
    Out = [0, C, O1, O2]    # sources of x_1, x_2, x_3, x_4
    return In, Out


def distinguished(r):
    In, Out = positions(r)
    return sorted(set(In) | set(Out))


IN_LABEL = ['x4', 'x1', 'x2', 'x3']
OUT_LABEL = ['x1', 'x2', 'x3', 'x4']


def mul(f, g, p):
    h = {}
    for i, a in f.items():
        for j, b in g.items():
            h[i + j] = (h.get(i + j, 0) + a * b) % p
    return {e: c for e, c in h.items() if c}


def rank_solve(rows, rhs, p):
    """Gaussian elimination mod p. rows: list of dict col->val. Returns (rank, solution dict or None)."""
    m = [dict(r) for r in rows]
    b = list(rhs)
    piv = []
    rk = 0
    n = len(m)
    for i in range(n):
        # reduce row i by previous pivots
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
            # eliminate pc from previous pivot rows
            for (pr, pc2) in piv:
                c = m[pr].get(pc, 0)
                if c:
                    for col, val in m[i].items():
                        m[pr][col] = (m[pr].get(col, 0) - c * val) % p
                    m[pr] = {cc: v for cc, v in m[pr].items() if v}
                    b[pr] = (b[pr] - c * b[i]) % p
            piv.append((i, pc))
            rk += 1
        elif b[i] % p:
            return rk, None
    sol = {}
    for (pr, pc) in piv:
        sol[pc] = b[pr]
    # free variables are 0; pivot variable value = b (row reduced, other pivot cols eliminated)
    return rk, {c: v for c, v in sol.items() if v}


def port_rows(In, Out, u, w):
    shifts = sorted({q - x for q in In for x in u} | {q - y for q in Out for y in w})
    rows = []
    for q in In:
        rows.append({s: u[q - s] for s in shifts if (q - s) in u})
    for q in Out:
        rows.append({s: w[q - s] for s in shifts if (q - s) in w})
    return rows


def dep_dim(In, Out, u, w, p):
    rk, _ = rank_solve(port_rows(In, Out, u, w), [0] * 8, p)
    return 8 - rk


def realize(In, Out, u, w, vec, p):
    _, sol = rank_solve(port_rows(In, Out, u, w), vec, p)
    return sol


def dep_vectors(In, Out, u, w, p):
    """Basis of Dep_i (left kernel of the 8 x shifts matrix), as 8-vectors."""
    rows = port_rows(In, Out, u, w)
    # augment with identity to track combinations
    aug = [dict(r) for r in rows]
    comb = [{i: 1} for i in range(8)]
    piv = []
    kern = []
    for i in range(8):
        for (pr, pc) in piv:
            c = aug[i].get(pc, 0)
            if c:
                for col, val in aug[pr].items():
                    aug[i][col] = (aug[i].get(col, 0) - c * val) % p
                for col, val in comb[pr].items():
                    comb[i][col] = (comb[i].get(col, 0) - c * val) % p
        aug[i] = {c: v for c, v in aug[i].items() if v}
        if aug[i]:
            pc = next(iter(aug[i]))
            inv = pow(aug[i][pc], p - 2, p)
            aug[i] = {c: v * inv % p for c, v in aug[i].items()}
            comb[i] = {c: v * inv % p for c, v in comb[i].items()}
            piv.append((i, pc))
        else:
            kern.append([comb[i].get(j, 0) % p for j in range(8)])
    return kern


def nullspace(vecs, n, p):
    """Basis of {x in F_p^n : v.x = 0 for all v in vecs}."""
    rows = [list(v) for v in vecs]
    piv_cols = []
    r = 0
    for c in range(n):
        pr = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
        if pr is None:
            continue
        rows[r], rows[pr] = rows[pr], rows[r]
        inv = pow(rows[r][c], p - 2, p)
        rows[r] = [x * inv % p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[r])]
        piv_cols.append(c)
        r += 1
    free = [c for c in range(n) if c not in piv_cols]
    basis = []
    for fc in free:
        x = [0] * n
        x[fc] = 1
        for i, pc in enumerate(piv_cols):
            x[pc] = (-rows[i][fc]) % p
        basis.append(x)
    return basis


def rnd_nonzero(p):
    return random.randrange(1, p)


def run_case(name, u, w, p, rows_of, dep_face=None):
    """Realize the face. rows_of: rows for the 42 face lines. Returns True iff all checks pass."""
    u = {e: c % p for e, c in u.items() if c % p}
    w = {e: c % p for e, c in w.items() if c % p}
    lines = {}      # name -> row
    for t in range(21):
        lines[('L', t)] = rows_of[2 * t]
        lines[('M', t)] = rows_of[2 * t + 1]
    edges = []      # (src, out_idx, dst, in_idx, value)
    face_edges = []
    for t in range(21):
        face_edges.append((('L', t), 3, ('M', t), 0))            # x_4: O2 -> 0
        face_edges.append((('M', t), 0, ('L', (t + 1) % 21), 1))  # x_1: 0 -> I1
    face_ports = {}  # line -> list of (kind, idx) coords that are face ports
    for (s, oi, d, ii) in face_edges:
        face_ports.setdefault(s, []).append(4 + oi)
        face_ports.setdefault(d, []).append(ii)
    deps = {ln: dep_dim(*positions(r), u, w, p) for ln, r in lines.items()}
    # Lemma 3 of the proof, over all rows 1..60 (face rows included)
    ndep_rows = sum(1 for r in range(1, 61) if dep_dim(*positions(r), u, w, p))
    if ndep_rows > 1:
        print(f"  [{name}] FAIL: {ndep_rows} dependent rows among 1..60")
        return False
    dependent = [ln for ln, dd in deps.items() if dd]
    if len(dependent) > 1:
        print(f"  [{name}] FAIL: {len(dependent)} dependent lines")
        return False
    val = {}        # face edge -> value
    extra_rows = iter(range(200, 400))
    if dependent:
        i0 = dependent[0]
        In, Out = positions(lines[i0])
        D = dep_vectors(In, Out, u, w, p)
        perp = nullspace(D, 8, p)
        fp = face_ports[i0]
        for _ in range(1000):
            x = [0] * 8
            for bvec in perp:
                c = random.randrange(p)
                x = [(xi + c * bi) % p for xi, bi in zip(x, bvec)]
            if all(x[j] for j in fp):
                break
        else:
            print(f"  [{name}] FAIL: no admissible vector at dependent line")
            return False
        # face edges at i0 take their values from x; other nonzero entries go to private neighbour lines
        for j in range(8):
            if j in fp or not x[j]:
                continue
            nb = ('E', j)
            lines[nb] = next(extra_rows)
            if j < 4:   # in-edge at In[j], label IN_LABEL[j], from nb's out port of the same label
                oi = OUT_LABEL.index(IN_LABEL[j])
                edges.append((nb, oi, i0, j, (-x[j]) % p))
            else:
                ii = IN_LABEL.index(OUT_LABEL[j - 4])
                edges.append((i0, j - 4, nb, ii, x[j]))
        for (s, oi, d, ii) in face_edges:
            if s == i0:
                val[(s, oi, d, ii)] = x[4 + oi]
            elif d == i0:
                val[(s, oi, d, ii)] = (-x[ii]) % p
    for fe in face_edges:
        if fe not in val:
            val[fe] = rnd_nonzero(p)
        edges.append(fe + (val[fe],))
    # port vectors
    vec = {ln: [0] * 8 for ln in lines}
    for (s, oi, d, ii, c) in edges:
        vec[s][4 + oi] = c % p
        vec[d][ii] = (-c) % p
    f = {}
    for ln in lines:
        if any(vec[ln]):
            sol = realize(*positions(lines[ln]), u, w, vec[ln], p)
            if sol is None:
                print(f"  [{name}] FAIL: line {ln} not realizable (dep {deps.get(ln)})")
                return False
            f[ln] = sol
    # verification of every b-edge equation of the modelled copy
    ok = True
    incident = {ln: [None] * 8 for ln in lines}
    for (s, oi, d, ii, c) in edges:
        incident[s][4 + oi] = c % p
        incident[d][ii] = (-c) % p
    pure = 0
    escaped = 0
    for ln in lines:
        In, Out = positions(lines[ln])
        P = mul(f.get(ln, {}), u, p)
        Q = mul(f.get(ln, {}), w, p)
        for j in range(4):
            want = incident[ln][j] if incident[ln][j] is not None else 0
            ok &= P.get(In[j], 0) == want
            want = incident[ln][4 + j] if incident[ln][4 + j] is not None else 0
            ok &= Q.get(Out[j], 0) == want
        if ln in face_ports:
            ok &= all((P if j < 4 else Q).get((In + Out)[j], 0) != 0 for j in face_ports[ln])
        if f.get(ln):
            Dset = set(In) | set(Out)
            if set(P) <= Dset and set(Q) <= Dset:
                pure += 1
            escaped += len(set(P) - set(In)) + len(set(Q) - set(Out))
    nf = sum(1 for ln in lines if f.get(ln))
    print(f"  [{name}] p={p}: |supp u|={len(u)}, |supp w|={len(w)}, dependent lines={len(dependent)}, "
          f"active lines={nf} (face 42 + private {nf - 42}), edge eqs ok={ok}, pure={pure}, "
          f"escaped port points={escaped}")
    return ok and pure <= 1 and nf >= 42


def main():
    allok = True
    rows_of = list(range(1, 43))
    for p in (2, 3, 10007):
        print(f"field F_{p}")
        # (a) witness-support pair u = c0 + c1 t, w = c2 + c3 t with c0 c3 != c1 c2 (known regular)
        if p == 2:
            u, w = {0: 1}, {0: 1, 1: 1}
        else:
            u, w = {0: 1, 1: 2}, {0: 3, 1: 1}
        allok &= run_case("witness {1,a,b,ab}", u, w, p, rows_of)
        # (b) open-regime random pairs: >= 13 exponents, S - S meets Dist in >= 11 rows, span >= 10^51
        for k in range(3):
            pool = [0, 1, 7] + [10 ** (5 * r - 4) for r in range(1, 14)] + [10 ** (5 * r) for r in range(1, 14)]
            Su = random.sample(pool, 9)
            Sw = random.sample(pool, 8)
            u = {e: rnd_nonzero(p) for e in Su}
            w = {e: rnd_nonzero(p) for e in Sw}
            S = set(Su) | set(Sw)
            diffs = {x - y for x in S for y in S if x != y}
            hit = [r for r in range(1, 60) if diffs & {abs(a - b) for a in distinguished(r) for b in distinguished(r) if a != b}]
            print(f"    open pair {k}: |S| = {len(S)}, span = 10^{len(str(max(S) - min(S))) - 1}.., "
                  f"rows r with (S - S) meeting Dist_r: {len(hit)}")
            allok &= run_case(f"open random {k}", u, w, p, rows_of)
        # (c) adversarial: u/w = -B^v/A^v on a face line's own ports, so that line is dependent
        for which, idx in (("middle M_0", 1), ("long L_3", 6)):
            In, Out = positions(rows_of[idx])
            A = {-In[0]: 1, -In[1]: 2 % p or 1}            # A^v on -In
            B = {-Out[3]: 3 % p or 1, -Out[1]: 1}         # B^v on -Out
            u = {e: (-c) % p for e, c in B.items()}
            w = dict(A)
            allok &= run_case(f"dependent {which}", u, w, p, rows_of)
    print("ALL CHECKS PASS" if allok else "SOME CHECK FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
