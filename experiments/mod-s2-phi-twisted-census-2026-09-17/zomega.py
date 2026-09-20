#!/usr/bin/env python3
"""H_1(M_Phi; Z[omega, 1/3]_chi) for chi : M_Phi -> Phi/L = Z/3 -> <omega>.

From the R-chains of twisted.py, put t = omega (Z[omega] = Z[t]/(t^2+t+1),
elements a + b omega stored as pairs).  Q_omega = Z[omega]^{ngen}/rows is
H_1(M_Phi; Z[omega]_chi) + Z[omega] (twisted.py).  We eliminate over the
ring A = Z[omega, 1/3], a PID whose units are the u with N(u) a power of 3
(N(a + b omega) = a^2 - a b + b^2; 3 = -omega^2 (1 - omega)^2 ramifies):

  phase 1: pivots that are units of Z[omega] (N = 1), q <- q - q_j u^-1 p,
           exact over Z[omega], Markowitz order as in fastelim.py;
  phase 2: pivots u with N(u) = 3^k, q <- N(u) q - q_j conj(u) p (N(u) is a
           unit of A, so the A-span is unchanged), then the row is divided by
           (1 - omega) as long as it stays integral (again a unit of A).

Each step is an A-isomorphism of Q_omega (x) A that deletes one generator.
If at the end exactly one generator survives and no relation row does, then
Q_omega (x) A = A, i.e.

    H_1(M_Phi; Z[omega]_chi) (x) Z[1/3] = 0,

so H_1(M_Phi; Q(omega)_chi) = 0 and H_1(M_Phi; Z[omega]_chi) is a finite
3-group.  Usage: python3 zomega.py <L index | z | max<k>> [out.json]
(max<k>: base U, L = max_k, a test: rank H_1(M_U; Q(omega)_chi) =
(b_1(M_max_k) - 16)/2.)
"""
import heapq
import json
import sys
import time

import twisted as T


def mul(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def conj(x):
    a, b = x
    return (a - b, -b)


def norm(x):
    a, b = x
    return a * a - a * b + b * b


def sub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def is_three_power(n):
    while n % 3 == 0 and n > 1:
        n //= 3
    return n == 1


def div_one_minus_omega(x):
    """x / (1 - omega) if integral, else None; 1/(1-omega) = (2+omega)/3."""
    y = mul(x, (2, 1))
    if y[0] % 3 or y[1] % 3:
        return None
    return (y[0] // 3, y[1] // 3)


def to_omega(v):
    out = {}
    for g, a in v.items():
        e = (a[0] - a[2], a[1] - a[2])
        if e != (0, 0):
            out[g] = e
    return out


def phase1(ngen, rows, log):
    colrows = {}
    for r, v in rows.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    alive = set(range(ngen))
    heap = []

    def push(r):
        v = rows[r]
        best = None
        for g, a in v.items():
            if norm(a) == 1:
                c = len(colrows[g])
                if best is None or c < best[0]:
                    best = (c, g)
        if best is not None:
            heapq.heappush(heap, ((len(v) - 1) * (best[0] - 1), r, best[1]))

    for r in rows:
        push(r)
    steps, t0 = 0, time.time()
    while heap:
        cost, r, j = heapq.heappop(heap)
        v = rows.get(r)
        if v is None or j not in v or norm(v[j]) != 1:
            if v is not None:
                push(r)
            continue
        true = (len(v) - 1) * (len(colrows[j]) - 1)
        if true > cost:
            heapq.heappush(heap, (true, r, j))
            continue
        uinv = conj(v[j])
        piv = v
        del rows[r]
        for g in piv:
            colrows[g].discard(r)
        for q in list(colrows.get(j, ())):
            row = rows[q]
            f = mul(row[j], uinv)
            for g, b in piv.items():
                nv = sub(row.get(g, (0, 0)), mul(f, b))
                if nv != (0, 0):
                    if g not in row:
                        colrows.setdefault(g, set()).add(q)
                    row[g] = nv
                elif g in row:
                    del row[g]
                    colrows[g].discard(q)
            assert j not in row
            if not row:
                del rows[q]
            else:
                push(q)
        alive.discard(j)
        colrows.pop(j, None)
        steps += 1
        if steps % 5000 == 0:
            log(f"  phase1: {steps} pivots, {len(alive)} gens, {len(rows)} "
                f"rows, cost {cost} [{time.time()-t0:.0f}s]")
    return alive, rows


def phase2(alive, rows, log):
    """Dense-ish elimination over A = Z[omega, 1/3] on what is left."""
    rows = [dict(v) for v in rows.values() if v]
    alive = set(alive)
    maxbits = 0
    while True:
        best = None
        for i, v in enumerate(rows):
            for g, a in v.items():
                n = norm(a)
                if is_three_power(n):
                    key = (n, len(v))
                    if best is None or key < best[0]:
                        best = (key, i, g)
        if best is None:
            break
        _, i, j = best
        piv = rows.pop(i)
        u = piv[j]
        N, cu = norm(u), conj(u)
        new = []
        for v in rows:
            if j in v:
                f = mul(v[j], cu)
                w = {}
                for g in set(v) | set(piv):
                    x = sub(mul((N, 0), v.get(g, (0, 0))),
                            mul(f, piv.get(g, (0, 0))))
                    if x != (0, 0):
                        w[g] = x
                assert j not in w
                while w:
                    d = {g: div_one_minus_omega(x) for g, x in w.items()}
                    if any(x is None for x in d.values()):
                        break
                    w = d
                v = w
            if v:
                new.append(v)
                for x in v.values():
                    maxbits = max(maxbits, abs(x[0]).bit_length(),
                                  abs(x[1]).bit_length())
        rows = new
        alive.discard(j)
    log(f"phase2 done: {len(alive)} gens, {len(rows)} rows, max entry bits "
        f"{maxbits}")
    return alive, rows


def phase3(alive, rows, log):
    """Exact structure of what is left, as an abelian group: restriction of
    scalars Z[omega] -> Z^2 (x = a + b omega on the basis 1, omega; a row r
    gives the integer rows r and omega r), Smith form with flint.  Returns
    (Z-rank, prime-to-3 invariants, 3-power invariants).  Z-rank = 2 *
    (Z[omega]-rank); the extra Z[omega] summand of twisted.py contributes 2."""
    from flint import fmpz_mat
    cols = sorted(alive)
    ci = {g: 2 * i for i, g in enumerate(cols)}
    n = 2 * len(cols)
    seen, R = set(), []
    for v in rows:
        for m in ((1, 0), (0, 1)):
            z = [0] * n
            for g, x in v.items():
                y = mul(m, x)
                z[ci[g]], z[ci[g] + 1] = y
            t = tuple(z)
            if any(t) and t not in seen:
                seen.add(t)
                R.append(z)
    log(f"phase3: {len(R)} integer rows on {n} columns")
    if not R:
        return n, [], []
    H = fmpz_mat(R).hnf()
    Hr = [[int(H[i, j]) for j in range(n)] for i in range(H.nrows())]
    Hr = [r for r in Hr if any(r)]
    if not Hr:
        return n, [], []
    D = fmpz_mat(Hr).snf()
    diag = [abs(int(D[i, i])) for i in range(min(D.nrows(), D.ncols()))]
    nz = [d for d in diag if d]
    rank = n - len(nz)
    p3, other = [], []
    for d in nz:
        e = 1
        while d % 3 == 0:
            d //= 3
            e *= 3
        if e > 1:
            p3.append(e)
        if d > 1:
            other.append(d)
    return rank, other, p3


def main(which, outp=None, base="phi"):
    t0 = time.time()
    ngen, R, Z, zinfo, info = T.build(which, base=base)
    rows = {}
    for r, v in enumerate(R):
        w = to_omega(v)
        if w:
            rows[r] = w
    del R, Z
    T.log(f"{len(rows)} nonzero Z[omega]-rows on {ngen} gens")
    alive, rows = phase1(ngen, rows, T.log)
    T.log(f"phase1 done: {len(alive)} gens, {len(rows)} rows "
          f"[{time.time()-t0:.0f}s]")
    alive, left = phase2(alive, rows, T.log)
    zr, other, p3 = phase3(alive, left, T.log)
    out = dict(info)
    out.update({"Q_omega_Z_rank": zr, "Q_omega_prime_to_3_torsion": other,
                "Q_omega_3_torsion_after_phase2": p3,
                "H1_twisted_Q_omega_rank": (zr - 2) // 2,
                "H1_twisted_Z13_vanishes": zr == 2 and not other,
                "gens_left": len(alive), "rows_left": len(left),
                "seconds": round(time.time() - t0)})
    if left:
        out["left_rows"] = [{str(g): list(x) for g, x in v.items()}
                            for v in left[:50]]
    print(json.dumps({k: v for k, v in out.items() if k != "left_rows"}),
          flush=True)
    if outp:
        json.dump(out, open(outp, "w"), indent=1)


if __name__ == "__main__":
    a = sys.argv[1:]
    base = "U" if a[0].startswith("max") else "phi"
    main(a[0], a[1] if len(a) > 1 and a[1] != "-" else None, base)
