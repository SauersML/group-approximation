# Integer lattice helpers: Hermite normal form of a row span, membership, Smith invariants.
from sympy import Matrix
from sympy.matrices.normalforms import smith_normal_form

def hnf(rows, n):
    """Echelon integer basis of the Z-span of rows (list of length-n int lists)."""
    rows = [list(r) for r in rows if any(r)]
    out = []
    for col in range(n):
        piv = [r for r in rows if r[col]]
        rest = [r for r in rows if not r[col]]
        while len(piv) > 1:
            piv.sort(key=lambda r: abs(r[col]))
            p = piv[0]; nxt = [p]
            for r in piv[1:]:
                q = r[col] // p[col]
                r2 = [a - q * b for a, b in zip(r, p)]
                if r2[col]: nxt.append(r2)
                elif any(r2): rest.append(r2)
            piv = nxt
        if piv:
            p = piv[0]
            if p[col] < 0: p = [-a for a in p]
            out.append(p)
        rows = rest
    for i, p in enumerate(out):
        c = next(j for j in range(n) if p[j])
        for k in range(i):
            q = out[k][c] // p[c]
            if q: out[k] = [a - q * b for a, b in zip(out[k], p)]
    return out

def member(basis, v, n):
    v = list(v)
    for p in basis:
        c = next(j for j in range(n) if p[j])
        if v[c] % p[c]: return False
        q = v[c] // p[c]
        v = [a - q * b for a, b in zip(v, p)]
    return not any(v)

def invariant_span(vecs, maps, n, maxit=200):
    """Smallest lattice containing vecs and stable under each linear map in maps."""
    B = hnf(vecs, n)
    for _ in range(maxit):
        new = [m(b) for b in B for m in maps]
        new = [v for v in new if not member(B, v, n)]
        if not new: return B
        B = hnf(B + new, n)
    raise RuntimeError('no stabilisation')

def smith(basis, n):
    if not basis: return [0] * n
    M = Matrix(basis)
    D = smith_normal_form(M)
    d = [abs(D[i, i]) for i in range(min(D.shape))]
    d = [x for x in d if x != 0]
    return d + [0] * (n - len(d))   # quotient Z^n/span = sum Z/d_i (+ Z for each 0)
