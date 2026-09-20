#!/usr/bin/env python3
"""Exact torsion of coker(A) over the Laurent ring L = F_p[t, t^-1].

A is a sparse matrix given as a list of rows; each row is a dict
col -> flint.nmod_poly (entries are Laurent polynomials, stored as
polynomials; a row may be multiplied by any power of t, a unit of L).

coker(A) = L^ncols / (row space).  The routine performs only invertible
row operations, invertible column operations, and deletion of a row and a
column meeting in a unit pivot whose row and column are otherwise zero.
Each of these preserves coker(A) up to isomorphism.  It returns the list of
non-unit diagonal entries d_i (each normalised to be monic with nonzero
constant term) and the free rank, so that

    coker(A) = L^free  (+)  (+)_i L/(d_i).

Used for H_2 of periodic Rips complexes: with A = boundary d_3 (rows =
orbits of 4-cliques, cols = orbits of 3-cliques), the torsion submodule of
coker(d_3) equals the torsion submodule of H_2 (C_2/Z_2 = B_1 is free over
the PID L, so C_2/B_2 = H_2 (+) B_1).
"""
import flint

P = 2147483629


def val(f):
    """t-adic valuation of a nonzero nmod_poly."""
    c = f.coeffs()
    for i, x in enumerate(c):
        if int(x):
            return i
    raise ValueError("zero")


def strip(f):
    v = val(f)
    return f.right_shift(v) if v else f


def is_unit(f):
    """Nonzero monomial c t^e (a unit of L)."""
    c = f.coeffs()
    return sum(1 for x in c if int(x)) == 1


def ldeg(f):
    """Degree in L: deg(f) - val(f)."""
    return f.degree() - val(f)


def strip_row(row):
    if not row:
        return row
    v = min(val(f) for f in row.values())
    if v:
        return {c: f.right_shift(v) for c, f in row.items()}
    return row


def monic(f, p):
    lc = int(f.coeffs()[-1])
    return f * pow(lc, p - 2, p)


class Mat:
    def __init__(self, rows, ncols, p=P):
        self.p = p
        self.ncols = ncols
        self.rows = {}
        self.colidx = {c: set() for c in range(ncols)}
        for rid, row in enumerate(rows):
            row = {c: f for c, f in row.items() if not f.is_zero()}
            if row:
                row = strip_row(row)
                self.rows[rid] = row
                for c in row:
                    self.colidx[c].add(rid)
        self.pivots = 0
        self.invariants = []

    def _set_row(self, j, new):
        old = self.rows.get(j, {})
        for c in old:
            if c not in new:
                self.colidx[c].discard(j)
        for c in new:
            self.colidx[c].add(j)
        if new:
            self.rows[j] = new
        else:
            self.rows.pop(j, None)

    def _delete(self, i, c):
        for k in self.rows[i]:
            self.colidx[k].discard(i)
        del self.rows[i]
        del self.colidx[c]
        self.pivots += 1

    def _combine(self, j, sj, i, coef):
        """row_j <- t^sj * row_j - coef * row_i  (coef an nmod_poly)."""
        rj = self.rows[j]
        ri = self.rows[i]
        new = {}
        for c, f in rj.items():
            new[c] = f.left_shift(sj) if sj else f
        for c, f in ri.items():
            g = new.get(c)
            h = coef * f
            g = -h if g is None else g - h
            if g.is_zero():
                new.pop(c, None)
            else:
                new[c] = g
        self._set_row(j, strip_row(new))

    def unit_stage(self):
        p = self.p
        while True:
            progress = False
            for c in sorted(self.colidx, key=lambda c: len(self.colidx[c])):
                if c not in self.colidx:
                    continue
                best = None
                for r in self.colidx[c]:
                    f = self.rows[r][c]
                    if is_unit(f):
                        cost = len(self.rows[r])
                        if best is None or cost < best[0]:
                            best = (cost, r)
                if best is None:
                    continue
                i = best[1]
                u = self.rows[i][c]
                e = val(u)
                inv = pow(int(u.coeffs()[e]), p - 2, p)
                for j in list(self.colidx[c]):
                    if j == i:
                        continue
                    a = self.rows[j][c]
                    self._combine(j, e, i, a * inv)
                self._delete(i, c)
                progress = True
            if not progress:
                break

    def euclid_stage(self):
        p = self.p
        while self.rows:
            # entry of least L-degree
            best = None
            for i, row in self.rows.items():
                for c, f in row.items():
                    d = ldeg(f)
                    if best is None or d < best[0]:
                        best = (d, i, c)
                        if d == 0:
                            break
                if best[0] == 0:
                    break
            _, i, c = best
            a = self.rows[i][c]
            alpha = val(a)
            a0 = a.right_shift(alpha) if alpha else a
            dirty = False
            # clear column c by row operations
            for j in list(self.colidx[c]):
                if j == i:
                    continue
                b = self.rows[j][c]
                beta = val(b)
                b0 = b.right_shift(beta) if beta else b
                q, rem = divmod(b0, a0)
                # t^alpha row_j - t^beta q row_i ; entry becomes t^(a+b) rem
                self._combine(j, alpha, i, q.left_shift(beta) if beta else q)
                if not rem.is_zero():
                    dirty = True
            if dirty:
                continue
            # clear row i by column operations (only row i changes)
            ri = dict(self.rows[i])
            for k, b in list(ri.items()):
                if k == c:
                    continue
                beta = val(b)
                b0 = b.right_shift(beta) if beta else b
                q, rem = divmod(b0, a0)
                if rem.is_zero():
                    del ri[k]
                else:
                    ri[k] = rem.left_shift(beta) if beta else rem
                    dirty = True
            self._set_row(i, ri)
            if dirty:
                continue
            if ldeg(a0) > 0:
                self.invariants.append(monic(a0, p))
            self._delete(i, c)

    def run(self):
        self.unit_stage()
        residual = (len(self.rows), sum(len(r) for r in self.rows.values()))
        self.euclid_stage()
        free = self.ncols - self.pivots
        return free, self.invariants, residual


def torsion_of_coker(rows, ncols, p=P):
    m = Mat(rows, ncols, p)
    return m.run()


def factor_invariants(invs):
    """Distinct irreducible factors (as coefficient lists) with multiplicity."""
    out = {}
    for f in invs:
        _, facs = f.factor()
        for g, e in facs:
            key = tuple(int(x) for x in g.coeffs())
            out[key] = out.get(key, 0) + e
    return out
