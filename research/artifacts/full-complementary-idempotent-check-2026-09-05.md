---
kind: artifact
date: 2026-09-05
---

# Full complementary idempotents: statement, proof, and exact check

Research note received 2026-09-05 (forwarded by the author from an external
pass), re-derived by hand and checked by exact noncommutative computation in
this repository.  The theorem below is now printed in `non_mf_groups_exist.tex`
as `thm:full-defect-ring`, with `cor:simple-infinite-ring` and
`cor:one-sided-ring-maximal`.

## Statement

Let `R` be a countable unital associative ring with `s, t ∈ R` such that

```text
t s = 1,        R (1 - s t) R = R
```

(the second equation is an equality of two-sided ideals: there are finitely
many `a_j, b_j` with `Σ_j a_j (1 - st) b_j = 1`).  Then for every `n ≥ 4`,
every homomorphism from `EL_n(R)` to an MF group is trivial.  No finite
generation of `R` is assumed.

Consequences: every countable simple unital ring that is not directly finite;
every Leavitt algebra `L_k(1,m)`, `k` a countable field, `m ≥ 2`
(`t_2 (1 - s_1 t_1) s_2 = 1`); and, for `R` merely not directly finite,
`C*_max(EL_n(R))` contains a proper isometry for `n ≥ 4`.

## Proof

Write `e = 1 - st`; then `e² = e`, `es = te = 0`.  First let `R` be finitely
generated.  Put `G = EL_n(R)`, `L = EL_3(R)` on coordinates `1,2,3`; both have
property (T) by Ershov–Jaikin-Zapirain, Theorem 1.1 (literature input).

*Compressor.*  For `i = 1,2,3` let
`u_i = e_{4i}(t-1) e_{i4}(1) e_{4i}(s-1) e_{i4}(-t)`, whose `(i,4)` block is
`[[s, e],[0, t]]`.  Then `u = u_3 u_2 u_1 ∈ EL_4(R)` is

```text
u = [[s,0,0,e],[0,s,0,et],[0,0,s,et²],[0,0,0,t³]],
u⁻¹ = [[t,0,0,0],[0,t,0,0],[0,0,t,0],[e,se,s²e,s³]],
u · diag(A,1) · u⁻¹ = diag(e I₃ + s A t, 1),
```

so `u e_{ij}(a) u⁻¹ = e_{ij}(s a t)` and `u L u⁻¹ ≤ L`.  The compression is
strict when `e ≠ 0`, since `e (s a t) = 0` while `e · 1 = e`.

*Centralizer.*  `c = [e_{41}(e), e_{14}(t)] = diag(1,1,1,1+et)` (using
`te = 0`; `(et)² = 0`), which commutes with `L`.  Then

```text
u c u⁻¹ = e_{12}(e),        d = [u c u⁻¹, e_{23}(1)] = e_{13}(e),
```

so `d ∈ D_G(L)` in the notation of the manuscript (compressor `u`,
centralizer `c`, source element `e_{23}(1)`).

*Saturation.*  `[e_{41}(a), e_{13}(e)] = e_{43}(ae)` and
`[e_{43}(ae), e_{32}(b)] = e_{42}(aeb)`, so `e_{42}(1) = Π_j e_{42}(a_j e b_j)`
lies in the normal closure `N` of `d`; signed permutation matrices move it to
every root position and `[e_{ij}(1), e_{jk}(r)] = e_{ik}(r)` gives every
coefficient.  So `N = G = D_G(L)`, and the one-sided compression criterion
(`thm:compression-criterion`, `K = G`) makes every homomorphism to an MF group
trivial.

*General countable `R`.*  Each element of `EL_n(R)` lies in `EL_n(S)` for a
finitely generated unital subring `S ∋ s, t, a_j, b_j`; the identities hold in
`S`, so the restriction of any homomorphism to `EL_n(S)` is trivial.

## Exact check

The script below computes in the free `ℤ`-algebra on `s, t, a, b, a_{ij}`
modulo the single rewrite `ts → 1` (no overlapping left-hand sides, so normal
forms are unique), and in `L(1,2)` modulo `t_i s_j → δ_{ij}`.  Finite
matrices cannot model `ts = 1 ≠ st`, so the check is symbolic, not numeric.
It verifies the elementary factorization, both inverse products, the
compression for a generic `A`, the six roots, the centralizer word, its
transport, the defect, both propagation commutators, strictness, and the
Leavitt fullness identity.

Output:

```text
e idempotent, es = te = 0: ok
u = u3 u2 u1 equals the displayed matrix: ok
u u^-1 = u^-1 u = 1: ok
u diag(A,1) u^-1 = diag(e I + s A t, 1) for generic A: ok
u e_ij(a) u^-1 = e_ij(s a t) for the six roots of EL_3: ok
c = [e41(e), e14(t)] = diag(1,1,1,1+et): ok
c commutes with diag(A,1): ok
u c u^-1 = e12(e): ok
[u c u^-1, e23(1)] = e13(e): ok
[e41(a), e13(e)] = e43(a e): ok
[e43(a e), e32(b)] = e42(a e b): ok
e (s a t) = 0 and e != 0: compression of EL_3 is strict: ok
t2 (1 - s1 t1) s2 = 1 in L(1,2): ok
ALL CHECKS PASSED
```

Script (`python3`, standard library only):

```python
#!/usr/bin/env python3
"""Exact check of the full-complementary-idempotent argument.

Noncommutative polynomials with integer coefficients in the free algebra on
the listed generators, modulo the rewriting system given by RULES.  Words are
tuples of generator names; a polynomial is {word: int}.  The rewriting systems
used have no overlapping left-hand sides, so normal forms are unique.
"""
from itertools import product

class NC:
    def __init__(self, rules):
        self.rules = rules  # dict: tuple(word) -> polynomial (dict)
        self.maxlen = max((len(k) for k in rules), default=0)

    def reduce(self, poly):
        out = {}
        stack = list(poly.items())
        while stack:
            w, c = stack.pop()
            if c == 0:
                continue
            hit = None
            for i in range(len(w)):
                for L in range(1, self.maxlen + 1):
                    if w[i:i+L] in self.rules:
                        hit = (i, L); break
                if hit: break
            if hit is None:
                out[w] = out.get(w, 0) + c
                if out[w] == 0: del out[w]
            else:
                i, L = hit
                for rw, rc in self.rules[w[i:i+L]].items():
                    stack.append((w[:i] + rw + w[i+L:], c * rc))
        return out

    def const(self, k): return self.reduce({(): k})
    def gen(self, g): return self.reduce({(g,): 1})
    def add(self, p, q):
        r = dict(p)
        for w, c in q.items():
            r[w] = r.get(w, 0) + c
            if r[w] == 0: del r[w]
        return r
    def neg(self, p): return {w: -c for w, c in p.items()}
    def mul(self, p, q):
        r = {}
        for w1, c1 in p.items():
            for w2, c2 in q.items():
                r[w1 + w2] = r.get(w1 + w2, 0) + c1 * c2
        return self.reduce(r)

    # matrices: list of lists of polynomials
    def eye(self, n): return [[self.const(1 if i == j else 0) for j in range(n)] for i in range(n)]
    def mmul(self, A, B):
        n = len(A); m = len(B[0]); k = len(B)
        return [[self._sum(self.mul(A[i][l], B[l][j]) for l in range(k)) for j in range(m)] for i in range(n)]
    def _sum(self, it):
        r = {}
        for p in it: r = self.add(r, p)
        return r
    def meq(self, A, B): return all(A[i][j] == B[i][j] for i in range(len(A)) for j in range(len(A[0])))
    def elem(self, n, i, j, a):  # e_{ij}(a) = I + a E_{ij}, 1-based
        M = self.eye(n); M[i-1][j-1] = self.add(M[i-1][j-1], a); return M
    def elem_inv(self, n, i, j, a): return self.elem(n, i, j, self.neg(a))
    def comm(self, g, ginv, h, hinv): return self.mmul(self.mmul(self.mmul(g, h), ginv), hinv)

# ---------------------------------------------------------------- ring: ts = 1
gens = ['s', 't', 'a', 'b'] + [f'a{i}{j}' for i in range(1, 4) for j in range(1, 4)]
R = NC({('t', 's'): {(): 1}})
s, t, a, b = (R.gen(g) for g in ['s', 't', 'a', 'b'])
one = R.const(1)
e = R.add(one, R.neg(R.mul(s, t)))          # e = 1 - st
assert R.mul(e, e) == e and R.mul(e, s) == {} and R.mul(t, e) == {}
print("e idempotent, es = te = 0: ok")

n = 4
def u_i(i):
    m = R.mmul(R.elem(n, 4, i, R.add(t, R.neg(one))), R.elem(n, i, 4, one))
    m = R.mmul(m, R.elem(n, 4, i, R.add(s, R.neg(one))))
    return R.mmul(m, R.elem(n, i, 4, R.neg(t)))
u = R.mmul(R.mmul(u_i(3), u_i(2)), u_i(1))
zero = {}
U = [[s, zero, zero, e],
     [zero, s, zero, R.mul(e, t)],
     [zero, zero, s, R.mul(R.mul(e, t), t)],
     [zero, zero, zero, R.mul(R.mul(t, t), t)]]
assert R.meq(u, U); print("u = u3 u2 u1 equals the displayed matrix: ok")
Uinv = [[t, zero, zero, zero],
        [zero, t, zero, zero],
        [zero, zero, t, zero],
        [e, R.mul(s, e), R.mul(R.mul(s, s), e), R.mul(R.mul(s, s), s)]]
assert R.meq(R.mmul(U, Uinv), R.eye(n)) and R.meq(R.mmul(Uinv, U), R.eye(n))
print("u u^-1 = u^-1 u = 1: ok")

# compression of a generic A in coordinates 1..3
A = [[R.gen(f'a{i}{j}') for j in range(1, 4)] for i in range(1, 4)]
D = R.eye(n)
for i in range(3):
    for j in range(3): D[i][j] = A[i][j]
lhs = R.mmul(R.mmul(U, D), Uinv)
rhs = R.eye(n)
for i in range(3):
    for j in range(3):
        rhs[i][j] = R.add(e if i == j else zero, R.mul(R.mul(s, A[i][j]), t))
assert R.meq(lhs, rhs); print("u diag(A,1) u^-1 = diag(e I + s A t, 1) for generic A: ok")
for i, j in [(i, j) for i in range(1, 4) for j in range(1, 4) if i != j]:
    l = R.mmul(R.mmul(U, R.elem(n, i, j, a)), Uinv)
    assert R.meq(l, R.elem(n, i, j, R.mul(R.mul(s, a), t)))
print("u e_ij(a) u^-1 = e_ij(s a t) for the six roots of EL_3: ok")

# centralizer element
c = R.comm(R.elem(n, 4, 1, e), R.elem_inv(n, 4, 1, e), R.elem(n, 1, 4, t), R.elem_inv(n, 1, 4, t))
C = R.eye(n); C[3][3] = R.add(one, R.mul(e, t))
assert R.meq(c, C); print("c = [e41(e), e14(t)] = diag(1,1,1,1+et): ok")
Cinv = R.eye(n); Cinv[3][3] = R.add(one, R.neg(R.mul(e, t)))
assert R.meq(R.mmul(C, Cinv), R.eye(n)) and R.meq(R.mmul(Cinv, C), R.eye(n))
assert R.meq(R.mmul(C, D), R.mmul(D, C)); print("c commutes with diag(A,1): ok")
ucu = R.mmul(R.mmul(U, C), Uinv)
assert R.meq(ucu, R.elem(n, 1, 2, e)); print("u c u^-1 = e12(e): ok")
d = R.comm(R.elem(n, 1, 2, e), R.elem_inv(n, 1, 2, e), R.elem(n, 2, 3, one), R.elem_inv(n, 2, 3, one))
assert R.meq(d, R.elem(n, 1, 3, e)); print("[u c u^-1, e23(1)] = e13(e): ok")

# propagation through the ideal
x = R.comm(R.elem(n, 4, 1, a), R.elem_inv(n, 4, 1, a), R.elem(n, 1, 3, e), R.elem_inv(n, 1, 3, e))
assert R.meq(x, R.elem(n, 4, 3, R.mul(a, e))); print("[e41(a), e13(e)] = e43(a e): ok")
y = R.comm(R.elem(n, 4, 3, R.mul(a, e)), R.elem_inv(n, 4, 3, R.mul(a, e)), R.elem(n, 3, 2, b), R.elem_inv(n, 3, 2, b))
assert R.meq(y, R.elem(n, 4, 2, R.mul(R.mul(a, e), b))); print("[e43(a e), e32(b)] = e42(a e b): ok")

# strictness: e * (s a t) = 0 while e * 1 = e != 0
assert R.mul(e, R.mul(R.mul(s, a), t)) == {} and e != {}
print("e (s a t) = 0 and e != 0: compression of EL_3 is strict: ok")

# ---------------------------------------------------------------- Leavitt L(1,2)
L = NC({('t1', 's1'): {(): 1}, ('t2', 's2'): {(): 1}, ('t1', 's2'): {}, ('t2', 's1'): {}})
s1, s2, t1, t2 = (L.gen(g) for g in ['s1', 's2', 't1', 't2'])
eL = L.add(L.const(1), L.neg(L.mul(s1, t1)))
assert L.mul(L.mul(t2, eL), s2) == L.const(1); print("t2 (1 - s1 t1) s2 = 1 in L(1,2): ok")
print("ALL CHECKS PASSED")
```

## Relation to what the graph already had

* `generic-leavitt-self-compression-full-mf-radical` needs a full binary
  Leavitt family `s_0,s_1,t_0,t_1`, rank `n ≥ 16`, and property (T) of
  `E_4(R)` and `E_n(R)` as hypotheses.  The theorem above needs one one-sided
  inverse whose complementary idempotent is full, rank `n ≥ 4`, and derives
  (T) from EJZ on finitely generated subrings.
* `RankFourCompressors.lean` already defines `compressor = U₃U₂U₁` with the
  same twelve-transvection word over a `LeavittFamily` (`p1` in the role of
  `e`); its matrix value is `compressor_val`.  The centralizer word
  `[e_{41}(e), e_{14}(t)]` and the full-idempotent criterion are new.
* `full-leavitt-idempotent-defect-saturation` is the same two-commutator
  propagation in rank 20 with `q = s_1 t_1`.

Not verified here: worldwide novelty of the criterion; a Lean carrier for
the centralizer identity and the theorem (none exists as of this note).
