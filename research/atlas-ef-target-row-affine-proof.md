---
rg: 2
id: atlas-ef-target-row-affine-proof
kind: route
title: Use pe=e and qf=f to compute the first coefficient-moving target action
target: atlas-ef-target-rows-shrink-but-do-not-remove-degenerate-face
requires:
  - atlas-target-gl3-preserves-the-fifteen-type-degeneracy
  - atlas-steinberg-rank-five-translation
  - atlas-steinberg-spare-index-independence
---

The rows in `(EFR3)` are the Steinberg identities

```text
[x_1r(a),x_rs(b)]=x_1s(ab)                             (EFP1)
```

for `(a,b)=(p,e),(q,e),(p,f),(q,f)`.  The length-two roots are unambiguous
by spare-index independence.  Substituting `(EFR2)` into `(EFP1)` and using
involutivity gives the four conjugation formulas.

On a joint character vector, multiplying `D_(r,p)` by a negative
`D_(s,e)` toggles the `r`th `p` bit `u_r`.  The same actor multiplies the
coefficient-one root because `1e=e`, so it also toggles `w_r`; it leaves the
`q` sign fixed because `qe=0`.  This is the first map in `(EFR5)`.  The
second is symmetric using `pf=0`, `qf=f`, and `1f=f`.

For `alpha=beta=1`, the translation subgroup at coordinate `r` contains

```text
(u,w) |-> (u+e_r,w+e_r),
(u,w) |-> (u,w+e_r),
(u,w) |-> (u+e_r,w).                                  (EFP2)
```

Starting at `(0,0)`, the last point is nondegenerate.  Starting at a
type-`B` point `(0,w!=0)`, the first translation is nondegenerate unless
`w=e_r`, in which case `(u,w)=(e_r,0)` is already nondegenerate.  The same
argument with the second translation handles every type-`C` point.  This
proves the mixing assertions.

If the six `e/f` signs are positive, every control bit in `(EFR5)` vanishes,
so the fixed-face assertion is immediate.  For the trace count, the
coefficients `p,q` lie in degree zero and are independent orthogonal
idempotents, whereas `e,f` are independent degree-one monomials.  Hence
`{p,q,e,f}` is linearly independent over `F_2`.  At each target root this
gives `C_2^4`, and the three distinct matrix entries give their direct
product `C_2^12`.  Canonical trace restricts to the regular character of this
finite subgroup.  Six prescribed positive `e/f` signs therefore cost
`2^-6`, independently of the six `p/q` signs.  Multiplication by the
previous `15/64` degeneracy fraction and then by the marked half gives
`(EFR7)--(EFR8)`.

The orbit representation on the fixed face proves only a local no-go for
the coefficient-one and `e/f` target rows.  Relations involving `E,F` are
not included and may couple the survivor to longer coefficient words.
