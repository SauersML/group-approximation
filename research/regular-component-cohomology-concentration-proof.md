---
rg: 2
id: regular-component-cohomology-concentration-proof
kind: route
title: Project normalized curvature onto the regular Hilbert component and kill its cocycle
target: two-kazhdan-correction-concentrates-normalized-hs-curvature
requires: []
artifacts:
  - research/artifacts/parallel-arithmetic-holonomy-2026-09-04.md
---

The target is conditional on actual degree-two Hilbert cohomology
vanishing. The following proves that conditional implication; no lattice
vanishing theorem is an implicit input.

Fix a free ultrafilter. Let `H_all` be the Hilbert ultraproduct of the
normalized matrix 2-spaces. Let `H_reg` be the closed subspace generated
by sequences bounded in operator norm, and let `P_reg` be its orthogonal
projection. Fixed word representatives `q_g` give unitaries
`u_j(g)=U_j(q_g)`, with fixed-pair multiplicative error `O(delta_j)`.
Each `Ad(u_j(g))` preserves `H_reg` and its complement. It defines a
genuine group action on `H_reg`: on operator-bounded vectors, conjugation
by a unitary `D_j` with `||D_j-I||_2->0` differs from the identity by at
most `2||X_j||_op||D_j-I||_2`. Density proves the group law there.

Set

```text
D_j(g,h)=u_j(g)u_j(h)u_j(gh)^*,
c(g,h)=[(D_j(g,h)-I)/delta_j] in H_all.
```

These classes are bounded by the fixed van Kampen areas. For
operator-bounded `A_j,B_j` with 2-norm `O(delta_j)`, their product divided
by delta is bounded in 2-norm and orthogonal to `H_reg`, since

```text
|tr(Y_j^* A_j B_j)|/delta_j
 <= ||Y_j||_op ||A_j||_2 ||B_j||_2/delta_j -> 0
```

for every operator-bounded `Y_j`. Apply this to the quadratic terms in
the exact identities

```text
(D-I)+(D-I)^*=-(D-I)^*(D-I),
D(g,h)D(gh,k)=Ad(u(g))(D(h,k))D(g,hk).
```

It follows that `c_reg=P_reg c` is a skew-Hermitian 2-cocycle for the
genuine action on `H_reg`. The target's hypothesis supplies a regular
skew-Hermitian cochain `b` with
`c_reg(g,h)=b(g)+g.b(h)-b(gh)`. Real skew-Hermitian coefficients are
permitted by complexification followed by the equivariant real projection.
Choose representatives `b_j(g)` approximable in 2-norm by operator-bounded
sequences and set

```text
v_j(g)=exp(-delta_j b_j(g))u_j(g).
```

Two elementary regularity estimates justify the first-order expansion.
If `X_j` is so approximable and `B_j` is operator-bounded with 2-norm
tending to zero, then `||X_jB_j||_2+||B_jX_j||_2->0`, by approximation
and `||Y_jB_j||_2<=||Y_j||_op||B_j||_2`. For regular skew-Hermitian
`b_j`, splitting its spectral measure at a fixed cutoff proves
`||exp(delta_j b_j)-I-delta_j b_j||_2=o(delta_j)`.
Thus

```text
[(v_j(g)v_j(h)v_j(gh)^*-I)/delta_j]=c(g,h)-db(g,h),
P_reg [(v_j(g)v_j(h)v_j(gh)^*-I)/delta_j]=0.
```

This calculation does not assume the original `c_j` is regular. Every
cross term involving it has the regular exponential difference as its
other factor, so the preceding product estimate applies.

A 2-norm-bounded class `[X_j]` is orthogonal to `H_reg` exactly when
`lim_omega||X_j||_1=0`. One implication uses
`|tr(Y^*X)|<=||Y||_op||X||_1` and density; the converse tests against the
operator-bounded polar partial isometries of `X_j`. Consequently the
corrected maps have fixed-pair trace-norm error `o(delta_j)`.

For a generator symbol `s`, use `V_j(s)=v_j(bar(s))`, where `bar(s)`
is its image in `G`. The fixed null word `q_(bar(s))s^(-1)` bounds
`||u_j(bar(s))-U_j(s)||_2` by a fixed multiple of delta; this avoids
assuming different generator symbols have distinct images in `G`.
The exponential estimate then gives generator correction `O(delta_j)`.
Telescoping the finitely many defining relators gives trace-norm defect
`o(delta_j)`, and the original HS defect plus generator correction gives
HS defect `O(delta_j)`. A subsequence converts the finitely many
ultrafilter estimates into the target's ordinary limits.

For the small-support conclusion, set `E_(j,r)=V_j(r)-I` and
`a_j=max_r||E_(j,r)||_1/delta_j->0`. Choose `t_j>0` tending to zero
with `a_j/t_j->0`, and put

```text
P_j=join_r 1_(|E_(j,r)|>t_j delta_j),   Q_j=I-P_j.
```

Markov's inequality gives `tr(P_j)<=|R|a_j/t_j->0`. Since `Q_j` is
below every low spectral projection, and `E_(j,r)` is normal, both
`||E_(j,r)Q_j||_op` and `||Q_jE_(j,r)||_op` are at most `t_j delta_j`.
This proves `(KCC3)` without any invariance assertion.

Finally, under the target's optional square-tail condition, every
`c_j(g,h)` is regular: its fixed van Kampen expansion is a finite sum
of unitary translates of rescaled defining defects. Then `c=c_reg`, so
the same correction has residual `o(delta_j)` in 2-norm itself. The
artifact supplies the detailed spectral-tail estimates, a rank-one
counterexample to the unrestricted full-Hilbert-ultraproduct argument,
and the exact limitation on iteration.
