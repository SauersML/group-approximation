---
rg: 2
id: regular-finite-table-quantum-classical-hamming-gap
kind: claim
title: A regular-character finite table has a unitary limit but a positive permutation gap
distinct_from:
  finite-table-quantum-classical-hamming-gap: that literal multiplication-only formulation is refuted by the constant identity model; this node explicitly includes identity and pair-separation errors.
  hyperlinear-nonsofic-group: that is the global group-existence statement; this is one finite local obstruction and by itself constructs no group.
  coherent-groupification-of-table-gap: that asks to realize a local obstruction coherently inside one hyperlinear group; this asks only for the obstruction.
  known-game-gaps-miss-finite-group-table-quantifiers: that audits known game sources; this is the unrestricted existence question left after the audit.
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

There are a finite set `F` with `|F| >= 2`, a distinguished label `e in F`,
a set of tested products `P subseteq F x F x F`, and `c > 0` with the
following property.

For `d >= 1`, write `d_2(A,B)^2 = tr_d((A-B)^*(A-B))`, and for an assignment
`U:F -> U(d)` put

```text
D_U(U) = max {
  max_(g,h,k in P) d_2(U_g U_h,U_k),
  d_2(U_e,I_d),
  max_(g != h in F) |tr_d(U_g^* U_h)|
}.
```

For a nonempty finite set `X`, normalized Hamming distance `d_H`, and
`sigma:F -> Sym(X)`, put

```text
D_perm(sigma) = max {
  max_(g,h,k in P) d_H(sigma_g sigma_h,sigma_k),
  d_H(sigma_e,id_X),
  max_(g != h in F) (1-d_H(sigma_g,sigma_h))
}.
```

Then

```text
inf_(d >= 1, U:F -> U(d)) D_U(U) = 0,
inf_(nonempty finite X, sigma:F -> Sym(X)) D_perm(sigma) >= c.   (RFT1)
```

The last term in each defect is the regular-character separation condition:
`tr_d(U_g^*U_h)` and the fixed-point fraction
`1-d_H(sigma_g,sigma_h)` must vanish for distinct labels. It rules out the
constant identity assignments that refute the unseparated formulation.

Any hyperlinear nonsofic group would supply a finite local obstruction of this
form. The converse requires a coherence step: one must realize compatible
local obstructions inside a single hyperlinear group. That remaining step is
`coherent-groupification-of-table-gap`.

## Attempts

- Known exact finite-dimensional quantum/classical gaps do not give `(RFT1)`:
  `exact-finite-dimensional-group-table-classicalizes` produces an exact
  separated permutation table whenever the unitary infimum is attained.
- Known nonlocal-game and nonclosed-game sources miss one of the two sides;
  see `known-game-gaps-miss-finite-group-table-quantifiers`.
- A numerical search must certify the infimum over unbounded matrix dimension,
  not merely a fixed relaxation level. A convergent hierarchy or an explicit
  defect-to-zero sequence is required on the unitary side.
