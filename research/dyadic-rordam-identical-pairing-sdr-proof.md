---
rg: 2
id: dyadic-rordam-identical-pairing-sdr-proof
kind: route
title: Follow one branch history across infinitely many seeds and count its common coordinates
target: dyadic-rordam-identical-pairing-destroys-sdr
requires: []
artifacts:
  - research/artifacts/stw99-lxvi-dyadic-rordam-v4-audit-2026-08-30.md
---

Fix branches `gamma_1,...,gamma_r` before the paired step.  We first prove
by induction on `s <= r` that there are a finite exceptional set `F_s`, a
finite common set `C_s`, and an injection `rho_s` on the remaining seed
coordinates such that

`alpha_gamma_s ... alpha_gamma_1({a_i}) = C_s union {rho_s(a_i)}`

for `i notin F_s`, with `rho_s(a_i)` pairwise distinct and outside
`C_s`.  At `s=0`, take `C_0=empty` and `rho_0(a_i)=a_i`.  For the
induction step, enlarge `F_s` by the finitely many indices for which
`rho_s(a_i)` belongs to the finite evaluation set `E_gamma_(s+1)`.  Then
injectivity gives pairwise distinct surviving coordinates
`rho_(s+1)(a_i)=nu_gamma_(s+1)(rho_s(a_i))`, and

`C_(s+1) = nu_gamma_(s+1)(C_s minus E_gamma_(s+1)) union I_gamma_(s+1)`

is finite and independent of `i`.  Injectivity, together with the fresh
range/tensor-coordinate convention, keeps the distinguished coordinates
outside the common set.  This proves the induction.

Now choose one of the identical branch pairs `(beta,beta)` at the paired
step.  Discard the finitely many further indices whose distinguished
coordinate lies in `E_beta`.  Both children of every remaining `J_i` are
the same set

`K_i = C' union {v_i}`,

where

`C' = nu_beta(C_r minus E_beta) union I_beta`

is finite, and `v_i=nu_beta(rho_r(a_i))` are pairwise distinct outside
`C'`.  Choose `N>|C'|` good indices and form the sublist containing both
copies of their `K_i`.  It has length `2N`, whereas

`|union_i K_i| = |C'| + N < 2N`.

Rordam's Proposition 3.2 is explicitly a statement about finite lists,
so the repeated copies count separately.  Its Hall condition fails on
this sublist.  In particular the proposed argument cannot invoke
Proposition 4.5(i) at, or after, the paired step.  Notice that making
`I_beta` larger only increases the fixed finite number `|C'|`; the
infinite seed always permits choosing a larger `N`.
