---
rg: 2
id: bounded-p-part-twisted-weyl-homs-proof
kind: route
title: Split the level, run the evaluation on the coprime leg, and read the residue as a twisted equivariance
target: bounded-p-part-sector-reduces-to-twisted-weyl-homs
requires:
  - odd-congruence-lambda-exact-sector-collapses
---

**Part 1.**  With `b_m <= C`, pass to a subsequence on which the
`p`-part representation is a fixed `sigma_p` of `SL_3(Z/p^C)`;
`sigma_m = sigma_q^(m) otimes sigma_p` by CRT
(`SL_3(Z/n) = SL_3(Z/q) x SL_3(Z/p^C)`).  Property (T) lifting (as
in the coprime proof, Step 1) places any element commuting with
`pi(Lambda_-)` into the ultraproduct of the levelwise commutants
`sigma_m(Lambda_-)' = R_q otimes-bar B`, using that the image of
`Lambda_-` in the coprime factor is full (it contains `Lambda(p^2)`,
which surjects mod `q`) and its image in the `p`-factor is the fixed
parahoric image with commutant `B`.  Choosing `lambda_h = h mod q`,
`= 1 mod p^C` (CRT surjectivity of `Lambda`), the slot
`V' = sigma(lambda_h)` has trivial `p`-leg, so it lies in
`sigma_q(G_q) otimes 1`, commutes with `R_q otimes-bar B`, and
implements `Ad(h)` on `pi(Lambda_-)` up to the `p`-leg (exactly on
the `q`-leg; the `p`-leg of the conjugation relations is carried by
`W`).  Both `V` and `V'` conjugate `pi(Lambda_-)`-elements by the
respective relations, so `W = V'^* V` commutes with `pi(Lambda_0)`
for the finite-index (T) subgroup on which the two conjugations
agree levelwise, and (T) lifting places `W in R_q otimes-bar B`.
For a Weyl element `w in Lambda`, `pi(w) = sigma_q(w) otimes
sigma_p(w)`; the `sigma_q(w)`-leg acts trivially on
`R_q otimes-bar B`, so `Ad(pi(w)) W = W^((w))` as defined.

**Part 2.**  Repeat the coprime evaluation with the split slots.
For the inversion relation: `pi(w_13) V pi(w_13)^(-1) = V^(-1)`
with `V = V' W` gives `[pi(w_13) V' pi(w_13)^(-1)] W^((w_13)) =
W^(-1) V'^(-1)`; the bracket is the slot of `h^(-1) mod q` (trivial
`p`-leg), equal to `V'^(-1)`, and slots commute with
`R_q otimes-bar B`, so `W^((w_13)) = W^(-1)`.  For the three-term
relation `pi(h) pi(h'')^(-1) = pi(h')`: `pi(h'') = pi(w_23) V
pi(w_23)^(-1) = V'_(h'') W^((w_23))` and `pi(h') = V'_(h')
W^((w_12))` with the primed slots again of trivial `p`-leg; since
`V' V'_(h'')^(-1) = V'_(h')` exactly on the `q`-leg (the mod-`q`
values multiply as in the coprime proof) and all slots commute with
the corrector algebra,

```text
V' W W^((w_23))^(-1) V'_(h'')^(-1) = V'_(h') W^((w_12))
  ==>  W (W^((w_23)))^(-1) = W^((w_12)).
```

Commutation `[pi(h_x), pi(h_y)] = 1` transports likewise to
commutation of the `W^((w))` family.  This is `(BP1)`, and the
family `x mapsto W_x` (defined on the Weyl orbit of the fundamental
coweight through the conjugates and extended by the lattice
relations, which `(BP1)` makes consistent) is a homomorphism of the
coweight lattice equivariant for the `S_3`-action twisted by
`Ad(1 otimes sigma_p(w))`.

**Part 3.**  If the twist is trivial the equivariance is the
untwisted one and the vanishing of the `S_3`-coinvariants of the
coweight lattice (each transposition negates a root coweight, the
cycle identifies them — the computation recorded in
`odd-congruence-exact-sector-is-one-inner-action`) forces
`W_x = 1` for all `x`, recovering the coprime collapse.  In general
the solution set of `(BP1)` is the set of twisted-equivariant homs
into the unitary group of the abelian von Neumann algebra generated
by the family — determined, for each gauge, by the `S_3`-action of
`sigma_p|_(Weyl)` on the finite-dimensional `B` — which is the
classification object named in the claim; no attempt is made here to
solve it.
