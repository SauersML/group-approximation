---
rg: 2
id: leavitt-el3-triviality-via-rank-four-cuntz-family
kind: route
title: A corner Leavitt family from the fourth index, with no ring rank model, trivializes EL_3 rank models
target: leavitt-el3-rank-models-over-finite-fields-are-trivial
requires:
  - rank-four-isometry-relations-give-corner-cuntz-family
  - leavitt-algebra-has-no-unital-rank-model
  - el3-unit-root-matrix-units-iff-two-root-identities
  - matrix-unit-rank-models-extract-ring-rank-models
  - el4-model-trivial-on-one-unit-root-element-is-trivial
  - nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple
  - reversed-root-pair-identity-forces-root-squares-to-vanish
artifacts:
  - research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md
  - research/artifacts/rank-four-corner-endpoint-and-framing-2026-09-12.md
---

Let `K` be a finite field of characteristic `p`, `R = L_K(1,2)`, and `sigma : EL_3(R) -> M^x` a rank
model into a characteristic-`p` rank ultraproduct. `EL_3(R)` is a subgroup of `R^x = EL_4(R)`, and
by `leavitt-gl-equals-el-and-perfect-unit-group` the two coincide for `R`, so `sigma` is a rank
model of `R^x`. Put `D = N_23 N_12`.

* If `D = 0`, then in characteristic two `N_12^2 = 0` is automatic and
  `el3-unit-root-matrix-units-iff-two-root-identities` makes the six unit root elements act by
  matrix units; `matrix-unit-rank-models-extract-ring-rank-models` then extracts a unital ring
  homomorphism `R -> p_1 M p_1`, or `sigma` is trivial. The first is excluded by
  `leavitt-algebra-has-no-unital-rank-model`. So `sigma` is trivial.
* If `D != 0`, then `rank-four-isometry-relations-give-corner-cuntz-family` gives an order-two
  Leavitt family in a corner `eMe` with `rk(e) > 0`, i.e. a unital homomorphism `R -> eMe` into a
  rank ultraproduct, again excluded by `leavitt-algebra-has-no-unital-rank-model`. So this case does
  not occur.

Either way `sigma` is trivial, which is `leavitt-el3-rank-models-over-finite-fields-are-trivial` for
`R = L_K(1,2)`. In odd characteristic the first case also needs `N_12^2 = 0`, which `D = 0` forces
(Framing, item 5). The route is valid once its single open prerequisite,
`rank-four-isometry-relations-give-corner-cuntz-family`, is established. The other six requirements
are established.

**Status (lead pass, family R4).** The route is valid and equivalent to the gate. The mechanism first
proposed for its open prerequisite does not work: every relation it lists lies in `U_4(R)`
(`unipotent-frame-relations-cannot-assemble-corner-cuntz-family`,
`unitriangular-data-cannot-assemble-corner-leavitt-families`). See artifact Section L7.

**Minimal form of the second case (lead pass, family R4).** The contradiction uses only
`T_0 S_0 = e = T_1 S_1` and `T_1 S_0 = 0` in `eMe` with `e != 0`. Then `(T_0 + 1 - e)(S_0 + 1 - e) = 1`,
and direct finiteness of `M` gives `S_0 T_0 = e`, so `T_1 = T_1 S_0 T_0 = 0` and `e = T_1 S_1 = 0`.
Completeness `S_0 T_0 + S_1 T_1 = e` is not used. Artifact Section L1.

**Framing (w4-r4-corner).** Artifact `rank-four-corner-endpoint-and-framing-2026-09-12.md`,
Sections 3.2 and 3.4.
1. **Which model the case split runs on.** `EL_3(R)` and `EL_4(R)` are identified with `R^x` only
   through prefix-code isomorphisms `phi_3` and `phi_4`. So run the case split on the transport
   `sigma_4 = sigma ∘ phi_3^-1 ∘ phi_4 : EL_4(R) -> M^x`. Its `EL_3` block is `sigma ∘ psi` for a
   non-surjective self-embedding `psi`. So `D` above means the block defect of `sigma_4`, not
   `sigma`'s own `N_23 N_12`.
2. **First case.** The block `sigma ∘ psi` is trivial. `el4-model-trivial-on-one-unit-root-element-is-trivial`
   then makes `sigma_4` trivial, and with it `sigma`.
3. **Finite `K != F_2`.** `leavitt-algebra-has-no-unital-rank-model` is stated for `F_2` only. For every
   finite `K`, both exclusions (of `R -> p_1 M p_1`, and of the corner family) are covered by
   `nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple`.
4. **Conclusion.** The route is valid, with these two established requirements added.
5. **Odd characteristic** (scope note from `w4-vf-gate`, e4d7e1c7fa). In odd `p` the first case needs
   `N_12^2 = 0` before the matrix-unit claim applies. The identity `D = 0` already forces it, by
   `reversed-root-pair-identity-forces-root-squares-to-vanish`, which is now listed in requires.

Payoff: through the target's own routes, `non-linear-sofic-group` for `K = F_2`, `n = 2`, and the
non-`F_p`-linear-soficity of `R^x` and of `PG`.
