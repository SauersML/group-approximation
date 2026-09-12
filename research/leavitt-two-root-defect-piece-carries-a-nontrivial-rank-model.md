---
rg: 2
id: leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model
kind: claim
title: In a nontrivial characteristic-two rank model of the Leavitt unit group, the Kazhdan subgroup acts on a corner pair's defect piece by a nontrivial rank model and never fixes it
distinct_from:
  two-root-identity-is-corner-local-for-leavitt-rank-models: that is the per-model equivalence between triviality and the two-root identity on any cylinder corner; this combines it with fixed-ideal globality to show that the defect piece of a corner pair in the centralizer of the Kazhdan subgroup is never fixed and carries a nontrivial rank model of the same group.
  leavitt-rank-models-kazhdan-fixed-ideals-are-global: that identifies what the Kazhdan subgroup fixes with what the whole group fixes; this shows the two-root defect piece is never among those fixed objects in a nontrivial model.
artifacts:
  - research/artifacts/two-root-defect-piece-and-fd-representations-2026-09-12.md
---

**ESTABLISHED** (proof route `leavitt-two-root-defect-piece-rank-model-proof`; artifact Section 1;
independent re-derivation requested from `w3-vf-linear`).

**Setting.**
* `R = L_(F_2)(1,2)` and `iota_P(g) = S[P] g T[P] + (1 - S[P]T[P])`.
* `Gamma = iota_0(R^x)` is the nine-leaf Kazhdan subgroup of units supported on `[0]`.
* `x' = iota_1000(x_12(1))` and `y' = iota_1000(x_23(1))`.
* `sigma : R^x -> M^x` is a nontrivial homomorphism into the units of a rank ultraproduct over a
  field of characteristic two, and `P = (sigma(y') - 1)(sigma(x') - 1)`, with `PM = qM` for an
  idempotent `q`.

**Statement.**
1. `qM` is `sigma(Gamma)`-invariant, so `gamma -> q sigma(gamma) q` is a homomorphism
   `Gamma -> (qMq)^x`.
2. That homomorphism is nontrivial. Composed with `iota_0` it is an injective rank model of `R^x`
   on the corner `qMq`, of normalized rank `rk(P) > 0`. In particular `qM` is not pointwise fixed
   by `sigma(Gamma)`.
3. For every prefix `P'`, `q (sigma(iota_(0P')(x_23(1))) - 1)(sigma(iota_(0P')(x_12(1))) - 1) q != 0`.
4. If `u` in `R^x` conjugates `(x', y')` to `iota_(0P')` of the unit pair, for instance a prefix
   replacement taking `[1000]` onto `[0P']`, then `q sigma(u) q != 0`.

**Consequence for the gate.** Step 1 of the mechanism audit
(`research/artifacts/two-root-identity-nonsofic-mechanism-2026-09-12.md`, Section 3) says the
defect piece is invariant, not fixed, and that globality only reaches fixed objects. The fixed case
cannot occur in a nontrivial model, so globality is already used in full. What remains is
self-reproducing: the defect piece carries a nontrivial model of the same group, whose own defect
pieces lie inside it, with ranks weakly decreasing. A contradiction along this line needs a uniform
bound on that descent. Nothing proved here supplies one.
