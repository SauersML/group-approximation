---
rg: 2
id: signed-thompson-z-moving-rank-functions-match-v-rank-functions
kind: claim
title: The signed Thompson group algebra has a rank function moving minus one iff Thompson's V has a non-augmentation rank function
distinct_from:
  simple-group-rank-functions-are-augmentation-or-detecting: that classifies the rank functions on the algebra of one simple group; this transfers rank functions between the signed Thompson group and V, through the unsigned subgroup in one direction and an embedding of the signed group as the centralizer of a fixed-point-free involution of V in the other.
  ternary-leavitt-rank-models-move-z-iff-nontrivial: that is for the whole ternary unit group, where moving z is automatic; this is for the subgroup E ⋊ V, where moving z is equivalent to a nontrivial rank function of V itself.
artifacts:
  - research/artifacts/signed-thompson-minus-one-gate-is-v-rank-gate-2026-09-12.md
---

**ESTABLISHED** (artifact Sections 1–3). Verified by `w4-vf-gate`: PASS, §21 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md` (d9bc4a55ad). Let `H = E ⋊ V <= L_(F_3)(1,2)^x`
be the signed Thompson group, with `E = {tau_C = 1 - 2P_C}` and `z = tau_X = -1`. Let `K` be any field. The
following are equivalent:
1. `K[H]` carries a Sylvester matrix rank function with `rk(1 - [z]) > 0`;
2. `K[V]` carries a Sylvester matrix rank function other than the augmentation rank;
3. `K[V]` carries a Sylvester matrix rank function detecting every nontrivial element.

**How the directions go.**
- **(1) ⟹ (2):** restrict to the unsigned `V <= H`. If `V` lay in `N_rk`, conjugation would put all `tau_A`
  with `A` proper in one class `c`. Then `tau_[0] = tau_[00] tau_[01]` gives `c = c^2 = 1`, so `z` would lie
  in `N_rk`.
- **(3) ⟹ (1):** pull back along the embedding `phi : H -> V'`, `phi(tau_C)(ε x) = (ε + 1_C(x)) x`,
  `phi(g)(ε x) = ε (gx)`. It sends `z` to the first-letter swap `σ_0`, and its image is `C_(V')(σ_0)`.

Only the Sylvester axioms, simplicity of `V` and transitivity of `V` on proper clopens are used. The same
equivalence holds for rank models into rank ultraproducts or abstract rank algebras. In characteristic
`!= 2` a z-moving model compresses to an anti-central one.

**Consequences** (artifact Section 4).
- "Every Sylvester rank function on `F_3[H]` kills `1 - [z]`" is `thompson-v-ternary-rank-functions-are-augmentation`.
  Proving it would make `V` nonsofic, so the `E ⋊ V` route to the characteristic-three gate is the rank
  gate of `V`.
- If `F_3[V]` carries a non-augmentation rank function (for example if `V` is sofic), there is no ternary
  corner witness supported in `H`, and `odd-measure-crossed-product-unit-below-cylinder-idempotent` is false.
- A "No" proof for `G_3` that does not settle `V` must use elements outside `H`.

Proof: route `signed-thompson-z-moving-rank-functions-proof`.
