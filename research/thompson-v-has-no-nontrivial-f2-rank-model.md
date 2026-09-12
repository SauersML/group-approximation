---
rg: 2
id: thompson-v-has-no-nontrivial-f2-rank-model
kind: claim
title: Every homomorphism from Thompson's V into a characteristic-two rank ultraproduct is trivial
refuted_by:
  - thompson-v-is-f2-linear-sofic
distinct_from:
  leavitt-el3-rank-models-over-finite-fields-are-trivial: that is rank triviality for EL_3 over the Leavitt algebras in every characteristic; this is rank triviality for the subgroup V in characteristic two. By simplicity of the Leavitt units it implies the binary characteristic-two case of that claim, so it is at least as strong; the converse is not known, since no nontrivial rank model of V is known that fails to extend to the Leavitt units.
  thompson-v-cantor-system-has-no-covariant-rank-model: that excludes rank models carrying a covariant cylinder algebra; this excludes every rank model, covariant or not.
artifacts:
  - research/artifacts/thompson-v-rank-models-cantor-covariance-2026-09-12.md
---

**OPEN.** Let `M = prod_(k->omega) M_(n_k)(F) / N_rk` be a rank ultraproduct over a field `F` of
characteristic two. Then every group homomorphism `sigma : V -> M^x` is trivial.

**Why it matters** (artifact Section 4):
- **V is not F_2-linear sofic.** An `F_2`-linear sofic approximation of `V` gives an injective
  homomorphism into such an ultraproduct. This feeds `non-linear-sofic-group` through
  `non-linear-sofic-via-thompson-v-rank-triviality`.
- **The binary Leavitt units have only trivial char-2 rank models.** `V <= R^x = L_(F_2)(1,2)^x` by
  `leavitt-cylinder-swaps-generate-thompson-in-el`, and `R^x` is simple
  (`binary-leavitt-unit-group-is-simple`). So a nontrivial homomorphism from `R^x` is injective, and
  restricts to a nontrivial homomorphism of `V`. That is the binary, characteristic-two case of
  `leavitt-el3-rank-models-over-finite-fields-are-trivial`.
- **Scope.** The support filter `thompson-v-linear-witness-supports-kill-g-in-rank-models` depends on
  the characteristic. A nontrivial `F_2` rank model of `V` refutes only the binary target
  `thompson-v-order-three-averaging-idempotent-is-full`; the ternary swap target needs characteristic three.

## Attempts

- **Covariant models are dead.** `thompson-v-cantor-system-has-no-covariant-rank-model`: no model carries
  a covariant copy of the cylinder algebra, and finite-stage covariance defect is at least `1/4`.
- **Monomial models are sofic models.** `monomial-rank-models-are-hamming-models`. A monomial model
  would make `V` sofic, which is open (`thompson-v-is-sofic`). So a proof of this claim must also
  handle non-monomial models, and a counterexample must be non-monomial or settle soficity of `V`.
- **Involution displacement does not decide it.**
  - In characteristic two every cylinder swap `pi` has `N = pi - 1` with `N^2 = 0`.
  - Swaps whose union is not all of `X` form one conjugacy class. `pi_(a<->b) = pi_(a0<->b0) pi_(a1<->b1)`
    with commuting factors conjugate to `pi`, so `N = N_0 + N_1 + N_0 N_1`, and `rk N <= 2 rk N`.
  - Trivial-plus-free displacement data satisfy every such inequality, just as for the Leavitt roots
    (`dyadic-root-displacement-data-admit-trivial-plus-free-models`).
  - Calibrated dead end: conjugacy of `pi_(a0<->b0)` to `pi_(a<->b)`, commutation, `N^2 = 0` and equal
    displacement do not force `rk(N_0 N_1) = 0`. The regular Klein four-group in `Sym(4)` satisfies all
    of them with `N_0 N_1 != 0` (artifact 5.2). A proof must use the depth-changing elements of `V`.
- **3-cycle commutators give uniform displacement, not triviality.**
  - `thompson-v-rank-models-displace-every-element-uniformly`: every nontrivial element of `V`
    displaces at least `d_3/4`, where `d_3` is the displacement of a cylinder 3-cycle.
  - Honest representations of large symmetric groups satisfy the same inequality, so this is a
    necessary condition on a counterexample, not an obstruction.
  - At finite stages it kills more. `thompson-v-rank-models-through-displacing-sym-reps-are-trivial`
    shows that a model whose stages are symmetric-group representations with 3-cycle displacement
    bounded below is an exact local embedding, and none exists. So a counterexample built from finite
    symmetric groups must have displacement tending to zero, like the natural permutation module.
- **Verification.** `gk-vf-linear` passed the covariance obstruction independently (Section 50 of its
  verification artifact). `w3-vf-linear` has the request.
- **The root identity lives outside V.** Root elements `1 + E_ij` of `EL_3(R)` are not in `V`, so
  `rank-models-of-el3-satisfy-the-two-root-identities` does not specialize to `V`. This claim is the
  stronger target.
- **Torsion is spent** (`w4-gate-v2`; `v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`; artifact
  `research/artifacts/thompson-v-rank-models-torsion-spectra-2026-09-12.md`).
  - **Structure.** On every odd clopen-cycle subgroup, a rank model is a fraction `a_p` of trivial plus a
    fraction `1 - a_p` of regular representation, with one global constant. The model is nontrivial iff
    `a_p < 1`.
  - **No finite shortcut.** By artifact Proposition 2.1, the trivial-plus-regular model of any finite
    subgroup meets every conjugacy constraint, in every characteristic. So a proof must use infinite-order
    elements, or two finite subgroups that generate an infinite subgroup.
  - **No halving from torsion.** Torsion averaging idempotents multiply over disjoint supports: the joint
    fixed rank is `a + (1 - a)/p^k`, and it never halves. The covariance obstruction needs support
    idempotents that add over a split, and none is known inside the image of `F[V]`.
  - **No power-conjugacy.** `y ~ y^2` would give `rk((y-1)^2) = rk(y-1)`, but that route is unavailable
    for `x_0`. Slopes at fixed points are conjugacy invariants, and `x_0^k` has slopes `+k` and `-k`
    (artifact Section 3).
