---
rg: 2
id: covariant-monotone-cylinder-families-in-rank-models-are-constant
kind: claim
title: In a rank ultraproduct every Thompson-covariant refinement-monotone family of principal ideals indexed by proper cylinders is constant
distinct_from:
  thompson-v-cantor-system-has-no-covariant-rank-model: that proves covariant cylinder idempotents cannot have additive positive rank; this needs only monotonicity of principal ideals, and applies to image spans of root groups, which are not idempotent families.
  leavitt-two-root-defect-piece-forces-covariant-diagonal: that asserts a violation of the two-root identity gives a covariant orthogonal diagonal; this shows that conclusion holds in no rank model and that the plan's first lemma, coincidence of refined root spans, is an automatic instance holding in every rank model whatever the defect.
  two-root-identity-is-corner-local-for-leavitt-rank-models: that is the per-model equivalence between triviality and the corner identity through ring-rank extraction; this gives a group-theoretic proof, with no ring rank model, that the all-coefficient identity on a frame (a0, b, a1) forces triviality.
artifacts:
  - research/artifacts/covariant-diagonal-plan-adversarial-audit-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-r4-adversary`; verification requested from `w4-vf-gate`) by
`covariant-monotone-cylinder-families-constant-proof`.

**Setting.**
- `M` is a rank ultraproduct of matrix algebras along a nonprincipal ultrafilter on `N`, or a nonzero
  corner of one.
- `V` is Thompson's group acting on `X = {0,1}^N` by prefix replacement, and `sigma : V -> M^x` is a
  homomorphism.

1. **Joins exist.** Countable families of principal right ideals have joins, of rank equal to the
   supremum of their finite joins; dually, countable meets exist. This follows from countable saturation
   and faithfulness of rank.
2. **Monotone rigidity.** Let `A_w`, over proper cylinders `w`, be principal right ideals with
   `sigma(v) A_w = A_(vw)` whenever `v` carries `w` onto a cylinder by prefix replacement, and with
   `A_(w0), A_(w1) ⊆ A_w`. Then all the `A_w` are equal. The same holds for left ideals.
3. **No orthogonal diagonal.** Hence covariant orthogonal idempotents with `e_(w0) + e_(w1) = e_w` are
   all zero.
4. **Root spans.** Let `R = L_(F_2)(1,2)` and `sigma` be a characteristic-two rank model of `R^x`.
   - The image and co-image spans of the root groups `1 + s_w R t_(w')` depend only on the branch
     component of the pair `(w, w')`.
   - If `N_(b,a1)(y) N_(a0,b)(z) = 0` for all `y, z` on one frame of disjoint cylinders `a0, b, a1`,
     with `a ∪ b != X`, then `sigma` is trivial.

## Consequences

- **The diagonal claim is the gate.** `leavitt-two-root-defect-piece-forces-covariant-diagonal` has a
  conclusion that holds in no model, so the claim is equivalent to the characteristic-two gate. Its
  route stays valid.
- **The plan's first lemma is inert.** It is item 2 applied to root spans, and it holds in every rank
  model. Every orthogonal family is monotone, so the missing input "orthogonality" is exactly the
  contradiction.
- **The kill tests.**
  - (a), joins, is not a kill.
  - (b), the Toeplitz Kazhdan group, is consistent: its invariant trace forbids depth-changing units.
  - (c) is the gate itself.
- **What root spans carry.** Only the known direction, nontrivial ⟹ violation, here with a proof that
  uses no ring rank model.

## Attempts

- Established, not open. Artifact Sections 1–5.
