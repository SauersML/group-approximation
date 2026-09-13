---
rg: 2
id: ah-face-bundles-are-trivial
kind: claim
title: Every W*-bundle over a closed set of extreme traces of a unital AH algebra is trivial
distinct_from:
  central-halving-trivializes-every-closed-bauer-face-bundle: that proves triviality for algebras with central halving; this asks for it for every AH algebra, whatever its connecting maps.
  nontrivial-w-star-bundle-with-r-fibres-exists: that asks whether any nontrivial hyperfinite W*-bundle exists; this asserts that none arises from a closed face of an AH algebra, so a failure answers that question while a proof confines witnesses to non-AH sources.
  toms-no-gamma-algebra-is-trivial-on-closed-bauer-faces: that is the special case of Toms's towers, which are block-balanced.
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

**OPEN.** Let `A = lim q_n(C(X_n) ⊗ K)q_n` be a unital separable AH algebra, with
compact metrizable `X_n`, arbitrary unital connecting maps, and no finite-dimensional
representation. Then for every nonempty closed `K ⊆ ∂_e T(A)`, the W*-bundle `M_K` of
`closed-extreme-trace-sets-give-r-fibre-w-star-bundles` is trivial.

**Why it matters.** A counterexample answers BBSTWW Question 3.14, and AH algebras need
not be simple here. A proof shows that no AH source, simple or not and with any trace
simplex, carries a projection-starved bundle.

**Known cases.**
- **Block-balanced towers**, including Toms's no-Γ algebra
  (`block-balanced-towers-have-central-halving` and
  `central-halving-trivializes-every-closed-bauer-face-bundle`).
- **Simple non-elementary AH algebras of stable rank one.** Vaccaro (arXiv:2604.24682v2,
  Theorem A and Corollary 4.1, as recorded on `stw99-problem-xx-villadsen-algebras-uniform-gamma`)
  gives uniform property Γ, hence central halving.
- **Finite-dimensional `K`**, and countable unions of closed finite-dimensional subsets
  (`r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`).

## Attempts

- **Close partners (heuristic, not proved).**
  - At a point `y` of a late stage, the connecting map from stage `n` has `L` eigenvalue
    points in `X_n`. Cover `X_n` by `N_r` balls of radius `r/2`. At most `N_r` of the `L`
    points lack a partner within `r`, whatever the configuration.
  - Rotating between the blocks of two `r`-close points is approximately central for a
    fixed `a ∈ A_n`, with error the modulus of continuity of `a` at `r`.
  - So a soft matching of close pairs gives, pointwise in `y`, an approximately central
    projection of trace within `N_r/L` of `1/2`.
  - **Where it dies.** Continuity in `y` over high-dimensional `X_m`. The space of such
    halvings is Grassmannian-like, and its obstruction classes are Villadsen-type
    characteristic classes. Twisting line bundles can prevent even local rotations from
    gluing.
  - Relative to a closed face, 2-norm approximation would allow excising sets of small
    measure uniformly in `λ ∈ K`. No excision theorem of that form was proved.
- **Symmetric (braided) doubling (heuristic).** Replace ordered pairs by unordered pairs,
  the real blow-up of `X × X` along the diagonal modulo the swap. Then block projections
  exist only on the double cover, so Proposition B does not apply.
  - The close-partner mechanism still suggests central halving over iid-type faces. Among
    `L` iid points only a fraction `≤ N_r/L` is isolated, uniformly over the base measure.
  - So braiding alone looks insufficient.
- **Where a counterexample must live.**
  - No balanced block splitting from infinitely many stages.
  - Higher stable rank, in the simple case.
  - A closed family of extreme traces on which close-partner matchings cannot be glued in
    measure.
  - By `bauer-gamma-failure-localizes-to-infinite-dim-point`, a strongly
    infinite-dimensional part of `K`.
- **Twisted homogeneous blocks do give witnesses; untwisted blocks resist the same argument
  (2026-09-13, lane `ex2-tw-unsplittable-tails`, unreviewed).**
  - **The witness.** Flat `M_2`-bundles with Pauli holonomy over
    `RP^{4^{k−1}} × RP^{2·4^{k−1}}`, tensored along the tower.
    - They give a nontrivial face bundle, in fact the whole bundle: every self-adjoint element is
      somewhere scalar (`pauli-tower-bundle-has-scalar-point-property`).
    - The building blocks are homogeneous but have nonzero Dixmier–Douady class, so they are not
      corners `q C(X, M_n) q`, and this is not an AH presentation.
  - **Why it does not transfer to AH.**
    - The certificate is the top Stiefel–Whitney class of the traceless self-adjoint bundle.
    - For `End(W)` of a genuine vector bundle that class is pulled back from `BU(w)`, and it vanishes
      identically.
    - Mod-`p` Borel cohomology gives nothing either. Elementary abelian subgroups of `U(n)` are
      toral, so they fix soft half projections. By Quillen stratification,
      `H*(BU; F_p) → H*_G(X_ε; F_p)` then has nilpotent kernel, and the source has no nilpotents.
  - **What remains for AH.** Any AH witness of this kind needs an unstable (non-Borel) obstruction,
    or relative commutants that are twisted although the blocks are not. Diagonal maps with
    multiplicity create block projections in the commutant, hence central halving
    (`block-balanced-towers-have-central-halving`). Braided (monodromy-permuted) blocks are the
    untested case.
