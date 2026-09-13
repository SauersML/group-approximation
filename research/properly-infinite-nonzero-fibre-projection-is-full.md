---
rg: 2
id: properly-infinite-nonzero-fibre-projection-is-full
kind: claim
title: Every properly infinite projection in M(C(X) ⊗ K) with nonzero fibres is full
distinct_from:
  nonzero-fibre-projection-full-under-weak-omega-comparison: that proves this when Cu(C(X)) has weak omega-comparison; this is the unconditional statement over every compact metrizable X, open exactly where weak omega-comparison fails.
  self-similar-hilbert-cx-module-has-unit-section: that establishes unit sections and records this converse question in prose; this is the question as a node.
artifacts:
  - research/artifacts/k1-defect-ideal-corona-converse-2026-09-13.md
---

For every compact metrizable X, every properly infinite projection `P ∈ M(C(X) ⊗ K)` whose fibres are all
nonzero is full. Equivalently:
- `P ~ 1`;
- every countably generated Hilbert C(X)-module E with nonzero fibres and `E ⊕ E ↪ E` complementably is
  isomorphic to `H_X`;
- (AO) for such E, finitely many sections always admit a unit section that is uniformly almost
  orthogonal to all of them.

Why it matters (converse direction of the Corona Factorization question):
- **A yes** rules out every witness `I = K(E)` over a commutative base for
  `o2-multiplier-ideal-with-non-k1-injective-unitization`.
- **A yes** also rules out every commutative detector with compact defect for a non-null unitary of the
  Toeplitz defect ideal `J~`. Such a detector would refute LXI
  (`toeplitz-defect-ideal-connected-iff-extension-k1-injective`).
- **A no** gives the first candidate arena over a commutative base.

## Attempts

- **Weak ω-comparison** (`nonzero-fibre-projection-full-under-weak-omega-comparison`).
  - Property (S) holds automatically, so OPR Proposition 4.8 proves the claim whenever `Cu(C(X))` has
    weak ω-comparison. That includes every finite-dimensional X.
  - A counterexample needs a base where weak ω-comparison fails, such as `X = ∏ S²`, which lacks the
    CFP (OPR p. 1, after Rørdam).
- **Selection** (lanes ex-k1-halving-homotopy, ex2-k1-defect-ideal): dies at unbounded overlap.
  - Proper infiniteness gives orthonormal sections `η_j = V_2^j V_1 ξ` with
    `Σ_j |⟨ζ, η_j⟩(x)|² ≤ ‖ζ(x)‖²`, so pointwise some `η_j` is almost orthogonal to ζ.
  - Patching the indices by a partition of unity costs √(multiplicity), which is unbounded over
    infinite-dimensional X.
- **Cross-product and quaternionic tricks** for a single unit section ξ (ex2-k1-defect-ideal).
  - Exact orthogonal sections `Σ_k 2^{-k}(p_{2k+1} η_{2k} - p_{2k} η_{2k+1})`, where `p_j = ⟨ξ, η_j⟩`,
    vanish exactly where ξ is orthogonal to every `η_j`.
  - Adding a reserved direction there reintroduces a codimension-two bad locus. Removing that locus is an
    extension problem into a finite-dimensional sphere.
  - The infinite-dimensional sphere would remove the obstruction, but `x -> (p_j(x))_j` is only weakly
    continuous, and `{‖p(x)‖ = 1}` need not be closed.
- **Partial positive lemma**: if `sup_x ‖W^*ξ(x)‖ < 1` for some isometry `W ∈ L(E)`, then `ξ^⊥`
  contains a complemented copy of E.
- **Chern-class protection is impossible.** If `E = ⊕ M_k` with a trivial initial window of rank r, proper
  infiniteness forces the top Chern class of every late window to vanish. So tails without sections must
  be protected by secondary torsion obstructions.
- **Literature (bounded).** Checked:
  - OPR arXiv:0903.2917v4 sections 1 to 4;
  - OPR arXiv:0904.0541, already on main as `opr-properly-infinite-multiple-splits-citation`.
  The arXiv API search for "corona factorization" returned nothing (rate-limited). No statement of this
  converse was found.
