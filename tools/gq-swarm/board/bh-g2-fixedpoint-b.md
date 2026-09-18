# bh-g2-fixedpoint-b (G2-fp over a one-ended non-amenable group) — 2026-09-18

Landed 201fb24d4 (lane proof, elementary, unreviewed):
- free-group-boundary-shifts-are-quantum-rigid (+ free-group-boundary-shift-rigidity-proof). The end shift of any tree group (F_n, free products of Z and Z/2) is D-quantum rigid for every D ≥ 1 over every field. Mechanism: the edge identity E_{s^-1}(gs) = I − E_s(g), so the backward projections along any geodesic form an increasing commuting chain, and every label sits in or against that chain.
- With quantum-rigidity-is-product-stable: ∂T_m ⊠ ∂T_n over F_m×F_n is rigid, minimal and topologically free, but NOT free.

For other lanes:
- bh-invent-04 (Busemann transplants): for Γ = F_m×F_n on T×T, the boundary shift is an SFT (H_Ω) and is quantum rigid, by my node plus product stability. Rigidity also passes to the radius-K sector recoding, because site marginals of a higher-block family commute and block idempotents are products of them. So on products of trees your transfer needs only (C) and rigidity of Y over Z².
- bh-g2-f2f2: the one-ended non-amenable rigidity calibration is met for non-free shifts. Only freeness is left.

Not attempted or not closed:
- A fixed-point hierarchy over F×F. The boundary shift makes it unnecessary for rigidity. For freeness it would need a coupling that kills end-fixed points without an amenable Z^r fibre.
- The Roller-boundary (CAT(0) cube complex) analogue: posed on the node.

## Coordinator follow-up: the ABHT shift on F_n×Z, read at source (arXiv:2204.11492v3 §5; copy in src/bh-g2-fixedpoint-b/, md5 5e2f7f7e…)
Landed cc93f9797 (lane proofs, unreviewed):
- path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is (+ path-folded-sft-rigidity-pullback-proof).
  - Fold lemma: if an SFT contains every fold x∘β ⊗ y along a 1-Lipschitz surjection β, then the total shift being D-rigid ⇒ the fibre is D-rigid.
  - ABHT's Z is such a fold (their Prop configsJuntas), so Z is rigid ⇒ the horizontally expansive Labbé-type X is rigid ⇒ LC(X_0,k)⋊Z² is fp. The same holds for the unimodular GBS lifts and the BS(2,3) H²-fold.
- path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid (OPEN, the converse).
  - Proved: the flow marginals commute (end-shift theorem), and horizontal expansivity gives operator-level row determinism.
  - Open: centrality (C), the same step as bh-invent-04's.
Verdict: over F_n×Z, existence and skeleton rigidity are supplied. The fibre gate is exactly the Z² gate, plus the transfer (C).

## Relaunch after restart (09-18 ~15:00): E2 transport for self-simulation
Recovery: all 5 earlier drafts were already byte-identical on main; nothing to land. I had no probes and no MSI jobs.
Landed 5f2b02c48 (lane proofs, elementary, unreviewed):
- paradoxical-subshifts-are-never-quantum-rigid. BSS P_K has a finite recolouring (swap the colours of the two preimages of v) at a |K|-dense set of vertices. With the far-modification lemma, it is never rigid, and neither is P_H ⊠ P_V.
- causal-depth-localizes-quantum-noncommutativity (+ causal-depth-localization-proof). With a commuting base (B) and a causal rule of radius R ≤ D:
  - e_n(z)C_c(z) = C_c(z)e_n(z) ∈ 𝒜;
  - every commutator is killed by e_n(z)e_n(z');
  - bounded depth ⇒ rigid;
  - finite-dim W splits into W_fin (commuting) ⊕ W_∞, where W_∞ has base spectrum at infinite depth.
- end-shift-path-covers-are-rigid-with-one-spine.
  - ψ_1, ψ_2 (rank-1 and rank-2 children) are a radius-0 code of the end shift, and the paths are descending geodesic rays.
  - The spine {τ=∞} is empty unless ξ ∈ Σ_ν (finitely many orbits; for F_2 it is F_2·(b^{-1}a)^{+∞}). When nonempty it is one axis.
  - Time-graded seeded codings over pt ⊠ ∂T ⊠ ∂T are rigid off the single sheet Γ_0 × F_n × ℓ_η.
Answer to the directive: E2 does NOT reduce to a finite check for Track A self-simulation. What is true:
- The geometry can be made rigid, by the end flow of an added F_n factor.
- Seeded layers are free of charge.
- The residue is the infinite-depth computation: one sheet for seeded designs; everywhere for hierarchical (minimal) ones.
- The finite check (scale collapse) covers only the self-similar Z² skeleton. The input direction does not rescale.
Next: is the unseeded computation on ℓ_η unsplittable for some explicit tileset? And a causal-depth analogue for hierarchical codings: bottom-up determination of macrotiles.

## 09-18 ~16:45: unsplittable spine (coordinator follow-up, aligned with v6 rigid seeds, b5ad39956)
Landed 4c2d76fe4: seeded-transport-codings-over-end-flows-are-quantum-rigid (+ seeded-transport-rigidity-downhill-proof).
- Setting: base Y ⊠ X_∂(F_m). Rules: (Sp) bijective space transport α_s(p,·); (Ti) c(v') = β(p, c(parent v')) on second-child steps, with β any map; (Se) seeds elsewhere.
- Result: rigid on every module, over every field, for D ≥ max(R, r_Y, 1).
- Explicit tilesets: the spine bit; clocks Z/q (C_Z along second-child time); data-dependent cyclic phases.
- The spine sheet carries at most |C| global choices, so it is unsplittable.
- New tool, downhill centrality: an away step forces the target's flow letter, or the target's chain back onto the source.
Honest scope: these are functional (graph) couplings. By the heuristic MSS trichotomy they cannot give minimality, so they give no E1.
Next: is some relational (non-graph) phase coupling R_s ⊊ C×C unsplittable over the end flow? Where the proof breaks is recorded in the route's Remark.

## 09-18 ~17:15: relational coupling test (coordinator follow-up)
Landed 755489fe5: relational-spine-couplings-are-splittable-or-not-minimal. Also corrected the Lesson on seeded-transport-codings-over-end-flows-are-quantum-rigid.
- Minimal ⟺ every spine phase field is constant in space, with values in κ's β-cycle.
- The functional clock Z/q is minimal, topologically free and rigid.
- Relational tests:
  - clock + nonzero increment: wrap-around bumps, splits;
  - one-way step on Z: unsplittable (C_Z-like), not minimal;
  - one-way on F_2: cones split.
Note for bh-g2-fixedpoint-a (crossing-wire minimality): boundary completeness is the mechanism. Show that every infinite-level completion is a limit of finite-level ones, and that no completion class is unreachable (the analogue of a second β-cycle).
Next: data-reading seeds and transports (the CAP direction). Does downhill centrality survive seeds that read a non-rigid data layer?

## 09-18 ~17:40: data-reading seeds (coordinator follow-up)
Landed df763a98d: downhill-centrality-needs-no-data-rigidity.
- Abstract downhill lemma: (F1) flow commutes; (F2) flow–data commute; (F3) one-predecessor causal rule; (F4) downhill potential. Then the flow is central, with no data hypothesis.
- Seeded transport reading an input H-SFT Y: rigid ⟺ Y rigid (the converse needs (Surj), with scale D ↦ D+R). Minimal if Y is minimal and boundary completeness holds.
Shared with bh-g1-simulation: a board note plus SendMessage (delivered).
Next: check (F3)/(F4) for the actual keyed-slot layer in bh-g1-simulation's (★′) design. It needs their node; I will not duplicate their construction.
