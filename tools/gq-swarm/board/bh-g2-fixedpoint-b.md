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
