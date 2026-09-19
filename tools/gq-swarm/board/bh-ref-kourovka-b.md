# bh-ref-kourovka-b
Direction: adversarial referee pass on the answers to Kourovka 21.74(b),(c) and 21.75.

**Status:** done (2026-09-18). Landed as fac0259d6b.

- `ct-z-finite-cycle-problems-are-undecidable` (21.74(b),(c)): **PASS**.
  - Conditional only on Kari–Ollinger MFCS 2008 Theorems 3 and 6, which I read in the PDF
    (gq/src/bh-free-58).
  - Robustness note: (c) can use the complete-3-RCM clause with a third prime (17), which avoids
    KO's one-line 3→2 conversion.
- `ct-p1-and-ct-p2-always-generate-ct-p1-union-p2` (21.75): **PASS**, elementary.
  - The printed 17.60 definition contains `P ∪ {2}`, which is what the proof uses.
  - Its "finite generation / F_∞" consequence cites `ct-p-z-is-a-one-vertex-k-graph-full-group`. That
    is not refereed here, and it would also settle 17.61, so it needs its own referee pass.
- `ct-z-north-south-element-has-no-finite-cycles`: the formula and items 1 and 3 **PASS**. Item 2
  (the 21.74(a) no-instance) is not reviewed.
- Printed texts checked against arXiv:1401.0300v46 (1 Sep 2026); local text at scratchpad/kourovka.txt.
- Priority searches (09-18) found nothing on 21.74 or 21.75. arXiv:2607.17477 covers 21.8 only.

## Batch 2 (2026-09-18, coordinator): landed 4697bc8f58
- `ct-p-z-is-a-one-vertex-k-graph-full-group` (Kourovka 17.61): **PASS**, conditional on Li, Matui
  and FKPS as cited.
  - `Y = X` is right with `𝔢_P = ∅`: Li's `X(e; 𝔣)` definition, and his corollary at l.2082.
  - `I_l ⋉ ∂Ω = G_Λ` holds: Li 2209.08087 l.875, plus a direct check that `Λ_P` is singly aligned
    and both groupoids are effective.
  - For 17.61 alone, only `cor:OneVertex` is needed, given PC = CT_P(Z).
- `pbh-class-closed-under-graph-products` (BFFHZ Q3.1): **PASS**. Every step of
  `pbh-graph-product-closure-proof` was checked, and BFFHZ Theorems C and E and Q3.1 were checked
  against the TeX.

## Batch 3 (2026-09-18, coordinator): landed 21a63f2691
- `(Sync_m)` in every rank (bh-free-61): **PASS**. Covers `half-tube-lattice-points-are-edge-split-vertices`
  and `unimodular-cells-synchronize-under-edge-splits-proof`, all steps. One wording note: `u ≥ 0` follows
  from integrality for every Dirichlet `q`.
- `oligomorphic-actions-with-f-n-set-stabilizers-are-f-n` and
  `circle-pl-groups-inherit-finiteness-from-interval-groups` (bh-near-actions): **PASS**.
  - Priority: Stein 1992 very likely covers `T_{2,3}`; BNR assert `T_τ`.
  - The V halves were not reviewed.
- `two-point-gluing-presentation-of-v-is-exact` and `splitting-kills-…` (bh-one-relator): **PASS**,
  conditional on the GAP certificate. I read the script and all its relators hold in `Γ~`; it was not
  re-run.

## Batch 4 (2026-09-18, coordinator): landed e1de4c7e75
- `sw-crossing-wire-tiles-give-free-rigid-sfts-on-kazhdan-lattices`: the Layout Lemma **FAILS** as written.
  - Causality gap: SW-determinism makes top bit `p` depend on bottom bits `≤ p` only, and the one-zone
    design with shared input/output positions does not handle this.
  - A multi-block repair looks plausible. The node stays CONDITIONAL, and its item (a) was not reviewed.
- `four-way-deterministic-sft-rigidity-lives-on-axis-faults`: items 1–4 **PASS**, with an ordering fix in the
  SE corner. Item 5 is heuristic.
- `a2-lattices-carry-finite-type-seeds`: **PASS**.
- `relational-spine-couplings-are-splittable-or-not-minimal`: **PASS**.

## Batch 5 (2026-09-18, coordinator): landed 42748830d6
- `odometer-root-hosts-are-non-affine-and-non-contracting` (bh-gln-tracka): **PASS**.
- `adder-hosts-linearize-odd-odometer-roots` (bh-free-16): **PASS**. Its 2V_H framework node was not
  re-refereed.
- `sft-isolated-points-are-finite-state-across-finite-edge-groups` (bh-g3-topfree): **PASS**, with a
  (UE) wording note.
- `relative-seeds-on-free-groups-have-fg-stabilizers` (bh-g1-universal-point): **PASS**.
