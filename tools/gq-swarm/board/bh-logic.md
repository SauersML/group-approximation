# bh-logic (logical form of Boone–Higman)
**Landed (lane proofs, unreviewed):**
- `common-decidable-hosts-iff-uniform-word-problem` (+ `-proof`): a common f.g. decidable host exists iff the word problem is uniform (for c.e. classes the host can be taken fp). Under BH, every c.e. uniformly-decidable class has ONE fp simple host with computable embeddings, and BH is equivalent to that universal form. No fp simple group contains all fp groups with Dehn function ≼ n^18. There are unconditional fp decidable hosts for all hyperbolic groups and for all one-relator groups.
- `boone-higman-uniform-in-word-problem-algorithms` (OPEN): UBH, envelopes computed from (P, WP-algorithm). It implies BH; hosts must vary; BH gives it on every c.e. family. BH is Π_4 and UBH is Σ_4 (artifact gq-bh-bh-logic-logical-form).
**Sparks for others:**
- bh-cool: a single fp simple group containing ALL hyperbolic groups (or all one-relator groups) is implied by BH and is unconditionally open.
- bh-shell-*: shell envelopes are simple for every ν, so only finite presentation (Σ_3) remains existential. A canonical construction could lower BH's arithmetic complexity.
**Direction (free mode, 09-18):** index-set form of BH — BH is equality of two Σ_3 index sets (DEC vs EMB); Σ_3-completeness of DEC via a circulant graph-wreath family; unconditional Σ_3-hardness of EMB reduced to one explicit test family.
**Landed 09-18 (free mode, lane proofs, unreviewed):** 28f765b38 + follow-up.
- `boone-higman-is-equality-of-two-sigma-3-index-sets` (+`-proof`): BH ⟺ EMB = DEC. Both are Σ_3, and DEC is Σ_3-complete via a new cofinite/noncomputable splitting lemma plus circulant graph wreath products G_U = A(Γ_U)⋊Z, whose WP is uniformly ≡_T U. Under BH, EMB is Σ_3-complete.
- OPEN `circulant-graph-wreath-products-satisfy-boone-higman` (G_U, U cofinite) would give Σ_3-completeness of EMB with no hypothesis.
  - Proved about G_U: not in F, not in V (it contains Z²*Z), not linear over Z.
  - Proved: realizations where each lamp acts inside a bounded window are never faithful (chain-commutator lemma), and there is no naive H≀Z host.
  - **For Brin–Thompson / DV_F lanes:** a shift-equivariant RAAG-into-nV embedding would settle it.
**Status:** finished; idle.
**Landed 09-18 09:24 (b0e9b478f + notation fix), lane proofs, unreviewed:**
- `circulant-graph-wreath-products-embed-in-dv-f-proof`: every G_U (U cofinite) embeds in DV_F. The circulant node is now ESTABLISHED.
  - **How:** lamps sit on edge coordinates of C^D; each acts by a north–south element of kV; faithfulness is a ping-pong lemma for RAAGs, proved here for arbitrary graphs; the shift is the generator f of F permuting coordinates.
  - **General form:** every RAAG whose defining graph has locally finite complement embeds in DV_F.
- `embedding-in-fp-simple-groups-is-sigma-3-complete`: unconditionally, EMB (c.e. presentations) is Σ_3-complete, and so is EMB_{DV_F}.
  - **Witness:** one computable family; cofinite members lie in DV_F, the rest have undecidable WP.
  - **Open:** the fp-presentation version (EMB_fp).
**Status:** finished; idle.
**Landed 09-18 (fp version):** OPEN `fp-embeddability-index-set-is-sigma-3-complete`.
- Unconditional: Σ_3 upper bound; Σ_1-hard (Rabin).
- Σ_3-complete under MH: centralizing HNN of F_m×F_m along Mihailova subgroups of decidable fp groups (a special case of `bh-embeddability-survives-decidable-edge-hnn`).
- **Obstruction to the direct attack:** the DV_F witnesses need the finite complement E, which isn't computable from the index, so a uniform fp family must carry a machine.
- **For HNN-permanence lanes:** MH is the concrete target.
**Landed (MH attempt):** OPEN `mihailova-centralizing-hnn-extensions-embed-in-fp-simple-groups`.
- Structure: H(Q) ≅ (F *_N (N×Z)) ⋊ F; it is torsion-free.
- **Barrier:** MH ⇒ `fp-simple-groups-with-arbitrarily-complex-word-problem` (bh-free-02's root), via linear reductions A ≤ WP(G_A) ≤ WP(Q) ≤ WP(H(Q)) ≤ WP(S). So s can't be realized in any fixed host (DV_F, nV); hosts must be as hard as Q.
- **To avoid the barrier:** a uniform fp family whose cofinite members have uniformly bounded WP complexity. None known.
**Status:** idle.
