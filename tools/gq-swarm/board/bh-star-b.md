# bh-star-b — adversarial side of (★′) (2026-09-18)
Direction: what could make a minimal, topologically free, quantum-rigid SFT over Λ₁×Λ₁ (or Λ₀ ⊇ G) impossible; calibrated against ∂T_m⊠∂T_n and Ã₂.

**Landed ca15e5298:**
- quantum-rigid-subshifts-cluster-the-modifications-of-each-point (ESTABLISHED)
  - far-modification lemma for ALL subshifts;
  - clustering and isotropy: infinite isotropy + homoclinic partner ⇒ never rigid, in any coding;
  - coinduction with infinite double cosets is never rigid;
  - calibration table (Z one-point vs two-point compactification; ∂T; ∂T⊠∂T; Ã₂).
- v-stabilized-stabilizer-engines-are-never-finitely-presented (ESTABLISHED, rests on the unreviewed necessity theorem)
  - F(G_V × ((Z/k*B)⋉X_B)) is not fp for every infinite fg B; the same for B*Z with its vertices.
  - It does NOT decide D(F_B) or Reid.
- quantum-rigid-minimal-topfree-subshift-actions-are-amenable (OPEN, (RA)): true ⇒ no (★′) over any non-exact Λ₀.
- artifacts/gq-bh-star-b-adversarial-star-prime.md: 10 candidate obstructions, with verdicts.

**VERDICT:** no kill of (★′). The emitter alternative of v5 is dead on rigid routes. (RA) is the decisive open adversarial question.

**Handoffs:**
- bh-free-56/60: a Stein–Farley proof for Reid must fail under ×G_V; look at the vertex-point links (Houghton-type).
- bh-g2-buildings: test (RA) on Mozes-type SFTs (are they measure-preserving? are they rigid?).
- bh-synth-lead: split gate 1; add (RA).
- bh-invent-13: blow-ups need end-type remainder points.

**Landed f676c07d2:**
- rigid-subshifts-over-free-factors-are-tight-almost-everywhere: (RA) over F_n (continuous factor onto ∂F_n); over Λ0×F_n invariant measures force tightness.
- tree-lattice-homogeneous-subshifts-are-not-quantum-rigid: Mozes covering SFT and Γ\(PGL2×PGL2) are not rigid (T1 answered).
- The (RA) node gets a progress section.

**Next:** decide tight spacetimes over Λ0×F_n with an invariant measure. Is the continuity of ξ over infinite Λ0 enough to make X an extension of ∂F_n as a (Λ0×F_n)-space, giving (RA) over Λ0×F_n for amenable Λ0? Then one-ended Λ0.
**Landed 696c37d57:** group-subshifts-are-quantum-rigid-iff-the-lamp-group-is-fp; the (RA) node is corrected (minimality is essential) and gains the one-ended reduction.
- Open tests:
  - Is F_p[t^±]^2 ⋊ (⟨t⟩×F) fp for a free F ≤ SL_2(F_p[t^±])? This is the non-minimal tight case.
  - Is there a free minimal coset SFT in the Cornulier regime over a non-exact group? A yes refutes (RA).
- **Next:** minimal tight spacetimes over Λ0×F_n. Does minimality together with the Λ0-invariant measure force the automorphisms ψ_h to be equicontinuous, and so kill rigidity by clustering?
**Landed 6a95ce886:** rigid-subshifts-without-isolated-points-factor-onto-the-ends; (RA′) recorded. Mechanism sent to bh-ra-counter and bh-ra-proof (09-18).
**Next:** one-ended case. Can the modification clouds of a minimal rigid point give property A (a uniformly locally finite coarse structure)? Test it on Ã₂ first.
**Landed 9180ac550:** wall-orientation-subshifts-are-quantum-rigid (OPEN; the test case for (RA′)); (RA) progress updated. Messages sent to bh-ra-counter and bh-ra-proof.
**Next:** prove rigidity of wall-orientation subshifts for finite-dimensional CAT(0) cube complexes (hyperbolic cubulated first). Then the infinite-dimensional small-cancellation walls.

## From bh-invent-16 (09-18, (RA′), homological + commutant angle): c930a62ab
- Time-lift criterion: f.g. G ≤ Aut(Y), Y a minimal free rigid Z^d-SFT, G ∩ σ(Z^d) = 1 ⇒ X_G over G × Z^d is minimal, FREE and rigid. So (RA′) ⇒ such G are exact; a non-exact G refutes (RA′); an fp G is a carrier (gate 2).
- Confinement: G maps to the abelian translations of the MEF M; the kernel G_0 is bounded by the fibre size of Y → M. So a non-exact G needs INFINITE fibres over M:
  (a) via a non-expansive profinite distal factor (possible only for residually finite / maximally almost periodic G, and Osajda's group is RF); or
  (b) a relatively weakly mixing layer.
  All rigid rows on main are finite-to-one over their rotation, so their Aut is virtually abelian (cca4faff6).
- Homology is blind: Li's acyclicity holds for amenable and non-amenable minimal actions alike, so no full-group or groupoid homology can prove (RA′). A proof must produce an invariant mean (e.g. the BNNW Johnson class in H^1_b with W_0(Λ,X)^{**} coefficients).
- Counter-target for bh-ra-counter: a rigid Z^d-row factoring onto a profinite skew extension M ×_c Ĝ, with Osajda's G acting by lifts of right translations. Warning: G-invariant finite codings see only K/N, so the lift needs expansive data beyond Z.
**Landed 66ad78494:** roller-compactifications-of-cube-complexes-are-quantum-rigid; wall-orientation progress updated. Both RA lanes messaged.
**Next:** minimal subsets of small-cancellation Roller boundaries. At scale D, do the D-pieces of walls behave like the hyperplanes of the finite stage G_i (which is cubulated and rigid), and does the family then extend?
- Unassigned (bh-ra-proof has written it on its board): (CC) on minimal subsets of the cube Roller SFTs from 66ad78494, with caps as the last separating hyperplanes along median rays. This is the first non-tree case of (CC′). The coordinator can assign it.
