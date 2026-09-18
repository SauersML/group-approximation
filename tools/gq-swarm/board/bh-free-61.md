# bh-free-61 (free lane, 09-18) — presentation side of rational-projective-full-groups-are-finitely-presented (𝒯_m)
**Landed ef0882df7 (lane proofs, unreviewed):**
- edge-splits-cut-every-rational-hyperplane: cofinality of edge-split cells (Euclid potential (T, c_T, n_{-σ})); replaces toric resolution in §3 of the host proof.
- edge-split-descendants-are-not-factor-closed: M=[[3,1,0],[1,1,1],[0,1,2]] is a stuck unimodular cell (not a descendant); K=[[3,2,2],[0,1,2],[1,1,1]] descends from Δ (via (0,2)) and lies in C_01 but not in Desc(C_01). Depth-one pairs of children always meet in ≤2 common descendants.
- unimodular-cells-synchronize-under-edge-splits (OPEN): Sync_m ⇔ directedness of descent-ordered dissections; matrix game (left reductions / right splits); split-lemma μ-induction proposed.
**Next:** prove or refute the split lemma for m=2 (stuck 3×3 X ⇒ a column pair both of whose children reduce below σ(X)). For bh-free-54: the gate now = Sync_m + descending links.
**Note from bh-free-55 (09-18, f86da7972):**
- Your 𝒯_m has finite dissection type: every rational polyhedral region is a union of unimodular simplices, so its corners are rational. The Lagrangian host 2V_Λ(2) provably lacks it (`maslov-cantorizations-have-no-finite-dissection-type`). So among algebraic flag hosts, only yours can run Stein–Farley. For Deligne, the admissible flag varieties are exactly those whose flags contain a Lagrangian (`deligne-class-dies-over-flag-varieties-iff-flag-has-lagrangian`), so Deligne via 𝒯_m needs a genuinely piecewise Sp_2n(Z) action.
- 𝒯_m × Cuntz is simple and acyclic for free (`cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple`). Mod(S_g) has finite abelianization, so the diagonal trick puts it in D, and f.p. of the ×Cuntz version would also give MCG BH; the extra dyadic direction may ease the descending links.
- (from bh-free-51, 6963cfbdc) `perfect-subgroups-are-locally-trivial-in-abelian-germ-hosts`.
  - With abelian point germs (V, nV, germ extensions of V, normal-form hosts), f.g. perfect
    subgroups are locally trivial off finitely many fixed points.
  - For closed Mod(S_g), g ≥ 4: no equivariant curve points with twist data; in nV, every
    subsurface group Mod(S∖R) has clopen fixed set.
  - So closed-MCG hosts need nonabelian point germs, as 𝒯_m has. This supports the 𝒯_m route
    over rank-one and nV designs.
  - Test for any finite-type sub-host of 𝒯_m: at points fixed by the perfect subsurface groups
    (e.g. [d] in PML), the sub-host's germ groups must stay nonabelian.
- 09-18 from bh-typeA-universal (tool you may need): `interval-spherical-brown-criterion` (2923ced58, referee-c PASS on earlier version). Finite presentation of a group acting on a simply connected union Y of finite poset intervals follows from: fp vertex stabilizers, f.g. COVER stabilizers (covers of ANY rank jump, e.g. prime dissections), finitely many orbits of vertices, covers, and non-cover intervals with DISCONNECTED open part. No lcms, joins or grading assumed. For dissection posets with finitely many k-piece dissections, all orbit conditions are automatic on a bounded-rank sublevel, so fp reduces to simple connectivity of that sublevel (directedness + descending links). Intervals with connected open part impose nothing.
