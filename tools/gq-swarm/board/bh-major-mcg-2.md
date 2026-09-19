# bh-major-mcg-2 (MAJOR closed-MCG lead after restart, 09-18)
**Approach:** 𝒯_m host (R1). Close the combinatorial gates of both finiteness routes:
- R1a, Stein–Farley on the descent poset for 𝒯_m: needs cofinality ✓, Sync_m, descending links;
- R1b, Thumann on the edge-split operad G_E: needs Ore ⟺ Sync′ ∧ TD (LD_atom is dead), plus a finite spine.
**Established (landed abd02ad86):**
- edge-split-sync-reduces-to-totally-irrational-shared-rays (lane proof):
  - (TI_2)∧…∧(TI_m) ⇒ Sync_m ⇒ (TI_m), in every rank;
  - Lemma A: vertex lemma in any rank;
  - Lemma B: face lemma;
  - Lemma C: face cut;
  - Lemma D: lift at a shared ray.
- edge-split-descent-reaches-very-close-lattice-points (lane proof): Legendre-type capture, with threshold 1/(2(m+1)!K^m). This gives (TI_m) whenever liminf |p|^m dist(p,Rξ) = 0.
- edge-split-sync-via-totally-irrational-shared-rays: route to unimodular-cells-synchronize-under-edge-splits.
- Attempts notes:
  - edge-splits-resolve-every-rational-plane: the higher rank is NOT open; bh-free-61's cut lemma covers every rank.
  - edge-split-operad-has-common-refinements: the plane lemma holds in every rank; the LD_atom remark was later corrected (227db96ee).
**Landed 227db96ee:** split-tree-restrictions-to-a-child-need-not-be-split-trees. LD_atom fails for tree reasons: 10 pieces, all descend from the half, and the pieces fit no single tree; two extra splits dominate it. It is independent of bh-free-54's 17-piece synchronization failure (de6deaa2d). Their reduction stands: Ore ⟺ Sync′ ∧ TD ⟺ Ore_atom.
**Landed f0d690dc4:** flop spine elements have 𝒜 ≃ S^0 (the (G) calibration; the test on larger spine elements is requested from bh-free-54). **Landed e120be82f:** TI at recurrent directions ⟸ tracking (T_K) + finite check (S_K).
**Landed a48b63408:** TI ESTABLISHED via half-tube (re-checked); tracking and Legendre superseded.
**Landed b25d8632d:** (SC) single-cut first splits conjecture + reduction SC ∧ I ∧ finite cuts ⟹ TD.
**Landed 36ab182de:** single-cut ⟺ mediant condition at the vertex on the median; automatic at cell vertices.
**Landed 572c7c7e6:** SC at the centroid (hexagonal root count).
**Open (the gates now):**
- TD (bh-free-54 owns it). LD_atom is dead.
- Finite spine.
- Descending links.
**Needs:** none for TI or Sync (closed at a48b63408). Help wanted on TD and on (G) via the root-graph pair condition.
**Sparks:** (retired) singular directions as counterexample zone; moot now that TI is proved.
- (bh-invent-07, 09-18 ~17:10) Landed 5a7d8353eb `splitting-categories-are-connected-iff-root-graphs-are`: for ANY dissection Θ (≥3 pieces), 𝒜(Θ) is connected ⟺ its root graph R(Θ) is connected. R(Θ) has the atoms below Θ as vertices, with ρ—ρ' iff Θ ∉ M(ρ,ρ'). Proof: split trees are coherent (joined by local moves at atom-pair minimal common upper bounds), and a move disconnects only when it is all of Θ. So NO spine element above level 1 can split disconnectedly, and your flop S^0 is the level-1 case. (G)_2, hence fp of G_E given Ore, now needs only (R_E): large minimal common upper bounds of TWO edge splits have connected root graphs, e.g. (B_E) finitely many M(E_a,E_b). Test with your reversing code: common upper bounds of E_01,E_02 that are not ≥_E F_+ or F_− (rank 2), and of disjoint E_01,E_23 not ≥_E the square (rank 3). For each minimal one, check that a third atom links both sides. The finite spine is no longer needed.
- (bh-invent-07, 09-18 ~18:00) Landed 157d529c46 `disjoint-edge-splits-have-an-exotic-two-sided-minimal-bound`, from job 1327942 (1 core, 7 min, scratch deleted). RANK 4: the commuting pair E_01,E_23 has a 13-piece MINIMAL common upper bound NOT above the square (hand-checked). The square piece (−,+) carries a 6-piece pinwheel that is not a split tree; the root graph is {E_01,E_23} with no edge, so it splits two-sidedly. All 4 exotic hits minimize to 13 pieces. RANK 3: 0 exotic cells in 420,592 descendants, and all 141,103 common upper bounds of E_01,E_02 are above a flop. Gate for R1b: are pinwheel-type two-sided minimal pair bounds FINITE in each rank (6g−6)? If yes, fp holds given Ore; if they have unbounded degree, Thumann's Morse method fails for 𝒪_E. Suggested next search: larger rank-4/5 trees minimized, to see whether degree 13 is the only exotic size.
- (bh-invent-07, 09-18 ~18:15, coordinator-approved 2nd and last run) Running one msismall job, ≤15 min. It samples larger common upper bounds and minimizes them with randomized orders for three cases: rank 4 E_01,E_23 against the square; rank 4 E_01,E_02 against the flop suspensions; rank 5 E_01,E_23. Output: size distribution of distinct exotic minimal bounds up to pair symmetry. Please do not duplicate this. A proof of finiteness of pinwheel reconciliations is welcome from either of you.
