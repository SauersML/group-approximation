# bh-houghton-morse
**Direction:** the Houghton-like lifting (bh-map 9b43b26d1), then after the redirect, the rigid-ν case.
**Finding:** the generic test case was already refuted by bh-map (6362d6c31). I re-derived it independently and did not duplicate that landing.
**LANDED 24dfc8368:** `fsym-containing-fp-groups-are-pinned-by-finitely-many-equations`. A general tool for any E ≤ Sym(X) with a finitely generated H = <A> ⊇ FSym(X):
- every hom fixing A is the inclusion, so finitely many relations pin B;
- Schreier-ball test: if every ball of the perturbed graph reappears in the original, E is not f.p.
**LANDED 348f2f784:** `zigzag-houghton-like-envelopes-are-virtually-houghton`. H_n(E_zigzag(Z)) is commensurable with H_(4n), so it is F_(4n-1) and not FP_(4n), for every n ≥ 1.
- The rigid case is realized for P = Z (nothing new for BH).
- Eventual periodicity is confined to virtually cyclic inputs (finite-ray node).
**Open lead:** non-virtually-cyclic P needs a ν whose ρ-edges pass the ball test's contrapositive (every far transplant detectable). Candidates are locally linear near relations λsλ⁻¹ = s^k (BS-type).
Status: done.

**ROUND 2, after the coordinator asked me to test my lead on Z²/BS(1,2)**
- **Correction:** my "λsλ⁻¹ = s^k" lead was impossible. The near index is invariant under conjugation, so k = 1, and then λ is finitary. The zigzag node is corrected.
- **LANDED ca0acda7f** `piecewise-translation-z2-enumerations-are-not-fp` (lane proof, no machine check).
  - Setting: any ν of Z² whose successor is a piecewise translation over finitely many polyhedral pieces.
  - R_ν has no F_2, and R_ν is NOT fp. So E_ν(Z²), every H_n(E_ν(Z²)) and the shell germ group are not fp.
  - Mechanism: translations give zero flux at each critical slice, so the offset character χ_θ is two-sided. Line-germ windows then block ascending splittings in both directions.
  - This generalizes the square spiral and proves the diamond-spiral prediction.
- **Surviving lead:** piecewise-ISOMETRIC polyhedral enumerations of Z² (rotations or reflections, as in the 1-D zigzag). There half-lines migrate between slices, and the end characters behave like Houghton's ray characters, with no antipodal obstruction. Also open: congruence-refined pieces (expected dead).
- BS(1,2) not attempted.
Status: done.

**ROUND 3 (INSIGHT FIRST; merge pinning, flux and lifting)**
- **LANDED 05c53d0dc** `zero-flux-strand-stacks-obstruct-fp-amenable-near-groups`.
  - Algebraic lemma: an F_2-free group acting on a Z-stack of strands with equal end speeds, a uniform shift and a non-uniform kernel element is not f.p.
  - Corollary for Z²: every polyhedral enumeration, isometries allowed, that has an active zero-flux slice dies. The rotating-quadrant enumeration dies (zero holonomy).
- **Merged picture:**
  - Pinning (bh-free-48) forces rigid relators.
  - Rigid *linear* relators create strand stacks.
  - A zero-flux stack plus an F_2-free near group means not f.p.
  - Survivors: (a) enumerations that transport stacks, with nonzero flux holonomy and at least 3 non-antipodal stack ends (Houghton-like, untested); (b) R_ν ⊇ F_2, where Σ-methods are blind. Lifting (bh-free-47) has no certificate for one-ended inputs over the lampshuffler base.
- **Neither decisive theorem is proved.** "No one-ended input" would need a non-Σ mechanism in case (b). A construction would need (a) plus pinning plus lifting.
- LESSONS.md appended.
Status: done.
