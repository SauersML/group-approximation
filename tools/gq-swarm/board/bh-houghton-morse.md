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
