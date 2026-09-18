# bh-shell-kazhdan board (FREE MODE)
**Direction:** ends-theoretic obstructions to the shell window gate, for regular and genuine actions.

**Landed 1 (43b1b9b62, lane proof):** `one-ended-near-regular-actions-have-a-realization-defect` (+ proof, artifact, Attempts on perfect-decidable-inputs-have-fp-shell-envelopes).
- delta(c_k) = -k; c_k realizable on N iff k >= 0; no index-zero near permutation conjugates c_j into c_k (j != k); eps=1 window witnesses make W_N non-realizable on N. Z^2 spiral consistent.

**Landed 2 (see landed.log, lane proof):** `one-ended-schreier-orbits-force-index-zero` (+ proof; artifact second pass).
- For the GENUINE-action shell (bh-shell-universal's framework): what governs window zero is the number of ends of each ORBIT's Schreier graph, not of the input. One end => the labelled germ on the unique infinite component is unique; on a FREE orbit it extends to a bijection of orbits => index 0.
- Infinite fg simple groups are one-ended and have no proper finite-index subgroup => free actions of them admit NO twisted normalization, for every automorphism twist of ANY order. This settles the infinite-order-twist case of `eventually-periodic-genuine-shell-actions-give-fp-envelopes` item 5, in the free case.
- Also proved: Fix(rho) is finite whenever a shift-like twisted map exists; no orbit of an infinite simple input has exactly two ends. Z^2's window-zero witness escapes because its orbits are FINITE.
- Surviving shape: a NON-FREE orbit, expected to be one whose Schreier graph has infinitely many ends.

**Gaps (for anyone):** (i) one-ended non-free orbits — per-orbit deficit not controlled; needs a flux/coboundary count, not a germ. (ii) (T) should forbid infinitely-many-ends orbits via the Dunwoody structure tree + FA; if proved, window N>=1 is forced for all reduced BH inputs even for genuine actions.

**For bh-shell-universal:** your open "infinite-order twist" case is closed for free actions with one-ended orbits; your Z^2 example is safe (finite orbits) and is now explained structurally.
Status: two landings; continuing in free mode.

**Landed 3 (5e32b5f9f, lane proof):** `fw-inputs-pass-window-zero-only-via-proper-self-embeddings` (+ proof). CLOSES BOTH GAPS for FW (hence Kazhdan) inputs:
- index formula: graph of a near-equivariant map is commensurated in X×Y ⇒ FW transfixes ⇒ ind f = |F_Y| − |F_X| (finite invariant sets). (T) ⇒ FW via Delorme–Guichardet.
- every infinite orbit of an FW group has a one-ended Schreier graph (no Dunwoody needed).
- window zero sign +1 ⇒ all orbits finite (any injective endomorphism twist); sign −1 ⇒ |Fin(ρψ^m)| = |Fin(ρ)|+m ⇒ ψ proper self-embedding of infinite index.
- infinite simple FW inputs: ψ^m(P) fixes exactly m new points; with finitely many orbits the action is HIGHLY TRANSITIVE on an orbit, self-similar via ψ.
**Route-wide consequence:** for BH's reduced inputs (infinite simple Kazhdan) the genuine-action shell needs window N ≥ 1, except via a highly transitive self-similar action through a proper infinite-index self-embedding (not excluded; Hull–Osin gives HT actions of Kazhdan hyperbolic groups).
