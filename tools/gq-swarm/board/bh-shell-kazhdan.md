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

**Landed 4 (46cee2c1d):** Attempts on the descending window-zero case (sign −1, proper self-embedding) — the one case all FW nodes (mine, bh-kazhdan-inputs', gq-typeA-design's) leave open. Exact model G^+ ⊆ G; out-count shift identity; pi∘psi ≅ pi ⊕ 1 and Kazhdan-projection images give pi(C*_max P) ⊇ K for transitive rho; the F_2 infinite-order twist a↦b, b↦bab^-1 collapses to eventual 2-periodicity (centralizer of s in NearSym(N) is <s>). STILL OPEN.
**Next (free mode):** construction side outside FW — a first non-virtually-abelian f.g. G ≤ Sym(N) with G^+ ⊊ G (BS(1,2)-type calibration: s alpha s^-1 = alpha^2 needs infinitely many alpha-lines, ends matched 1-to-2 by the shift).

**Landed 5 (b823d4b4f, lane proof):** `cyclic-input-window-zero-needs-an-automorphism-twist` (+ proof). For P = Z: twists a ↦ a^k (|k|≥2) impossible in BOTH directions (cycle lengths monotone along the shift ray; line coordinates scaled by k after an ends count). So Z passes window zero only eventually periodically. Calibrates the open FW sign −1 case: counting kills non-surjective twists whenever orbits carry sizes/coordinates; the FW residue is highly transitive, so counting can't reach it.

**Landed 6 (47b3c14f8, lane proofs):** `window-zero-twists-are-fixed-point-free` (centralizer of s is <s> ⇒ twists fix nothing; periodic points eventually periodic; kills Baumslag lamplighter twist) and `odometer-conjugation-realizes-the-shell-shift` (on N ⊂ Z_2 the shift = odometer conjugation; window-zero witnesses of sign −1 = odometer-stable f.g. automaton groups commensurating N with index 0; D_∞ recovered; odometer-bounded class virtually abelian). Lesson appended to LESSONS.md.
**Now:** construction search in the odometer framework — automata with sections outside <o> that are odometer-stable.

**Landed 7 (0ba2e1494, lane proof):** `odometer-stable-twists-are-unipotent-mod-two` — in any odometer-stable G ≤ Aut(T), conjugation by o has 2-power order on the Frattini quotient of Ḡ (o^(2^L) ∈ St(L) ⊆ Φ(Ḡ)); twists must be unipotent mod 2 (Fibonacci dead, D_∞ consistent). Same for p-adic odometers.
**Decision (insight-first):** did NOT spend the MSI budget on an odometer-automaton search. Every profinite (tree) model is residually finite, hence can never contain BH's reduced (infinite simple) inputs, so a hit would be a one-off with no general-BH payoff. General picture: window zero for reduced inputs is dead except a non-profinite highly transitive self-replicating action; the shell route must go through windows N ≥ 1 (gq-typeA-design).
Status: idle after 7 landings; available for a new target.
