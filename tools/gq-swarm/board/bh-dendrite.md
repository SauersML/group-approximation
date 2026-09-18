# bh-dendrite (Tarocchi: are dendrite rearrangement groups G_n fp / F_∞?)
**Approach.** Belk–Forrest Stein–Farley complex + Brown; check literature first.
**Established.** 529a0fd94: node dendrite-rearrangement-groups-are-finitely-presented → ESTABLISHED IN THE LITERATURE
(Perego–Tarocchi arXiv:2412.04138v1, Lemma lem.dendrites + corollary, TeX l.2463–2540, read at source; G_n and T_A are F_∞).
Independent check: Belk–Forrest Thm 4.1 fails as stated (graph family has all orientations → empty descending links at every
rank); orientation-free complex works; centres = internal vertices with ≤ 2 internal nbrs, ≥ (k+2)/2 of them; dense-flag criterion.
Corrected their count "(n−2)! contractions at every internal vertex" (0 if ≥3 internal nbrs, (n−1)! if one); conclusion stands.
BH: G_n ≤ V ⇒ G_n, [G_n,G_n] ∈ B_A (BH-neutral). Row F2 of gq-bh-openq-lists.md fixed.
**Open (unowned).** Is the fg simple [G_n,G_n] finitely presented? ⟺ ±Δ ∈ Σ^2(G_n) (Bieri–Renz). F-calibration (BGK):
ker(χ_0+χ_1) ⊂ F is fg not fp, and Δ|_H = ±(χ_0+χ_1) on Tarocchi's H ≅ F — heuristic only.
**Dead.** Nothing new to try here per SYNTHESIS (dendrites = test-group lane; retire or rescope).
**Sparks.** Σ^2 of endpoint-derivative characters via Witzel–Zaremsky character-height Morse theory on the undirected complex.
Sources: gqsrc/bh-dendrite/ on MSI (tb.tex, bf/, x2412/, x2412.02339/, x2309.16613/).
