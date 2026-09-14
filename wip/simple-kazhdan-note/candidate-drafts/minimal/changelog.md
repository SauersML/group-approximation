# sk-draft-minimal: changelog against main (revision 1, 5b1890ce6c, md5 8e04b341…)

Architecture: theorem, proof, one corollary (word problems), at most 3 pages. The draft is `sk/drafts/sk-draft-minimal/minimal.tex`.

1. **Intro.** Deleted "The following construction answers all three forms positively." The abstract and the theorem already say it.
2. **Theorem.** The EL_n clause moves out of the statement into one sentence after the proof. The proof remark "We write the proof for n=3 …" is deleted. The theorem is unchanged; only the placement moves.
3. **Intro, simplicity sentence.** "a finite simple group GL_d(F_2) acting on a clopen tower" becomes "a copy of the finite simple group GL_d(F_2) over a clopen tower". This is wording only.
4. **Ring paragraph.** The display of R is inlined. Same content.
5. **Finite models.** "every word of X occurs in x" becomes "occurs in x_{[0,∞)}", because the recurrence argument uses the forward half.
6. **Simplicity.**
   - ε_ab = u^a e_V u^{-b} (sk-arbitrary A2, PASS in sk-review-1 part 7). This gives the one-line product rule e_V u^c e_V = e_V e_{T^cV} u^c = 0 for 0<|c|≤2w.
   - The product formula is inline: f u^a e_V f' u^b = u^a (f∘T^a) e_V f' u^b ∈ {0, ε_{a,-b}}.
   - Last paragraph: the level ideal J and its Stepanov citation are replaced by two commutators, e_pl(re_V) = [e_pq(r), e_ql(e_V)] and e_pq(re_Vs) = [e_pl(re_V), e_lq(s)], plus the covering identity (sk-simplicity-short-b, PASS in sk-review-1 part 3). The Stepanov bibitem is deleted.
7. **New paragraph after the proof.** Brown's printed formulation: L(G) ⊂ R^ω (Ozawa Prop. 7.1), G is ICC, and G sits in the unitary group of the McDuff factor L(G)⊗̄R, which embeds in R^ω. Source: sk-operator-algebras Option A; node `brown-mcduff-witness-for-simple-kazhdan-lef-group` PASS in sk-review-2 part 3. The EL_n sentence follows it.
8. **Word problems.** sk-review-2 part 1 §4b repairs:
   - 4.i: restored "There are continuum many degrees". The corollary needs it.
   - 4.ii: "a word for e_12 of the cylinder indicator ∏ u^{-t}e_{v_t}u^t".
9. **Unchanged from main:** abstract, title, MSC, Matui/GM/GMpres/Thom credit, the f.p. sentence and open question, finite models, the Origin paragraph, and the other bibitems.

Main's decisions NOT in this draft, by architecture:
- Option B's Kirchberg/LLP sentence (rev2 item 17): a second consequence costs +8 lines and a bibitem.
- The questions paragraph (item 18): the minimal draft keeps only the one-sentence f.p. question.
- The expanders paragraph (item 6), the RF embedding (item 22), F_q (item 7).
