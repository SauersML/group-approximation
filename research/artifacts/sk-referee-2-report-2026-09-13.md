# sk-referee-2: referee report on the simple Kazhdan sofic group note (2026-09-13)

- Manuscript: `simple_kazhdan_sofic_group.tex`.
- Frozen copy: `manuscript-disk-1646.tex` in the SK campaign directory (md5 7b3dc4ec92b4581553bc0dc2b0edcb99, 340 lines). All line numbers below refer to it.
- Scope (brief sk-referee-2):
  - the finite models (l.118-152);
  - the definition of LEF and the deduction of sofic and hyperlinear;
  - the word-problem corollary (l.229-262).
- I also read the rest once; two remarks outside scope are at the end.
- Every fix is a verbatim before/after pair in `research/artifacts/sk-referee-2-proposal-2026-09-13.md`.

## Verdict
- ERROR: none.
- GAP: none.
- UNCLEAR: 5 (U1-U5).
- FREE SIMPLIFICATION: 1 (S1).
- CITATION: 2. C1 pins a correct citation, checked against the source. C2 adds credit for the notion of LEF.

The finite-model section and the corollary are correct as mathematics. The fixes remove places where a careful reader has to reconstruct a convention or a choice.

## 1. Periodic words (l.123-129)
**Claim.** For each k there is a periodic y with the same words of length 2k+1 as X, and N can be arbitrarily large.

**Check.**
- Minimality gives L such that every word of length L of X contains every word of length 2k+1 of X.
- Uniform recurrence gives, in a point x ∈ X, positions p < q with q−p ≥ L (as large as we like) and x_p⋯x_{p+2k−1} = x_q⋯x_{q+2k−1}.
- Put w = x_p⋯x_{q−1}, N = q−p, and y_n = w_{n mod N}.
- A window y_i⋯y_{i+2k} with 0 ≤ i < N equals x_{p+i}⋯x_{p+i+2k}, because y_{N+j} = w_j = x_{p+j} = x_{q+j} for 0 ≤ j < 2k.
- So every (2k+1)-word of y occurs in X, and w contains every (2k+1)-word of X. TRUE.

**U1 (wording).** "two occurrences of the same word of length 2k, separated by a segment w" can be read with w as the gap strictly between the two occurrences. Under that reading the join w_{N−1}w_0 of y = ⋯www⋯ need not occur in X, and the claim fails. The argument needs w to run from the start of the first occurrence to the start of the second. Proposal P1 states this choice explicitly at the same length.

## 2. The ring model (l.131-144)
**U2 (convention).** The text says only "evaluate its local table along y". The relation at l.140 holds for exactly one indexing:
- If f(x) = φ(x_{−ρ}⋯x_ρ), put D_y(f)δ_n = φ(y_{n−ρ}⋯y_{n+ρ})δ_n.
- With Pδ_n = δ_{n+1}: P^i D_y(f) P^{−i} δ_n = φ(y_{n−i−ρ}⋯y_{n−i+ρ}) δ_n.
- Since (Tx)_n = x_{n+1}, (f∘T^{−i})(x) = φ(x_{−i−ρ}⋯x_{−i+ρ}). So the right side is D_y(f∘T^{−i})δ_n, matching ufu^{−1} = f∘T^{−1}.
- The mirror indexing φ(y_{−n−ρ}⋯y_{−n+ρ}) gives D_y(f∘T^{i}) and breaks the relation.

Proposal P2 writes the formula at the same length.

**Checks of the listed claims (all TRUE):**
- **Well defined.** φ is determined by f only on words of X, and windows of y of radius ρ ≤ k are words of X.
- **Products.** (fu^i)(gu^j) = f·(g∘T^{−i})u^{i+j} ↦ D_y(f)D_y(g∘T^{−i})P^{i+j} = D_y(f)P^iD_y(g)P^j. This needs k ≥ ρ_g + |i|, which "including those shifted in the products" covers. Sums are immediate.
- **Nonzero coefficients.** If f ≠ 0 has radius ≤ k, then φ(v) = 1 for some word v of X, and v occurs in y.
- **Injectivity.** Suppose every listed element has exponents in [−J, J] and N > 2J.
  - Distinct exponents are distinct mod N.
  - The matrices D_y(f_j)P^j then sit on disjoint cyclic diagonals.
  - So Φ(r) = 0 forces D_y(f_j) = 0, hence f_j = 0, for every j.
  - "twice the largest absolute exponent" is the right bound.

## 3. Group models (l.146-149)
- **U3 (invertibility).** Φ(g) ∈ GL_{3N}(F_2) needs Φ(g)Φ(g^{−1}) = Φ(I_3) = I_{3N}. So the products for gg^{−1} must be among the listed operations. The text lists "the entries of ... their inverses" and "all intermediate sums and products needed for matrix multiplication" without saying which multiplications. TRUE once gg^{−1} is included; proposal P3 says so.
- **Partial homomorphism.** For g, h, gh ∈ F, the listed products g_{il}h_{lj} and their sums give Φ(gh) = Φ(g)Φ(h). TRUE.
- **Injective on F.** The entries of the differences g−h are listed. TRUE.
- **Definition of LEF (l.119-120).** It agrees with Vershik–Gordon as Pestov quotes it (§4 below). TRUE.

## 4. Sofic and hyperlinear (l.150-152)
Checked against arXiv:0804.3968v8 (4 Aug 2008), fetched and converted with pdftotext on MSI:
- p. 12: "So is every LEF group G in the sense of Vershik and Gordon [75], defined by the property that one can embed every finite F ⊆ G into a suitable finite group so as to preserve the partial multiplication." The preceding sentences define initially subamenable groups.
- p. 12: "Example 4.5. Every initially subamenable group is sofic."
- p. 7: "Theorem 3.3 (Elek and Szabó [26]). Every sofic group is hyperlinear."
- p. 7, just before it: "the restriction of the normalized Hilbert-Schmidt distance to S_n is not, in fact, even Lipschitz equivalent to the normalized Hamming distance."

So the deduction is correct and \cite{Pestov} is the right source.
- **C1.** "their permutation matrices give hyperlinear models" presents Theorem 3.3 as immediate, while Pestov warns the comparison of distances is not Lipschitz. Proposal P3 pins the two statements instead, which is shorter and exact. I did not check the journal numbering (BSL 14 (2008)) against the print; that belongs to sk-citations.
- **C2.** The title theorem uses LEF, but the note never credits Vershik–Gordon for the notion. Proposal P4.

## 5. The corollary (l.229-262)
**Upper bound (l.240-242).**
- Multiply the word out formally in LC(A^Z,F_2)⋊Z.
- Restriction LC(A^Z) → LC(X) is a T-equivariant surjection, so this ring maps onto R.
- The word equals I_3 iff each coefficient of (word − I_3) vanishes on X, i.e. its local table vanishes on the words of L(X) of that window length.
- These are finitely many queries, fixed in advance, so WP ≤_tt L(X). TRUE.

**U4.** "allowed windows" is not defined anywhere in the note (it also appears at l.142), and the domain of the computation is left to the reader. Proposal P5.

**Lower bound (l.242-249).**
- u^{−t}e_a u^t = e_{T^{−t}[x_0=a]} = e_{[x_t=a]}, so the product is the indicator of the cylinder at 0..n−1.
- e_12 of a product of ring generators is an iterated commutator by (eq:elementary), alternating the third index recursively.
- The word is 1 iff the cylinder is empty iff v ∉ L(X), so L(X) ≤_m complement of WP. TRUE.

**Sturmian facts (l.251-256).** Convention: x_t = 1_{[1−α,1)}(θ + tα mod 1), θ ∈ [0,1).
- **The language is computable from α.**
  - Letter t is 1 iff θ ∈ [−(t+1)α, −tα) mod 1.
  - The n+1 distinct points −jα mod 1 (0 ≤ j ≤ n) cut the circle into n+1 arcs, one word per arc, determined by the cyclic order of the labelled points.
  - The cyclic order is computable from α, with no ties because α is irrational.
  - So L(X_α) ≤_T α. TRUE.
- **The language computes α.**
  - 1_{[1−α,1)}(θ+tα mod 1) = ⌊θ+(t+1)α⌋ − ⌊θ+tα⌋, so a word of length n has ⌊θ+nα⌋ ones for θ ∈ [0,1).
  - The minimum is ⌊nα⌋, attained at θ = 0; closure points add no new words.
  - For integers p and n ≥ 1, p/n < α iff p ≤ ⌊nα⌋. So L(X_α) computes the Dedekind cut of α, which for irrational α is Turing equivalent to α. TRUE.

**U5.** The endpoints −jα, 0 ≤ j ≤ n, presuppose the convention 1_{[1−α,1)}, which the note never states. The note does not define X_α either. With the convention 1_{[0,α)} the endpoints are −jα, −1 ≤ j ≤ n−1, a rotation of the same configuration, so the statement survives, but the reader has to reconstruct all this. Proposal P6 adds the definition in two lines.

**Irrational representatives (l.257-260).**
- √2−1 is computable and irrational.
- For a noncomputable S, α_S = Σ_{i∈S} 2^{−i−1} has binary expansion χ_S, which is not eventually periodic. So α_S is irrational, lies in (0,1), and α_S ≡_T S.
- TRUE.

**S1.** Interleaving the characteristic sequence with 1's adds nothing; proposal P7 at the same length.

**Isomorphism invariance of the word-problem degree, and "continuum many" (l.260-261).** TRUE. There are at most continuum many f.g. groups, so the count is exactly continuum.

## 6. Outside scope (for sk-referee-1)
- l.180: C ∩ T^jC = ∅ for 0 < |j| ≤ 2w+2 already suffices. The levels have |a| ≤ m = w+1, s ∈ B_1(U) ⊆ B_m(U), and the products E_{ab}E_{cd} need |b−c| ≤ 2m. The bound 2w+3 is harmless slack.
- On one reading I found no error in l.67-117 or l.154-227. I did not referee those lines to the standard of this report.

## 7. Not checked here
- The journal numbering of Pestov (BSL 14 (2008)) against arXiv v8.
- Morse–Hedlund 1940 as the source of the Sturmian facts.
- The Vershik–Gordon bibliographic data. Both the second and third items belong to sk-citations.
