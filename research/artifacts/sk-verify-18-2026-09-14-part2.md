# sk-verify-18 part 2: review of the comb-stage RFD claim (2026-09-14)

Lane sk-verify-18, independent verifier for wave 12. Queue line 1 of `$SK2/queue/verify.txt`:
- claim `comb-tooth-tree-stages-are-residually-finite-dimensional` (sk-rfd-amalgam, 8ae79a74a1);
- route `comb-tooth-tree-stages-rfd-via-li-shen`;
- imports `li-shen-amalgamated-rfd-criterion` and `exel-loring-free-products-of-rfd-algebras-are-rfd`.

## Verdict
- **Claim and route:** PASS, re-derived by hand. Optional wording fixes W1–W3 add 0 lines.
- **Import `li-shen-amalgamated-rfd-criterion`:** PASS at source.
- **Import `exel-loring-free-products-of-rfd-algebras-are-rfd`:** PASS on two independent printed restatements read at source. The primary 1992 paper was not opened.

## Sources read (2026-09-14)
- **Li–Shen journal PDF:** Q. Li, J. Shen, *A note on unital full amalgamated free products of RFD C∗-algebras*, Illinois J. Math. 56 (2012), no. 2, 647–659, doi 10.1215/ijm/1385129969 (Crossref-confirmed). Read pp. 649, 650, 657, 658.
- **Li–Shen arXiv preprint:** *Unital Full Amalgamated Free Products of MF Algebras*, arXiv:1006.2447, `main.tex` l.84–145 on MSI. Theorem 4.1 is the same criterion, stated for unital RFD factors.
- **Armstrong–Dykema–Exel–Li**, arXiv:math/0210448, `main.tex` l.728–800 and bibitem EL, on MSI.
- **Printed secondary use:** Shulman et al., *The MF property for amalgamated free products*, arXiv:2603.13564, l.534. Compatible embeddings j_1∘θ_1 = j_2∘θ_2 into ∏M_n over a finite-dimensional C*(H), "by [LiShenRFD] … RFD". This is the same shape of application.

## Import checks
**Li–Shen Theorem 2 (p. 657), verbatim as printed.**
- Statement: "Let 𝒜, ℬ be separable unital C*-algebras and 𝒟 be a finite-dimensional C*-algebra. Suppose ψ_𝒜: 𝒟 → 𝒜 and ψ_ℬ: 𝒟 → ℬ are unital embeddings. Then 𝒜 ∗_𝒟 ℬ is RFD if and only if there are unital embeddings q_1: 𝒜 → ∏_{n=1}^∞ ℳ_{k_n}(ℂ) and q_2: ℬ → ∏_{n=1}^∞ ℳ_{k_n}(ℂ) for a sequence {k_n} of integers such that the following diagram commutes".
- The square is q_1∘ψ_𝒜 = q_2∘ψ_ℬ.
- The proof on p. 658 reduces through Lemma 6 (Brown–Dykema Lemma 2.2) to the abelian amalgam PDP and Proposition 2.
- The node and its citation route match exactly: the full product ∏, exact equality on 𝒟, separable unital factors.

**Li–Shen Example 1 (p. 650).**
- 𝒟 = ℂ⊕ℂ with φ_1(1⊕0) = diag(1,0) in M_2 and φ_2(1⊕0) = diag(1,0,0) in M_3. Then M_2 ∗_𝒟 M_3 "is not MF algebra (therefore it is not RFD or quasidiagonal)", since a tracial state would give τ(φ_1(1⊕0)) = 1/2 ≠ 1/3.
- The route's model test matches. Remark 2 (p. 650, ADEL) also matches the citation route.

**Exel–Loring.**
- Li–Shen p. 649, verbatim: "Lemma 1 (Theorem 3.2, [8]). Suppose 𝒜_1 and 𝒜_2 are unital C*-algebras. Then the unital full free product 𝒜 = 𝒜_1 ∗_ℂ 𝒜_2 is RFD if and only if 𝒜_1 and 𝒜_2 are both RFD." Reference [8] is Exel–Loring, Internat. J. Math. 3 (1992), 469–476.
- ADEL l.735–739 confirms independently: "Exel and Loring proved that the full free product of any two r.f.d. C*-algebras A and B with amalgamation over either the zero C*-algebra or over the scalar multiples of the identity (if A and B are unital) is r.f.d."
- The "only if" half is elementary: each factor sits inside the free product as a C*-subalgebra, and RFD passes to C*-subalgebras.

## Re-derivation of the route
**Setup.** V = U⊕M_d with e = (0,1). ψ_V(x,y) = x(1−e) + ye and ψ_{M_r}(x,y) = x(1−p) + yp, with p rank one. Both are unital embeddings exactly when U ≠ 0, d ≥ 1 and r ≥ 2. For r = 1 the map is not injective, as stated.

**Step 1 (hypotheses of Theorem 2).**
- U separable and RFD gives a countable separating family of nonzero unital finite-dimensional representations ρ_n: U → M_{D_n}:
  - for a dense sequence x_i and each k, pick a finite-dimensional σ with ‖σ(x_i)‖ ≥ ‖x_i‖ − 1/k;
  - compress to σ(1)H, which keeps the norms and makes it unital;
  - the countable family is isometric on a dense set, hence faithful.
- **Multiplicity bookkeeping:**
  - k_n = r·d·D_n;
  - q_1(u,m)_n = ρ_n(u)^{⊕(r−1)d} ⊕ (m⊗1_{D_n}) has size (r−1)dD_n + dD_n = k_n;
  - q_1(e)_n has rank dD_n, and q_1(1−e)_n has rank (r−1)dD_n;
  - q_1 is unital, a *-homomorphism, bounded (contractive), and injective (u = 0 from separation, m = 0 from m⊗1 = 0);
  - p⊗1_{dD_n} has rank dD_n and (1−p)⊗1 has rank (r−1)dD_n, with the same total k_n.
- A unitary W_n exists that carries these two ranges onto the second and first summands. Then q_2 = W_n(·⊗1)W_n^* is unital and injective, since M_r is simple and each coordinate is nonzero.
- So q_1∘ψ_V = q_2∘ψ_{M_r} coordinatewise, and V, M_r are separable and unital. Every hypothesis of Li–Shen Theorem 2 holds, so V ∗_{ℂ²} M_r is RFD.

**Step 2 (free unitary).** C(𝕋) is commutative, and point evaluations separate points, so it is RFD. By Exel–Loring (Li–Shen Lemma 1), (V ∗_{ℂ²} M_r) ∗_ℂ C(𝕋) is RFD. It is separable and unital, so the induction runs.

**Step 3 (rank ratio).**
- For a finite-dimensional representation π of U⁺, restrict to M_r on π(1)H. Every unital representation of M_r is a multiple of the standard one, so rank π(p) = m and rank π(1−p) = (r−1)m.
- Since e = p in the amalgamated product, rank π(e) : rank π(1)−π(e) = 1 : r−1.

**Step 4 (extension).**
- Let σ be a unital finite-dimensional representation of V with dim σ(1−e)H = (r−1)m, where m = dim σ(e)H.
- Split σ(1−e)H into r−1 blocks of dimension m. Partial isometries between the blocks and σ(e)H give a unital τ: M_r → B(H) with τ(p) = σ(e).
- The universal property of the full amalgamated free product then gives a representation of V ∗_{ℂ²} M_r. Any unitary on H extends it to U⁺.
- Conversely, Step 3 forces the dimension condition.

**Model tests re-checked.**
- U = ℂ, d = 1, r = 2: ψ_V is an isomorphism ℂ² ≅ V, so V ∗_{ℂ²} M_2 ≅ M_2 by the universal property, which is RFD.
- Li–Shen Example 1: the forced ratios 1:1 from M_2 and 1:2 from M_3 are incompatible, so there is no trace and no finite-dimensional representation. In the comb stage the two summands of U⊕M_d carry independent multiplicities, so the ratio 1 : r−1 is reachable, and Step 1 realizes it.

## Optional fixes (0 lines, no statement change)
- **W1:** in claim items 2–3 and route Steps 4–5, say "unital" (or "nonzero") finite-dimensional representation, or read 1−e as σ(1)−σ(e). For the zero representation the ratio is 0:0.
- **W2:** in route Step 1, add one clause saying why a separable RFD algebra has a countable separating family of unital finite-dimensional representations (dense sequence, norming representations, compress to σ(1)H).
- **W3:** in the Exel–Loring citation route, record the second independent restatement (ADEL arXiv:math/0210448, l.735–739) and the Li–Shen arXiv preprint (1006.2447, Theorem 4.1, l.118–139). The primary Exel–Loring paper is still unopened.

## Scope
This settles only missing input 1 of `weakly-dense-popa-combs-exist-in-property-t-factors`. Inputs 2 and 3, and the Popa clause of Brown's Question 3 for property (T) factors, stay OPEN, as the claim says. No priority is claimed; the step is a citation-level application of Li–Shen.
