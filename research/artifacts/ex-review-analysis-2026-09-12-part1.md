# EX review, analysis lanes, part 1: the class-three root (2026-09-12)

Lane `ex-verify-analysis`. Priority review requested by main. Landings `4edaed478a`, `003ca49dfc`,
`a7e18e225c`, `081b0e3017` and `2b5e6d8ce8`, all by ex-unitary-class-three. Verdict legend as in
`ex-review-analysis-2026-09-12.md` §0.

Source read for this review: A. S. Toms, "A simple C*-algebra which is not K1-injective",
arXiv:2609.09535v1. It is an unrefereed preprint. I read pp. 5--22 of the PDF, from the copy in the
ex-k1-properly-infinite lane directory.

## 1.2 `simple-ah-algebra-with-class-three-component-group` and the root: PASS

The root is `simple-cstar-unitary-components-class-three`. It is established only through
well-formed routes:
- `class-three-via-spin-bordism-trapping-tower` requires `simple-ah-algebra-with-class-three-component-group`.
- That claim's route `simple-ah-class-three-trapping-tower-proof` requires three claims:
  - `toms-trapped-spin-bordism-class`, through its citation route (`requires: []`);
  - `trapped-spin-bordism-class-over-any-spin-seed-factor`, whose proof requires the Toms import;
  - `eta-squared-commutator-has-nonzero-spin-bordism-class`, whose Arf proof requires
    `u2-triple-samelson-class-three-stage`. That claim's proof requires
    `samelson-circle-sphere-product-has-order-n`, which has a proof route with `requires: []`.
- None of the five landings adds a `requires: []` route other than the citation route.
- The dead route `class-three-via-equal-dimension-towers` stays invalidated.
- All ids are at most 53 characters.

### Item 1. Toms's detector, recursion and limit lemmas, and the S^4 claim: PASS

I went through each use of the seed factor and of simple connectivity in Toms.

- **Lemma 3.1 (pp. 9--10).** The normal bundle of the block-diagonal subbundle is identified with
  π*W_R by `z ↦ g X_z`, which is left translation. So the normal spin structure is a pure pullback
  of the structure on W_R. No adjoint twist enters, and the parity of `r` is irrelevant.
- **(13), p. 10.** Simple connectivity of B is used only to make the spin structures on TB and W_R
  unique. Toms says so in the text: "Simple connectivity of B gives uniqueness of the initial spin
  structures on TB and W_R, not uniqueness of all spin structures on Z(v)."
  - For B = M × X, W is pulled back from the simply connected X, so its structure is still
    unique on X, and the lane pulls it back.
  - TB gets σ_M × σ_X for a fixed σ_M. This is a choice, not a uniqueness statement, and nothing
    later uses uniqueness.
- **Definition 3.2 and Theorem 3.3, with proof (pp. 11--12).** The bordism `𝒵 = V^{-1}([0,1] × D(E))`,
  the collar compatibility (Lemma 2.3) and the extension of the protected map all hold in every
  dimension. For m = 5 the locus is a 5-manifold, and the bordism is 6-dimensional.
  - The constant-map subtraction is still needed.
  - Toms (6) gives `Ω̃^Spin_5(S^3) ≅ Ω^Spin_2(pt)`, and (8) is the regular-preimage description.
- **Lemma 4.1 and Proposition 4.2, with proofs (pp. 13--15).** The only S^4-specific step is on p. 15:
  "For either orientation, S^4 has a unique spin structure."
  - The lane replaces it with constancy. On M × {ξ}, the ambient structure is σ_M ⊕ (σ_X at ξ), and
    the normal structure is W's structure at ξ, transported by the constant isomorphism
    `ε D_ξ s : T_ξ X → W_ξ`.
  - Two spin structures on a trivial bundle over M that are both pulled back from a point agree up
    to orientation, since H^1(pt; Z/2) = 0. So each copy carries ±σ_M. I re-derived this.
  - Signs do not matter in Z/2, and in general they give the Euler number `<c_r(Q)^2, [X]>` by (19).
- **Lemma 5.1(iii), Proposition 5.2 and Construction 5.3 (pp. 16--18).** These concern only X_i and
  Q_i, for arbitrary m_i. I rechecked the numbers:
  - `r_{i+1} = r_i + 2 m_i N_i` and `dim X_{i+1} = 4 r_i + 8 m_i N_i = 4 r_{i+1}`;
  - the top Chern class is multiplicative, so `<c_{r_{i+1}}(Q_{i+1})^2, [X_{i+1}]> = 1 · 1`.
- **Section 6.1 (35).** The coordinate projections "preserve the S^4 coordinate". With T^2 × S^3 in its
  place, the 1/i-density construction still works; it only needs the projections to be surjective.
- **Lemma 6.2** uses connectedness of U(V_{i,l}). **Proposition 6.4** uses density and the fact that a
  section nonzero in every fibre of Γ(End E) is full. Neither uses S^4.
- **Lemma 7.1, with proof (p. 22).** Polar approximation at a common stage. It is general.
- **Proposition 6.5** (K_1(A_i) = 0 from even cells) does *not* transfer, because T^2 × S^3 has odd
  cells. The lane correctly does not claim K_1(A), and gets [w]_1 = 0 from w being a commutator.

The lane's Proposition 6.1 matches Toms's proof of Proposition 6.4. Its Lemmas 5.1 and 5.2 match
Lemma 6.2 and the finite-stage detection.

### Item 2. The η² seed and the Euler multiplier: PASS

- `c = [α(s_2), [α(s_1), ω(z)]]` is 1 on the fat wedge, so it factors through S^5.
- Write `h(s,x) = [α(s), x]`. Naturality gives `c̄ = h ∘ Σh` up to the order of the two circle
  factors. That order changes a sign, which η² ignores.
  - `u2-triple-samelson-class-three-stage` gives `h = ω ∘ η_3`. It is established through
    `samelson-circle-sphere-product-has-order-n`, which has a `requires: []` proof.
  - Hence `[c̄] = η_3 ∘ η_4`, the generator of π_5(S^3) = Z/2.
- **The preimage.** Let y ≠ 1 be a regular value and L = c^{-1}(y). Then L is compact and lies in the
  open cell (S^1∖1) × (S^1∖1) × (S^3∖1) ≅ R^5.
  - This cell is contractible, so every spin structure on T^2 × S^3 restricts to the unique one
    there. So L carries the spin structure induced by its framing alone, and the verdict does not
    depend on σ_M.
- **Stabilization.** For n = 3, k = 2 = n − 1, Freudenthal gives a surjection π_5(S^3) → π_2^s. Both
  groups are Z/2, so the stable class is η².
- **Detection.** The Lie-framed torus represents η². Its induced structure is the product of two
  nonbounding circles (Toms Lemma 2.6).
  - Its quadratic form is 1 on a, b and a + b, since `q(a+b) = q(a) + q(b) + a·b = 1`.
  - So the Arf invariant is 1, and the class is nonzero in Ω^Spin_2.
- **Euler multiplier at every stage.** `<c_{r_i}(Q_i)^2, [X_i]> = 1` by Toms (31) and (32), which
  depend only on the X_i and Q_i. So ν^M(w_i) = η²-class ≠ 0 = ν^M(1) at every i.

### Item 3. The witness: PASS

- **w ∉ U_0(A).** Some φ_{1,j}(w_1) would lie in U_0(A_j) by Lemma 7.1. It is homotopic to w_j, and
  that contradicts Lemma 5.2.
- **Order two.** 2[c̄] = 0 in π_5, and pointwise multiplication realizes the group law, so c² ≃ 1.
  Hence w² ∈ U_0. Together with w ∉ U_0, the order is exactly two.
- **K_1 class.** [w]_1 = 0 because K_1 is abelian and w is a commutator.
- **M_2.** diag(x, x*) ∈ U_0, so diag(x,1) ≡ diag(1,x) mod U_0, and so the classes of diag(x,1) and
  diag(y,1) commute. Hence diag(w,1) ∈ U_0(M_2(A)).
- **Stable finiteness.** A tracial state exists as an inverse limit, and it is faithful by simplicity.

### Item 4. The citation route quotes Toms verbatim: PASS, one paraphrase

Checked against the PDF:
- Setting, p. 9. ✓
- Definition 3.2, p. 11. ✓
- Theorem 3.3, p. 11. ✓
- Proposition 4.2 with (20), p. 14. ✓
- Lemma 5.1(iii) (24), p. 16. ✓
- Proposition 5.2 (30) and (31), pp. 17--18. ✓
- Lemma 7.1, p. 21. ✓

Lemma 6.3 (p. 20) appears in the route as a faithful paraphrase, not in quotation marks. The Part 1
artifact quotes it verbatim, and that quote matches.

### Item 5. The excess bound and the class-four finite stage: PASS

**`block-component-group-class-at-most-excess-plus-two`: PASS, re-derived.**
- **Filtration.** F_k is the kernel of restriction to X^{(k−1)}. F_1 is everything, since U(r) is
  connected, and F_{d+1} = 1. Homotopy extension gives representatives identically 1 on X^{(k−1)}.
- **Centrality.** [Π, F_k] ⊆ F_{k+1}.
  - Shrink the support of n into interior balls of the k-cells, rel X^{(k−1)}.
  - On each ball, deform g to its central value.
  - Conjugation by a constant of the connected group U(r) is homotopic to the identity rel the
    boundary.
- **Depth.** γ_2 ⊆ ker(Π → K^1(X)). In the stable range dim < 2r, Π(E|X^{(2r−1)}) ≅ K^1(X^{(2r−1)}),
  so naturality gives γ_2 ⊆ F_{2r}.
- **Count.** γ_c ⊆ F_{2r+c−2}, which is trivial once c ≥ d − 2r + 3.
- **Limits.** Π(A) = lim Π(A_i): surjectivity by polar approximation, injectivity modulo U_0 by Lemma
  7.1. γ_c commutes with direct limits.
- **Consistency with the trapping tower.** Its excess is 2r_i + 1, which is unbounded, as required.

**`u2-quadruple-samelson-class-four-stage`: PASS, one notation note.**
- **Lower bound.** One more naturality step gives ω∘η_3∘η_4∘η_5. The collapse is detected through
  the retraction of {1} × Y ⊂ S^1 × Y and the suspension splitting of the product.
- **Upper bound.** d = 6 and r = 2, so the excess bound gives class at most four.
- **Nonvanishing.** η_3³ ≠ 0 does not need Toda's theorem number. It suspends to η³ = 12ν ≠ 0 in
  π_3^s = Z/24, so it is the unique element of order two in π_6(S^3) ≅ Z/12.
- **Notation.** Toda's ν′ generates the 2-primary Z/4, so the element the lane writes "6ν′" is 2ν′
  in that notation. It is the same element, so no statement changes.
- **η_3^4 = 0.** η_6 is a suspension, so (6ν′)∘η_6 = 6(ν′∘η_6) = 0, since ν′∘η_6 has order two.

**`simple-cstar-unitary-components-class-four`: OPEN, correctly.** Its "blind detector" attempt
shows only that ν^M vanishes, and it says that silence proves nothing about U_0.

## Notes, no verdict change

- **Trust surface.** This rests on Toms's unrefereed preprint, but every step used was re-read on pp.
  5--22 and re-derived here. I did not re-read pp. 1--4 (Lemma 2.2 and the spin conventions (1) and
  (2)), and the lane does not use Lemma 2.2. Proposition 2.8 was read in statement only, with the end
  of its proof on p. 9.
- **Scope.** The root is a question built in this repository, from the stw59 lane. It is not an
  externally posed named problem.
- **Wording.** `toms-trapped-spin-bordism-class` says the "upper-left block gives f_v". Precisely,
  f_v = ρ ∘ a_v with the retraction ρ of Toms (15). For the witness, det c = 1, so ρ acts trivially.
