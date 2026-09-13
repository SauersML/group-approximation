# STW XCV part 1: cheaper witnesses and cheaper proofs (lane x95-alt, 2026-09-13)

Printed question (STW v2 §25, p. 80): if Cu(A) ≅ Cu(B) ≅ Cu(𝒵), must Cu(A ⊗ B) ≅ Cu(𝒵)?
The answer is no. This note checks every candidate witness, and every cheaper proof of the two sides, for the least
Lean theory. Base: review `fz-stw-xcv-review-2026-09-13.md` (ff0a8875e) §2 routes and §5 forced properties.

## 1. What any witness must satisfy (review §5, restated as filters)

Put F = A ⊗ B. Suppose Cu(A) ≅ Cu(B) ≅ Cu(𝒵) = ℕ₀ ⊔ (0,∞].
- F1. A and B are simple, have one functional on Cu, strict comparison and almost divisibility. Unital A has V(A) = ℕ₀,
  so K₀(A) = ℤ is torsion-free with rank one.
- F2. F is simple with a unique trace. A Cu-iso keeps compacts, and V(F) ↪ ℕ₀ gives K₀(F) ↪ ℤ: no ℤ², no torsion
  (landed: `not_injective_intProdInt_*`; x95-obstruction: `grothendieckAddGroup_eq_zero_of_nsmul_eq_zero`).
- F3. The trace cannot see the obstruction, since the K₁⊗K₁ product classes have trace 0. The obstruction has to be
  an index-type invariant.
- F4. K₀(F) ⊇ K₀A⊗K₀B ⊕ K₁A⊗K₁B = ℤ ⊕ K₁A⊗K₁B, so a witness needs K₁A ⊗ K₁B ≠ 0.
  - Any KK-trivial factor fails, including A = 𝒵.
  - K₁ must be nonzero on both sides.

## 2. Candidates ruled out

| candidate | fails at |
|---|---|
| A = 𝒵, or any 𝒵-like KK-trivial B | F4: Cu(𝒵 ⊗ B) ≅ Cu(B) ≅ Cu(𝒵) |
| trace-only obstruction | F3 |
| non-unital or non-separable variants | no gain; the Cu side still needs strict comparison |
| AT/AI limits with K₁ = ℤ, many traces | F1: unique trace forces the same comparison proof |
| mapping out of F to finite-dim algebras | F is simple, so no such maps |
| comparing Cu(A ⊗ B) with Cu(A) directly | circular: needs Cu(A ⊗ B) first |

The survivors are the Bernoulli witness E (review route B), the gcd-d Jiang–Su tower E_d (§3), and a circle
dimension-drop tower (§5).

## 3. Witness E_d: the Jiang–Su tower with gcd d > 1

Building block I_{p,q} = {f ∈ C([0,1], M_p ⊗ M_q) : f(0) ∈ M_p ⊗ 1, f(1) ∈ 1 ⊗ M_q}, the planned `DimDrop (Fin p) (Fin q)`.
Tower: (p,q) ↦ (p k₀, q k₁) with k₀ = 1+q and k₁ = 1+p k₀. This is the jiangsu-lane recursion.
Start at (4,6), so d = 2. The recursion keeps the gcd:
- k₁ is coprime to p k₀, so gcd(p k₀, q k₁) = gcd(p k₀, q).
- k₀ is coprime to q, so this equals gcd(p,q) = d.

### 3.1 Stage invariants (elementary)
- A projection has constant rank r ∈ qℤ ∩ pℤ = (pq/d)ℤ. So V(I_{p,q}) = ℕ₀·e, where rank e = pq/d, [1] = d·e, and
  τ(e) = 1/d.
- K₁(I_{p,q}) ≅ ℤ/d via the det-winding invariant ω. For a unitary u ∈ M_n(I_{p,q}):
  - u(0) = a ⊗ 1_q and u(1) = 1_p ⊗ b.
  - Choose θ_a, θ_b with det a = e^{iθ_a} and det b = e^{iθ_b}.
  - Let W be the continuous lift of arg det u(t) from q θ_a to some value at t = 1.
  - ω(u) = (W − p θ_b)/2π ∈ ℤ. Changing θ_a or θ_b by 2π moves ω by q or p, so ω is well defined in ℤ/d.
- The loop g(t) = diag(e^{2πit}, 1, …, 1) has ω(g) = 1.

### 3.2 Check: the connecting maps act as a unit on ℤ/d (verified by hand)
The jiangsu-lane map sends f to u(t)* diag_j f(ξ_j(t)) u(t), with k = k₀k₁ blocks:
- r₀ = k₁ blocks with ξ = t/2;
- k − k₀ − k₁ blocks with ξ = 1/2;
- r₁ = k₀ blocks with ξ = (1+t)/2.

Where r₀ and r₁ come from:
- At t = 0, the value must have the form x ⊗ 1_{q'}. This needs k₁ | r₀ and q k₁ | k − r₀, which forces r₀ = k₁.
- At t = 1, the value must have the form 1_{p'} ⊗ y. This forces r₁ = k₀.

Push g forward. Conjugation does not change det, so det φg(t) = ∏_j det g(ξ_j(t)).
- The lift rises by (r₀ + r₁)/2 = (k₀ + k₁)/2.
- At t = 0, the −1 eigenvalue of g(1/2) appears k − r₀ = q k₁ = q' times, so x has exactly one −1 and θ_x = π.
- At t = 1, it appears k − r₁ = p k₀² = p' k₀ times, so θ_y = k₀ π.

So ω'(φg) = (k₀ + k₁)/2 − (p' k₀ − q')/2 = 1 + q ≡ 1 (mod d).
- Here the algebra is p' k₀ = p k₀², k₁ = 1 + p k₀ and q' = q + p q k₀.
- So φ_* : ℤ/d → ℤ/d is the identity at every stage.
- By K₁ continuity, K₁(E_d) = ℤ/d and K₁ ⊗ K₁ = ℤ/d ≠ 0 (F4 holds).

### 3.3 Filters for E_d
- F1 holds with the same proofs as for 𝒵. Simplicity, the unique trace (oscillation halving) and comparison in I_{p,q}
  never use coprimality. The only change is the dimension function d_E = d·τ, which puts compacts ↔ ℕ₀.
- F2 fails for E_d ⊗ E_d. Künneth (checked against the literature, not used in Lean) gives
  K₀(E_d ⊗ E_d) = ℤ ⊕ ℤ/d, and torsion contradicts V(F) ↪ ℕ₀.
- F3 holds: the torsion class is invisible to every trace.

## 4. The obstruction for E_d: a ℤ/d class in K₀(E_d ⊗ E_d), without Künneth

### 4.1 Stage level (verified by hand)
Write I = I_{p,q}. Because C([0,1]) is nuclear, I ⊗ I = {f ∈ C([0,1], M_pq ⊗ I) : f(0) ∈ M_p⊗1⊗I, f(1) ∈ 1⊗M_q⊗I}.
- Ideal: J = C₀((0,1), M_pq ⊗ I) = S(M_pq ⊗ I).
- Quotient: M_p⊗I ⊕ M_q⊗I.
- Six-term piece: K₁(I) ⊕ K₁(I) --∂--> K₀(J) ≅ K₁(I) --ι--> K₀(I ⊗ I).
- ∂ is the difference of the two endpoint corner maps, which multiply by q and by p on K₁(I).
- d divides p and q, and d·K₁(I) = 0, so ∂ = 0. Only the vanishing is needed; the signs never enter.
- By exactness at K₀(J), ι is injective. So x = ι[g] satisfies x ≠ 0 (because ω(g) = 1) and d·x = 0 (because d[g] = 0).

### 4.2 Passing to the limit
x must stay nonzero under every (φ ⊗ φ)_*. The stage map φ does not send C₀((0,1)) into C₀((0,1)): the ξ = 1/2 blocks
are nonzero at t = 0. So the six-term sequence cannot be pushed forward along φ ⊗ φ directly. Two sound ways around:
- (a) Exterior product. Identify x = [g] ⊠ [g] under the product K₁ ⊗ K₁ → K₀. This takes one compatibility lemma:
  the product agrees with ι ∘ (suspension iso) on S M_pq ⊗ I. The product is natural for every *-hom, so by §3.2
  (φ⊗φ)_* x = (1+q)² [g'] ⊠ [g'] = x'. And x' ≠ 0 by 4.1 at the next stage.
- (b) Mixed tower. Write E_d ⊗ E_d = lim_m (I_n ⊗ I_m) and let the other factor carry the interval. Then φ_n ⊗ id keeps
  the ideal and six-term naturality applies. id ⊗ φ_m needs the symmetric picture, which (a) supplies.

Conclusion: x_∞ ≠ 0 and d·x_∞ = 0 in K₀(E_d ⊗ E_d). This needs K₀ continuity along a tower (ko-limits item 5)
and ⊗min commuting with the tower limit.

## 5. The circle dimension-drop tower J_{p,q} (dominated)

J_{p,q} = {f ∈ C([0,1], M_pq) : f(0) = f(1) ∈ M_p ⊗ 1_q}.
- Invariants: the six-term boundary is a ↦ qa − qa = 0, so K₀ = ℤ and K₁ = ℤ.
- F1 needs a new comparison theory on circle spectra, with total winding degree ±1 at each stage plus mixing.
  Nothing on the 𝒵 pipeline is reused.
- Obstruction: ℤ² ⊆ K₀, detected by (τ, c₁ over T²). The repo has `CharClass.Bundle` and Chern classes, but no H²(T²),
  degree, or winding API (grep at 8f0f73966: none).
- Verdict: worse than E_d on both sides.

## 6. Bernoulli E with a κ-index obstruction (a cheaper proof, same witness)

F = E ⊗ E = (B ⊗ B) ⋊ ℤ². Take the Toeplitz extensions 0 → A ⊗ 𝒦 → 𝒯(A,α) → A ⋊ ℤ → 0, one for each ℤ.
- Define κ = τ_{B⊗B} ∘ ∂₁ ∘ ∂₂ : K₀(F) → K₁((B⊗B) ⋊ ℤ) → K₀(B ⊗ B) → ℝ.
- κ([1]) = 0, since ∂₂ kills classes that come from the unit.
- κ(Bott(u₁,u₂)) = ±1, since each ∂ sends the implementing unitary to [1].
- Together with τ_F this gives ℤ² ↪ ℝ², hence ℤ² ↪ K₀(F), with no Künneth, no PV exactness and no K₀(B_∞) ≅ ℤ.
- The Cu(E) ≅ Cu(𝒵) side is unchanged: 𝒵-stability of E and a Cu computation for 𝒵-stable monotracial algebras
  (review §3 walls).

## 7. Cost comparison

| route | Cu(A) ≅ Cu(𝒵) | Cu(A⊗A) ≇ Cu(𝒵) | new theory beyond current fleet plans |
|---|---|---|---|
| B (review) | walls: 𝒵-stability of E, Cu of 𝒵-stable algebras | Künneth ℤ² ↪ K₀ | Künneth, PV |
| B + κ (§6) | the same walls | two Toeplitz index maps and a trace | Bott class, index map |
| E_d (§3–4) | the Cu(𝒵) pipeline, run with parameters (p,q) | torsion ℤ/d ↪ K₀ | ω, exterior product, one compatibility lemma |
| J (§5) | new circle comparison | c₁ over T² | degree theory, H²(T²) |

E_d is the only witness whose Cu side costs nothing new. It turns review route B's most expensive half, the Cu(E) walls,
into re-running Cu(𝒵) with parameters.

## 8. Lemma-by-lemma route E_d

- E1 `DimDrop P Q` for arbitrary Fintype P, Q (x95-jiangsu, already general).
- E2 ConnectingMap with k₀ = 1+q and k₁ = 1+p k₀ for any (p,q), with no coprimality hypothesis.
- E3 `CStarTower` started at (4,6); `gcd_step : gcd (p k₀) (q k₁) = gcd p q`.
- E4 Simple and UniqueTrace for the (4,6) tower, the same proofs as for 𝒵 (oscillation halving is parameter-free).
- E5 `IsCuZLike (d · τ)` for Cu(E_d), hence `Cu(E_d) ≃o CuZModel`. This is x95-cuz's recognition theorem, fed the
  stage comparison for I_{p,q}, which does not use coprimality.
- E6 ω : K₁(I_{p,q}) →+ ZMod d with ω[g] = 1, and d·[g] = 0 (elementary homotopy plus Bézout).
- E7 φ_*[g] = (1+q)[g'] (§3.2).
- E8 ι : K₀(S(M_pq ⊗ I)) → K₀(I ⊗ I) is injective, since ∂ = 0 (six-term exactness at K₀(J); ko-k1 SixTermIndex).
- E9 x = [g] ⊠ [g] ≠ 0 with d·x = 0 at every stage, with naturality of ⊠ (ko-bott / ko-tensor).
- E10 K₀ continuity for E_d ⊗ E_d = lim I_n ⊗ I_n (ko-limits).
- E11 Conclusion, as in route B: V(F) → Cu(F) lands in the compacts, Cuntz ⇒ MvN (x95-obstruction), and
  `grothendieckAddGroup_eq_zero_of_nsmul_eq_zero` rules out x.

Printed hypotheses check:
- Cu(A) ≅ Cu(B) ≅ Cu(𝒵) with A = B = E_d, via E5.
- Cu(A ⊗ B) ≇ Cu(𝒵) via E11.
- The question asks only for Cu-semigroup isomorphisms, so the Cu iso need not send [1] to 1. E_d has [1] = d·e, which
  is allowed.

## 9. Verdict

- Verified by hand: E_d satisfies F1 and F4; K₁ is ℤ/d along the tower (§3.2); the stage torsion class is nonzero (§4.1).
- Standard but not yet written: the compatibility of ⊠ with the suspension iso (§4.2(a)).
- Recommendation:
  - Keep route B as the fleet's primary route (review PASS; lanes are already building it).
  - Ask x95-jiangsu and x95-cuz to state E2–E5 for arbitrary (p,q) with no coprimality hypothesis. This costs nothing
    now and makes E_d a drop-in replacement for route B's Cu walls.
  - The E_d obstruction (E6–E10) reuses the same K-theory lanes as route B plus κ.
