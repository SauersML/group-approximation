# One-sided pairs over Radu's lattice at total radius four and five

Date: 2026-09-12. Lane: w7-radu-r4-linear, after w7-vh-anchored (e505d7328c, 9458a0c3d1).
Verifier: w4-vf-linear-b.
Claim: `radu-lattice-one-sided-pairs-need-radius-five`, route `radu-lattice-one-sided-pairs-need-radius-five-proof`.

Notation follows `research/artifacts/radu-lattice-anchored-linear-gadgets-2026-09-12.md` (cited as [AG]).
- Γ = Γ_R is Radu's lattice: horizontal letters a, b, c and vertical letters x, y, z, with the square table of [AG §0].
- A = ⟨a,b,c⟩ and V = ⟨x,y,z⟩, both C₂*C₂*C₂.
- Every g has a unique normal form αω, with α a reduced word in a, b, c and ω a reduced word in x, y, z, and |g| = |α| + |ω|.
- B_r and S_r are the ball and the sphere of radius r in the six letters.
- Γ_0 is the finite residual, and δ = xz.
- K is a field. For A, B ∈ M_n(K[Γ]) with BA = I_n, the defect is D = I_n − AB. S_A and S_B are the unions of the entry supports.

## Summary

1. **Source check (§0).** Remark 3.6 of Titz Mite–Witzel states what [AG, Corollary 3.2] uses. No correction.
2. **Theorem A (§2).** Suppose S_A ⊆ uB_rw and S_B ⊆ w⁻¹B_su⁻¹ with r + s ≤ 4. Then over any field AB = I_n, at every size n.
   - (B_2,B_2), (B_1,B_3) and (B_3,B_1) carry no pair, so the construction branch of the task is refuted.
   - The invariant finer than Γ_0 is not a quotient group. It is the idempotent law D = D² combined with the Γ_0 coincidences.
3. **Lemma B (§3).** Let C_k be the set of points of B_k that share a Γ_0-coset with another point of B_k. If C_k·C_k ∩ C_k = ∅, then r + s = k carries no pair.
4. **Theorem C (§4).** Suppose every element of length ten in Γ_0 is yδ⁴y or yδ⁻⁴y (hypothesis H10). Then r + s = 5 carries no pair.
5. **Radius six (§4.3).** C_6 contains δ and δ² = δ·δ, so C_6 is not product-free and Lemma B stops. Open.
6. Finer group invariants that were tried are in §5, and the extension of the [AG §4] table is in §6.

## 0. Source check of Remark 3.6

Titz Mite–Witzel (arXiv:2509.05054v2), Remark 3.6: "We checked with a computer that the only non-trivial elements in Γ_R of length at most eight that vanish under Φ are δ⁴ and δ⁻⁴."
- Φ is a representation of the derived subgroup Γ' into SL₂(Q(√−15, √17)).
- Length is word length in the six letters, which is the metric of [AG].
- The same remark says the image of Φ is residually finite, so an element of Γ_0 vanishes under Φ.

Written out: Γ^ab = (Z/2)³ is finite, so Γ_0 ⊆ Γ'. Φ(Γ') is finitely generated and linear, so it is residually finite. A finite-index normal subgroup of Φ(Γ') pulls back to a finite-index subgroup of Γ. That subgroup contains a finite-index normal subgroup of Γ, so it contains Γ_0. So Φ(Γ_0) lies in every finite-index normal subgroup of Φ(Γ'), and it is trivial.

**Input used below.** Γ_0 ∩ B_8 ⊆ {1, δ⁴, δ⁻⁴}.

Theorem A does not use δ⁴ ∈ Γ_0 (Lemma 3.5 with Proposition 3.4(4), which cites [Rad20, Prop 5.4]). If δ⁴ ∉ Γ_0, the proof ends one step earlier.

**Checked by hand.**
- The relators have even length, and Γ^ab = ⟨a⟩×⟨x⟩×⟨y⟩ with a = b = c and x = z. So elements of Γ_0 have even length, and even counts of horizontal letters, of letters x or z, and of y.
- a, b, c ↦ ε (central), x, z ↦ s, y ↦ t defines Γ → C₂ × D_∞. Every relator maps to s², t² or ε². So the vertical part ω of an element of Γ_0 maps to 1 in ⟨s,t⟩.

The lower bound "no nontrivial element of Γ_0 is shorter than eight" is not hand-checkable and stays imported. Verdict: PASS as a source check.

## 1. Geodesic words and coincidences in B_4

**Lemma 1.1.** A word for g = αω has at least |α| horizontal letters and at least |ω| vertical letters. If ω ∈ V and a word for ω has length |ω|, it is the reduced word of ω.

*Proof.*
- Square moves hv → v'h' preserve both letter counts. Moving every horizontal letter to the left gives a word α'ω', with α' horizontal and ω' vertical.
- Free reduction of α' and ω' only removes letters, and it yields the normal form, which is unique.
- If g ∈ V, a word of length |ω| therefore has no horizontal letter, so it is a word in x, y, z representing ω in C₂*C₂*C₂.
- Free reduction strictly shortens a non-reduced word, and reduced words are unique. ∎

**Lemma 1.2.** If g ≠ h lie in B_4 and g⁻¹h ∈ Γ_0, then {g, h} = {δ², δ⁻²}.

*Proof.*
- |g⁻¹h| ≤ 8, so g⁻¹h = δ^{±4} by §0.
- 8 = |δ^{±4}| ≤ |g| + |h| ≤ 8, so |g| = |h| = 4. A geodesic word u for g⁻¹ followed by a geodesic word w for h is a word of length 8 for δ^{±4}.
- By Lemma 1.1, uw is xzxzxzxz or zxzxzxzx letter by letter. So g⁻¹ ∈ {xzxz, zxzx}, that is g = δ^{∓2} and h = δ^{±2}. ∎

## 2. Theorem A

**Theorem A.** Let K be a field and A, B ∈ M_n(K[Γ]) with BA = I_n. Suppose S_A ⊆ uB_rw and S_B ⊆ w⁻¹B_su⁻¹ for some u, w ∈ Γ and r + s ≤ 4. Then AB = I_n.

*Proof.*
1. **Normalize.** A' = u⁻¹Aw⁻¹ and B' = wBu satisfy B'A' = wBAw⁻¹ = I_n and A'B' = u⁻¹ABu. Their supports lie in B_r and B_s. So assume u = w = 1. Every entry of D is then supported in S_AS_B ∪ {1} ⊆ B_4.
2. **Idempotent.** D² = I − 2AB + A(BA)B = D.
3. **Two-sided modulo Γ_0.** Let π: K[Γ] → K[Q] with Q = Γ/Γ_0.
   - Suppose X = π(A)π(B) − I_n ≠ 0, and choose a finite quotient Q → H injective on the support of X. Q is residually finite, so such an H exists.
   - In M_n(K[H]) the images still satisfy BA = I_n. That algebra is finite-dimensional, so the images also satisfy AB = I_n, and the image of X is 0.
   - H separates the support of X, so the image keeps a nonzero coefficient of X. This is a contradiction, so π(D) = 0.
   - So on every coset of Γ_0 the matrix coefficients of D sum to zero. This is [AG, Theorem 3.1] over K instead of F_p.
4. **Shape.** By Lemma 1.2 a coset of Γ_0 meets B_4 in at most one point, except that {δ², δ⁻²} may lie in one coset. So D = E(δ² − δ⁻²) with E ∈ M_n(K), and E = 0 if δ⁴ ∉ Γ_0.
5. **Disjoint square.** D² = E²(δ⁴ − 2·1 + δ⁻⁴). The elements δ⁴, 1, δ⁻⁴ differ from δ^{±2} by their normal forms. Comparing the coefficients of D = D² at δ² gives E = 0. So D = 0. ∎

**Remarks.**
- M_n(R[H]) embeds in M_{n|H|}(R), and determinants make it directly finite over any commutative ring R. So Theorem A holds over any commutative ring.
- [AG, Corollary 3.2] covers r + s ≤ 3. The new windows are (B_2,B_2), (B_1,B_3), (B_3,B_1), and the trivial (B_0,B_4) and (B_4,B_0).
- [AG] sees only π(D) = 0. In the ideal J = ker π, idempotency puts D in M_n(J^m) for every m, and at radius four the finite support turns that into a coefficient mismatch.
- The δ⁴ coincidence {δ², δ⁻²} is the only one available at radius four. A defect supported on it squares off its own support, so no size-n pair "using δ⁴ coincidences" exists there.

## 3. The product-free criterion

**Definition.** C_k is the set of g ∈ B_k such that g⁻¹h ∈ Γ_0 for some h ∈ B_k \ {g}.

**Lemma B.** Let A, B be as in Theorem A with r + s = k. After normalizing, D is supported in C_k. If C_k·C_k ∩ C_k = ∅, then AB = I_n.

*Proof.*
- A point of B_k \ C_k is alone in its coset within B_k, so step 3 makes its coefficient zero.
- For p ∈ C_k, the coefficient of D² at p is a sum over pairs q, r ∈ C_k with qr = p. No such pair exists.
- So D = D² vanishes on C_k as well. ∎

For k = 4, C_4 ⊆ {δ², δ⁻²} and C_4·C_4 ⊆ {1, δ^{±4}}. This is Theorem A.

## 4. Radius five and six

### 4.1 Coincidences in B_5 from δ^{±4}

Let F = {δx, δ⁻³x, δ⁻²x, δ²x} = {xzx, zxzxz, zxz, xzxzx} and R = {δ², δ⁻²}.

**Lemma 4.1.** The pairs g ≠ h in B_5 with g⁻¹h = δ^{±4} are {xzx, zxzxz}, {zxz, xzxzx}, {δ², δ⁻²}, and {tδ², tδ⁻²} for t ∈ {a, b, c, y}.

*Proof.*
- Swapping g and h, assume h = gδ⁴, and write g = αω. Then h = α(ωδ⁴) is in normal form.
- Let j be the length of the longest suffix of ω that cancels against δ⁴ = xzxzxzxz. That suffix is the reverse of the first j letters of δ⁴, and |h| − |g| = 8 − 2j.
- From |g|, |h| ≤ 5 and |g| + |h| ≥ 8, (|g|, |h|) is (3,5), (4,4), (5,3) or (5,5), with j = 3, 4, 5, 4.
  - j = 3 and |g| = 3: ω = xzx, so g = xzx and h = zxzxz.
  - j = 4 and |g| = 4: g = zxzx = δ⁻² and h = δ².
  - j = 5 and |g| = 5: g = xzxzx and h = zxz.
  - j = 4 and |g| = 5: ω ends in zxzx, and the letter before it, if any, is neither z (cancellation stops) nor x (reduced). So either ω = zxzx and α ∈ {a, b, c}, or ω = yzxzx and α = 1. So g = tδ⁻² and h = tδ². ∎

### 4.2 Theorem C

**Pairs from length ten.** Suppose g⁻¹h ∈ Γ_0 has length ten with g, h ∈ B_5. Then |g| = |h| = 5, and the geodesic words split in the middle.
- yδ^{±4}y lies in Γ_0 whenever δ⁴ does. Its unique geodesic word (Lemma 1.1) splits as (yxzxz)(xzxzy) and (yzxzx)(zxzxy), which gives the pair {δ²y, δ⁻²y}.
- **(H10)** Γ_0 ∩ S_10 ⊆ {yδ⁴y, yδ⁻⁴y}.

Under H10, C_5 ⊆ S := {1, a, b, c}·Ω, where Ω = F ∪ R ∪ yR ∪ Ry.

**Lemma 4.2.** S·S ∩ S = ∅.

*Proof.*
1. **Twisting.** For t ∈ {a, b, c} and ω ∈ Ω, ωt = t'ω' with t' ∈ {a, b, c} and ω' in the same one of F, R, yR, Ry. The rules are δa = bδ, δb = aδ, δc = cδ⁻¹, xa = ax, xb = bx, xc = cz, ya = ay, yb = cy and yc = by.
   - δ^{±2} commutes with a and b, and δ^{±2}c = cδ^{∓2}.
   - δ^i x t = t'δ^i x for t ∈ {a, b}, with t' = t for i even and t' the other letter for i odd. Also δ^i x c = cδ^{−i−1}x, which permutes F as δx ↔ δ⁻²x and δ⁻³x ↔ δ²x.
   - yδ^{±2}a = a·yδ^{±2}, yδ^{±2}b = c·yδ^{±2}, yδ^{±2}c = b·yδ^{∓2}.
   - δ^{±2}y·a = a·δ^{±2}y, δ^{±2}y·b = c·δ^{∓2}y, δ^{±2}y·c = b·δ^{±2}y.
2. **Ω·Ω ∩ Ω = ∅ in V.** In ⟨x, z⟩ ≅ D_∞ use δ^iδ^j = δ^{i+j}, δ^i x δ^j = δ^{i−j}x and δ^i x δ^j x = δ^{i−j}.
   - F has exponents E_F = {1, −3, −2, 2}. F·F gives rotations with exponents E_F − E_F = {0, ±1, ±3, ±4, ±5}, never ±2.
   - F·R and R·F give reflections with exponents in {0, −1, 3, −5, ±4}, disjoint from E_F.
   - R·R ⊆ {1, δ^{±4}}.
   - Products with a factor in yR ∪ Ry, with φ ∈ F ∪ R and ρ, ρ' ∈ R, are reduced words in x, y, z:
     - φ·yρ, ρy·φ, yρ·yρ' and ρy·ρ'y have a y strictly inside;
     - yρ·φ = y(ρφ) and φ·ρy = (φρ)y lie in Ω only if ρφ or φρ lies in R, which fails because RF and FR are reflections and RR ⊆ {1, δ^{±4}};
     - yρ·ρ'y ∈ {1, yδ^{±4}y} and ρy·yρ' ∈ {1, δ^{±4}}.
     None of these lies in Ω.
3. **Normal forms.** Let p = α₁ω₁ and q = α₂ω₂ lie in S.
   - If α₂ = 1, then pq = α₁·(ω₁ω₂).
   - Otherwise ω₁α₂ = t'ω₁' by step 1, and pq = (α₁t')·(ω₁'ω₂).
   - By uniqueness of normal forms, pq ∈ S needs the vertical part in Ω, which step 2 excludes. ∎

**Theorem C.** Assume H10. Suppose A, B ∈ M_n(K[Γ]) with BA = I_n, S_A ⊆ uB_rw and S_B ⊆ w⁻¹B_su⁻¹, where r + s = 5. Then AB = I_n.

*Proof.* Lemma 4.1 and H10 give C_5 ⊆ S. Then apply Lemma 4.2 and Lemma B. ∎

**Status of H10.**
- H10 is a finite statement. |S_10| = 2·1536 + 9·2304 = 23 808, and parity and C₂×D_∞ (§0) cut this down further.
- It follows from "ker Φ ∩ S_10 ⊆ {yδ^{±4}y}", the Remark 3.6 computation run to length ten.
- If other elements turn up, Lemma B still applies as long as the enlarged C_5 stays product-free, which is again a finite check.
- This lane did not run the computation, because RULES forbids enumerations.

### 4.3 Radius six

- C_6 contains δ⁻¹ = zx and δ³ = xzxzxz, because (zx)⁻¹·xzxzxz = δ⁴.
- It contains δ = xz and δ⁻³, because δ⁻¹δ⁻³ = δ⁻⁴.
- It contains δ² and δ⁻².
- δ·δ = δ², so C_6 is not product-free, and Lemma B gives nothing at r + s = 6. Radius six needs the coefficient equations of D = D² on C_6, for instance W_6 ∩ W_6^m = 0 for some m, where W_6 is the span of the zero-coset-sum elements supported in B_6.

## 5. Finer invariants that add nothing at length eight

| candidate | outcome | status |
|---|---|---|
| finite quotients, finite-index normal subgroups | contain Γ_0, so they are coarser | dead |
| finite-dimensional linear representations | image f.g. linear, so residually finite, so it kills Γ_0 | dead |
| letter identifications | y = 1 forces b = c and then z = x; z = x kills δ; a = b = c forces x = z. Each kills δ | dead |
| action on the horizontal tree | pushing a horizontal word through δ² leaves it unchanged (§4.2 step 1), so δ² acts trivially and the image does not separate δ² from δ⁻² | dead |
| augmentation (Jennings, Zassenhaus) filtration of F_p[Γ] | its intersection contains every element killed by all finite p-quotients, hence contains Γ_0 | dead |
| deeper normal N ⊊ Γ_0 with Γ/N sofic | a screen modulo N is valid, but separating δ² from δ⁻² needs δ⁴ ∉ N, and then Γ/N is sofic and not residually finite. No such quotient is known. The table realization of (B_1,B_1) is Γ itself [AG §4], so the support forces no quotient | no candidate |
| abelianized Γ_0, N = [Γ_0, Γ_0] | Γ/N is abelian-by-(residually finite), so sofic by Elek–Szabó, and the screen is valid. It is finer at length eight iff δ⁴ ∉ [Γ_0,Γ_0]. Γ/N is non-RF iff Γ_0 is not perfect. Neither is known | undecided |
| powers J^m of J = ker(K[Γ] → K[Γ/Γ_0]) | D = D^m ∈ M_n(J^m) for all m, so ∩J^m = 0 would kill every defect at every radius. But J/J² ≅ K[Γ/Γ_0] ⊗ H_1(Γ_0; K), so J = J² if H_1(Γ_0; K) = 0, and that group is unknown | undecided |

What does reach radius four is Theorem A: a ring identity (D = D²) on top of the Γ_0 screen, not a smaller normal subgroup.

## 6. Extension of the [AG §4] table

| candidate | where it dies | invariant |
|---|---|---|
| any size, r + s = 4, including (B_2,B_2), (B_1,B_3), (B_3,B_1) | D = E(δ² − δ⁻²) and D² = E²(δ⁴ − 2 + δ⁻⁴) have disjoint supports (Theorem A) | coincidence modulo Γ_0 plus D = D² |
| any size, r + s = 5, given H10 | C_5 is product-free (Lemma 4.2, Theorem C) | same, conditional on Γ_0 ∩ S_10 |
| any size, r + s = 5, without H10 | not decided | needs Γ_0 ∩ S_10, for instance ker Φ ∩ S_10 |
| any size, r + s = 6 | does not die by supports: δ·δ = δ² inside C_6 | needs the coefficient equations |
| smaller normal subgroups, abelianized Γ_0, J-adic filtration | §5 | coarser or undecided |

This corrects the [AG] sentence "blind from r+s=4 on". The coincidence screen alone is blind at four. With the idempotent law it excludes four, it excludes five under H10, and it is blind by supports at six.

## 7. Other lanes

- **w7-radu-gadget-b4** (nonlinear B_4 gadget, verifier w7-vf-nonlinear). Theorem A uses the ring structure, since D is an idempotent in M_n(K[Γ]). It says nothing about strict automata. The window-diameter screen of [AG §5] is unchanged, and the gadget with memories in B_2 and window in B_4 is not decided here.
- **w7-yh-rank-firewall.** That lane works on Y_h over F_3[G_3]. No rank function on K[Γ_R] is used or built here.
- The attempts of w3-lattice, w4-radu-f2 and w7-vh-anchored are cited, not repeated.

## 8. Open

1. H10, or a complete list of Γ_0 ∩ S_10, for instance from ker Φ ∩ S_10. This is finite.
2. r + s = 6: the coefficient equations of D = D² on C_6.
3. δ⁴ ∉ [Γ_0, Γ_0] (row 7 of §5), or H_1(Γ_0; F_p) ≠ 0 (row 8).
4. A pair at any size (unchanged).
