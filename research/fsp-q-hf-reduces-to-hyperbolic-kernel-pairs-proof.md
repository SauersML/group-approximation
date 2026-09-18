---
rg: 2
id: fsp-q-hf-reduces-to-hyperbolic-kernel-pairs-proof
kind: route
title: Read group normal forms as Cohn coproduct normal forms, apply the vertex Linnell condition coefficient by coefficient, and pass to directed unions
target: fsp-q-hf-reduces-to-hyperbolic-kernel-pairs
requires:
  - fsp-graph-of-rings-and-linnell-extension-imports
  - hughes-free-division-rings-pass-to-directed-unions
---

## Inputs

- **Gräter, Forum Math. 32 (2020), Cor. 8.3.** A Hughes-free division ring of a locally indicable group is
  Linnell. So for every `K <= A`, the right transversals of `K` in `A` are left independent over the division
  closure of `kK` in `D_A`. This is quoted by the FSP citation node.
- **Cohn's normal form for coproducts over a division ring** (Cohn, *Free Ideal Rings and Localization*, §2.4;
  Dicks). Let `E` be a division ring, `E ⊆ P, Q`. Choose a left `E`-basis `{1} ∪ X` of `P` and a left `E`-basis
  `{1} ∪ Y` of `Q`. Then `P *_E Q` is a free left `P`-module. Its basis consists of `1` and the alternating
  products `y1 x1 y2 x2 ...` (finite, ending in either letter) with `yi ∈ Y`, `xi ∈ X`, beginning with a letter
  of `Y`.
- **Cohn.** `R = D_A *_{D_C} D_B` is a fir, so it embeds in its universal field `U(R)`, and `kG -> R` is injective
  (FSP, Cor. locIndGraphDivRing; import item 6).
- **Serre.** A finitely generated group acting on a tree without inversions, with every element elliptic, fixes a
  vertex.

## 1. Division closures of vertex subgroups

Let `K <= A`. The division closure of `kK` in `U` equals its division closure in `D_A`, since `D_A ⊆ U` is a
division subring containing `kK`. Call it `D_K`. It lies in `D_A ⊆ R`. The same holds for `B`.

## 2. Bases adapted to the group

- Apply Gräter to `C <= A`. Fix a right transversal `T_A` of `C` in `A` with `1 ∈ T_A`. Then `T_A` is left
  independent over `D_C`.
- Extend `T_A` to a left `D_C`-basis `T_A ∪ X''` of `D_A`. Put `X = (T_A \ {1}) ∪ X''`.
- Define `T_B`, `Y''` and `Y` the same way.

**Group normal form.** Every `g ∈ G` can be written uniquely as `g = a · s1 s2 ... sn` with:
- `a ∈ A`;
- the `si` alternating between `T_B \ {1}` and `T_A \ {1}`, starting with `s1 ∈ T_B \ {1}`, and possibly `n = 0`.

To see this, take the reduced form `g = c t1 ... tm` relative to the right transversals `T_A`, `T_B`. If
`t1 ∈ T_A`, absorb `c t1` into `a`. Write `w(g) = s1 ... sn` and let `W` be the set of these words.

**Dictionary.**
- In `R`, the product `s1 ... sn` is a Cohn basis monomial `m_{w(g)}`, since `T_B \ {1} ⊆ Y` and
  `T_A \ {1} ⊆ X`.
- Distinct words give distinct basis monomials.
- So `g = a · m_{w(g)}`, with `a ∈ D_A` the left coefficient.

## 3. Elliptic subgroups (item 1)

**Case `K <= A`.**
- For `k ∈ K`, `kg = (ka) · w(g)`. So `Kg = Kg'` if and only if `w(g) = w(g')` and `Ka = Ka'`.
- Let `g1, ..., gr` lie in distinct right `K`-cosets and satisfy `Σ ei gi = 0` with `ei ∈ D_K`.
- This is an identity in `R`, since `ei ∈ D_A ⊆ R`. Collect by basis monomials:
  `Σ_w (Σ_{i : w(gi) = w} ei ai) m_w = 0`.
- By Cohn's freeness, each inner sum `Σ_{i : w(gi) = w} ei ai` vanishes in `D_A`.
- For a fixed `w`, the `ai` lie in distinct right `K`-cosets of `A`. By Gräter in `D_A`, all `ei = 0`.

**Case `K <= B`.** The coproduct is symmetric, so the same argument applies with the roles of `A` and `B` swapped.

**Case `K = h K' h^-1` with `K' <= A` or `K' <= B`.**
- Conjugation by the unit `h ∈ kG` is an automorphism of `U`. It carries `kK'` to `kK`, so `D_K = h D_{K'} h^-1`.
- If `Σ (h e'_i h^-1) gi = 0`, then `Σ e'_i (h^-1 gi) = 0`.
- The `h^-1 gi` lie in distinct right `K'`-cosets, so all `e'_i = 0`.

## 4. Locally elliptic subgroups and Hughes pairs (items 2–4)

**Item 2.**
- Write `K` as the directed union of its finitely generated subgroups `Kj`. Each `Kj` is elliptic.
- `∪ D_{Kj}` is a division subring of `U` that contains `kK`, so `D_K = ∪ D_{Kj}`.
- A finite relation `Σ ei gi = 0` has all `ei` in one `D_{Kj}`.
- Distinct `K`-cosets are distinct `Kj`-cosets, so item 1 for `Kj` applies.

**Item 3.** `N ⊴ H` and `H/N ≅ Z` with generator `tN`, so the cosets `N t^n` are pairwise distinct. The powers
`t^n` are therefore part of a right transversal of `N` in `G`, and item 2 applies.

**Item 4.**
- By definition, `D_L` is Hughes-free if and only if the Hughes condition holds for all pairs `(H, N)` with `H <= L`
  finitely generated.
- If `N` is locally elliptic, item 3 settles the pair.
- Otherwise some finitely generated subgroup of `N` fixes no vertex. By Serre (Bass-Serre actions are without
  inversions), it contains a hyperbolic element.
- **Same minimal subtree.** `N ⊴ H`, so the minimal `N`-subtree `T_N` is `H`-invariant, which gives `T_H ⊆ T_N`.
  Also `T_H` is `N`-invariant, so `T_N ⊆ T_H`.

## 5. Where the argument stops

- Let `N` be non-elliptic. A relation `Σ en t^n = 0` has coefficients `en ∈ D_N`. These are rational expressions in
  elements of several conjugate vertex rings.
- In the Cohn normal form they have no left coefficient in `D_A`, so collecting by monomials gives no relation over
  a vertex ring.
- The same holds for Cohn inner rank over `R`. Inner rank detects `R`-linear dependence of matrices over `R`, while
  the `en` are only in `U`. Writing them via Cramer's rule, `en = row · M^-1 · column` with `M` full over `R`, turns
  the relation into the non-fullness of one square matrix over `R`. That matrix has the powers `t^n` as entries
  together with `M`.
- Proving it full needs a statement about full matrices over the sub-coproduct of `N`. This is exactly the subgroup
  compatibility stated on the claim node.
- So the remaining input is the compatibility statement, not a finer rank computation in `R`. Its
  characteristic-`p` one-relator instances (FSP, Thm LL_HF, primitivity rank 2) are open.

## Calibration

- **Free group `F2 = Z * Z`, `C = 1`.** Items 1-3 give the Hughes condition for every pair with `N` inside a
  conjugate of a factor. This is consistent with Lewin's theorem that the free field is the Hughes-free division
  ring of `k[F2]`.
- The remaining pairs there (for example `N` the kernel of `F2 -> Z` of infinite rank) are covered by Lewin's
  theorem through Malcev-Neumann series of the ordered group `F2`. The coproduct normal form alone does not reach
  them, so the method is consistent on the known case and does not claim more.
