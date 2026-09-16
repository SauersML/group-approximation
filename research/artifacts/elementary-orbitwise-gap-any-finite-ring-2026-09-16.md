# Orbitwise fixed-point gaps for elementary groups over arbitrary finite rings (2026-09-16)

Swarm lane on `sofic-groups-embed-in-simple-kazhdan-sofic-groups`. Everything below is unreviewed.

## 0. Results

- **Theorem G (§2).** `EL_n(𝒜) ≤ H ≤ GL_n(𝒜)`, acting on the columns `W^n` of a finite module, has orbitwise gap
  `1/(2n²)`. No semisimplicity, commutativity or finiteness of `𝒜` is assumed.
- **Corollary C′ (§3).** Kazhdan cut-downs of column models of `EL_n(R)` through arbitrary finite image rings certify
  only LEF quotients. This removes the semisimplicity hypothesis from Corollary C of
  `orbitwise-gap-sofic-approximations-are-local-embeddings` and closes target T5 of
  `research/artifacts/sk-sofic-almost-action-plan-2026-09-14.md`.
- **Host consequence (§4).** If `[Δ,Δ]` is not LEF, no assignment of the letters of `F_2⟨A⟩` to matrices over `F_2`,
  with any almost invariant sets of vectors, certifies soficity of the lamplighter host `G_Δ` or of `EL_3(F_2[Δ])`.
- **§5** records where a sofic approximation of a non-LEF host must now live, and what Theorem G does not cover.
- **Nodes.**
  - Theorem G is claim `elementary-group-column-actions-have-orbitwise-gap`, with direct route
    `elementary-group-column-actions-orbitwise-gap-proof`.
  - Corollary C′ and the host consequence are claim `column-model-kazhdan-cut-downs-certify-only-lef`, with route
    `column-model-kazhdan-cut-downs-lef-proof`.
  - The remaining input for the target is the open claim `sofic-lamplighter-host-elementary-groups-are-sofic`. The
    reduction is route `sofic-envelope-from-sofic-lamplighter-host`.

## 1. Setting

- `𝒜` is a unital ring and `W` a unital left `𝒜`-module (`1·w = w`) that is finite as a set. Fix `n ≥ 2` and put `V = W^n`, written as
  columns `x = (x_1, …, x_n)`.
- `M_n(𝒜)` acts on `V` by `(hx)_k = Σ_j h_(kj) x_j`. Each `h` acts additively, and `(hh′)x = h(h′x)`.
- For `i ≠ j` and `a ∈ 𝒜`, `e_ij(a) = I + aE_ij`. `EL_n(𝒜)` is the group they generate.
- For `w ∈ W`, `w e_i` is the column with `w` in coordinate `i` and `0` elsewhere. For `S ⊆ W`, `S e_i = {w e_i : w ∈ S}`.
- `𝒜w = {aw : a ∈ 𝒜}` is an additive subgroup of `W`. For `x ∈ V` put `L(x) = Σ_j 𝒜x_j ≤ W`.
- An action `H ↷ Ω` on a finite set has *orbitwise gap* `δ` if for every `h ∈ H` and every `H`-orbit `O`, either `h`
  fixes `O` pointwise or `h` moves at least `δ|O|` points of `O`. This is the definition of
  `orbitwise-gap-sofic-approximations-are-local-embeddings`, applied to the image of `H` in `Sym(Ω)`.

## 2. Theorem G

**Theorem G.** Let `H` be a group with `EL_n(𝒜) ≤ H ≤ GL_n(𝒜)`, let `O ⊆ V` be an `H`-orbit, and let `g : V → V` be
any additive map, for instance any `g ∈ M_n(𝒜)`. If `g` moves fewer than `|O|/(2n²)` points of `O`, then `g` fixes `O`
pointwise.

So `H ↷ V` has orbitwise gap `δ_n = 1/(2n²)`. So does its restriction to any `H`-invariant subset `Z ⊆ V`, since the
orbits of `H|_Z` are the `H`-orbits contained in `Z`.

*Proof.* Put `P = {v ∈ V : gv = v}`. It is the kernel of the additive map `g − id`, hence an additive subgroup of `V`.
Put `m = |O ∖ P|` and assume `m < |O|/(2n²)`.

1. **Root cosets.** Fix `i ≠ j` and put `T_ij = {e_ij(a) : a ∈ 𝒜} ≤ H`.
   - For `x ∈ V`, `e_ij(a)x = x + (a x_j) e_i`. So the `T_ij`-orbit of `x` is `x + S_ij(x)` with
     `S_ij(x) = (𝒜x_j) e_i`, an additive subgroup of `V`.
   - `O` is `H`-invariant and `T_ij ≤ H`, so `O` is a disjoint union of `T_ij`-orbits.
2. **Coset lemma.** Let `S ≤ V` be a subgroup and `C = y + S` a coset with `C ⊄ P`. Then `|C ∖ P| ≥ |C|/2`.
   - If `C ∩ P = ∅` this is clear.
   - Otherwise pick `p ∈ C ∩ P`. Then `C = p + S` and, `P` being a subgroup, `C ∩ P = p + (S ∩ P)`.
   - `C ⊄ P` forces `S ⊄ P`, so `S ∩ P` is a proper subgroup of `S` and `|C ∩ P| = |S ∩ P| ≤ |S|/2 = |C|/2`.
3. **Bad sets.** Let `B_ij ⊆ O` be the union of the `T_ij`-orbits in `O` that are not contained in `P`.
   - Each such orbit `C` has `|C| ≤ 2|C ∖ P|` by step 2, so `|B_ij| ≤ 2|B_ij ∖ P| ≤ 2m`.
   - If `x ∈ O ∖ B_ij`, then `x + (𝒜x_j)e_i ⊆ P`. As `x ∈ P` and `P` is a subgroup, `(𝒜x_j) e_i ⊆ P`.
4. **Diagonal positions.** For `i ≠ j` put `s_ij = e_ij(1) e_ji(−1) e_ij(1) ∈ EL_n(𝒜) ≤ H`.
   - Applied to `x`, the factors act from right to left by `x_i ↦ x_i + x_j`, then `x_j ↦ x_j − (x_i + x_j) = −x_i`,
     then `x_i + x_j ↦ (x_i + x_j) + (−x_i) = x_j`. So `(s_ij x)_i = x_j`, `(s_ij x)_j = −x_i`, and the other
     coordinates are unchanged.
   - Put `D_ij = s_ij^(−1)(B_ji) ⊆ O`. Then `|D_ij| = |B_ji| ≤ 2m`.
   - If `x ∈ O ∖ D_ij`, then `z = s_ij x ∈ O ∖ B_ji`. Step 3 for the pair `(j,i)` gives `(𝒜z_i) e_j ⊆ P`, that is
     `(𝒜x_j) e_j ⊆ P`.
5. **Counting.** For each `j` choose `i(j) ≠ j`, possible since `n ≥ 2`. Put
   `E = ⋃_(i≠j) B_ij ∪ ⋃_j D_(i(j) j)`. Then `|E| ≤ (n(n−1) + n)·2m = 2n²m < |O|`, so some `x ∈ O ∖ E` exists. For
   this `x`, steps 3 and 4 give `(𝒜x_j) e_k ⊆ P` for all `j` and `k`: `k ≠ j` from `B_kj`, and `k = j` from
   `D_(i(j) j)`.
6. **Conclusion.** `P` is a subgroup, so it contains `Σ_(j,k) (𝒜x_j) e_k = L(x)^n`, the columns with all entries in
   `L(x)`. Every `y ∈ O` is `y = hx` with `h ∈ H ⊆ M_n(𝒜)`, and `y_k = Σ_j h_(kj) x_j ∈ L(x)`. So `O ⊆ L(x)^n ⊆ P`,
   and `g` fixes `O` pointwise. ∎

**Remarks.**
- **What is used.** The proof uses only three things: `g` is additive; `H` contains every `T_ij` and hence every
  `s_ij`; and `H ⊆ M_n(𝒜)`. Finiteness is used only through `|O| < ∞`.
- **Larger groups.** The proof works directly with `H`-orbits for any `H` between `EL_n(𝒜)` and `GL_n(𝒜)`, and in
  fact for any submonoid of `M_n(𝒜)` that contains `EL_n(𝒜)` and acts by permutations. It does not pass through the
  `EL_n`-orbits.
- **Non-unital homomorphisms.** Suppose `φ : R → End(W)` is a ring homomorphism with `e = φ(1)` not the identity.
  - Then `φ(r) = eφ(r) = φ(r)e`, so `W = eW ⊕ (1−e)W`. Every `φ(r)` kills `(1−e)W` and maps into `eW`.
  - The generators `e_ij(φ(r))` act on `V = (eW)^n ⊕ ((1−e)W)^n` as `ρ′ ⊕ id`, where `ρ′` comes from the unital
    homomorphism `r ↦ φ(r)|_(eW)`.
  - An orbit is `O′ + v_0` with `O′` a `ρ′`-orbit, and fixed points correspond. So the gap transfers.
- **Constant.** `1/(2n²)` is not sharp. For semisimple `𝒜`, Family (E) gives `1/2`. In every case computed in §6
  (matrices in `M_n(𝒜)` and group words) the minimal moved fraction is exactly `1/2`, but `1/2` is not proved in
  general. Theorem O needs only a gap that depends on `n` alone.
  - *Referee addition (2026-09-16).* For arbitrary additive `g`, `1/2` fails. Take `𝒜 = W = F_2 × F_2` and `n = 2`, so
    `V = F_2^2 × F_2^2` and `EL_2(𝒜) = SL_2(F_2) × SL_2(F_2)`.
    - The orbit `O` with both factors nonzero has `9` points.
    - The additive map `g = id + D∘C`, with `C(x,y) = x_1 + y_1` and `D(1)` nonzero, fixes exactly the hyperplane
      `{x_1 + y_1 = 0}` and moves `4` of the `9` points.
    - Random fixed subspaces, over small `F_2`-algebras generated by random matrices, also give fractions `4/9`,
      `10/21` and `24/49`. All of them are above `1/(2n²)`.
    - So the question about `1/2` concerns only `g ∈ M_n(𝒜)` or group elements.
- **Consistency checks.**
  - `Sym(m)` on points has no gap: a transposition moves `2/m` of the points. That group has no root subgroups.
  - Permutation matrices acting on `F_2^m` have no orbitwise gap either: the orbit of `e_1` has `m` points and a
    transposition moves 2 of them. Their image contains no `T_ij`. So the root subgroups are the load-bearing
    hypothesis, not linearity.

## 3. Corollary C′: column models through arbitrary finite image rings

**Corollary C′.** Let `R` be a finitely generated unital ring, `n ≥ 3`, and `H = EL_n(R)` with a finite Kazhdan
generating set `A` (`elementary-groups-over-fg-rings-have-property-t`). Let `G = H/K`. For each `N`:
- let `W_N` be a finite abelian group and `φ_N : R → End(W_N)` a unital ring homomorphism, with `𝒜_N = φ_N(R)`;
- let `H` act on `X_N = W_N^n` by `ρ_N(h) = (φ_N(h_(kl)))_(k,l)`;
- let `Y_N ⊆ X_N` satisfy `|aY_N Δ Y_N| ≤ ε_N|Y_N|` for `a ∈ A`, with `ε_N → 0`;
- let `σ_N` complete the partial maps `a|_(Y_N ∩ a^(−1)Y_N)` to permutations of `Y_N`.

Then:
- if `σ_N` is a sofic approximation of `G`, then `G` is LEF;
- if `G` is IRS-rigid, infinite and simple, it suffices that `σ_N` satisfies (AF1) and `|Fix_N| ≤ (1−c)|Y_N|` for some
  `c > 0`.

*Proof.*
1. **Homomorphism.** `φ_N` is a unital ring homomorphism and matrix multiplication is given by ring operations on
   entries. So `ρ_N : H → GL_n(𝒜_N)` is a homomorphism with `ρ_N(e_ij(r)) = e_ij(φ_N(r))`. Hence
   `ρ_N(H) = ⟨e_ij(φ_N(r)) : r ∈ R⟩ = EL_n(𝒜_N)`, acting on `X_N` by additive permutations.
2. **Common gap.** Apply Theorem G with `𝒜 = 𝒜_N`, `W = W_N` and `H = EL_n(𝒜_N)`. Every `ρ_N(h)` is additive, so
   `ρ_N(H) ≤ Sym(X_N)` has orbitwise gap `1/(2n²)`. Since `n` is fixed, this gap is common to all `N`.
3. **Apply Corollary C.** Corollary C of `orbitwise-gap-sofic-approximations-are-local-embeddings` is stated for any
   `ρ_N` whose images have a common orbitwise gap. Its proof (route
   `orbitwise-gap-sofic-approximations-local-embeddings-proof`, steps 1–5) uses about `ρ_N` only the following:
   - `ρ_N(H)` acts on `X_N` by permutations: injectivity of letters in step 1, and invariant sets in step 2;
   - the gap is inherited by `ρ_N(H)|_(Z_N)` on invariant `Z_N`: step 2, and §2 above;
   - the Kazhdan pair of `H`, for the cutting lemma;
   - Theorem O;
   - for the simple variant, Consequence 1 of `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`.

   Linearity over a field and semisimplicity are not used there. So the corollary applies verbatim. ∎

**Scope of "column models".** Corollary C′ covers exactly the models in which `H` acts on columns through a ring
homomorphism on entries. Other linear representations of `H`, such as tensor, adjoint or exterior powers, are not
of this form. Their root subgroups act by polynomial maps of degree `> 1` in `a`, so step 1 of Theorem G does not
apply to them. They are not covered.

## 4. Consequence for the hosts

Take `R = F_2⟨A⟩` for a finite alphabet `A` and `H = EL_n(F_2⟨A⟩)` with `n ≥ 3`. The quotients are:
- `G_Δ = EL_n(LC(2^Δ,F_2) ⋊ (Z/2 ≀ Δ))`, through a surjection of `F_2⟨A⟩` onto the finitely generated crossed product;
- `EL_3(F_2[Δ])`, through `F_2⟨A⟩ ↠ F_2[Δ]`, with `A` a symmetric generating set of `Δ`.

A unital ring homomorphism `F_2⟨A⟩ → End(W_N)` forces `2·id = φ(2) = 0`, so `W_N ≅ F_2^(m_N)`. It is then an arbitrary
assignment of the letters to `m_N × m_N` matrices over `F_2`, and `𝒜_N` is the algebra they generate, radical allowed.

**Host consequence.** Suppose `[Δ,Δ]` is not LEF, for instance `Δ = C(Γ)` with `Γ` finitely generated, sofic and not
LEF (`groups-embed-in-derived-subgroup-of-half-line-overgroup`). Then no sequence of such assignments, with any
`ε_N`-almost invariant sets of vectors (`ε_N → 0`), gives a sofic approximation of `G_Δ` or of `EL_3(F_2[Δ])` by the
completion procedure of §3.

*Proof.* By Corollary C′ such a quotient would be LEF. But `[Δ,Δ] ≤ EL_3(F_2[Δ]) ≤ G_Δ`. The first inclusion is the
Whitehead embedding `γ ↦ diag(u_γ,1,1)` of `perfect-groups-embed-in-crossed-product-elementary-groups`, with `X` a point.
The second holds because `F_2[Δ] ⊆ F_2[Z/2 ≀ Δ]` is a unital subring of the crossed product, and `EL_3 ≤ EL_n` by
blocks (plan artifact, R1). LEF passes to subgroups. ∎

The established node already had this for semisimple image algebras. It left open whether the image algebras of the
Theorem A models (`sofic-lamplighter-bernoulli-crossed-products-have-rank-models`) are semisimple. That question no
longer matters for this obstruction.

## 5. Where a sofic approximation of a non-LEF host must now live

This refines (M1)/(M2) of `research/artifacts/sk-sofic-almost-action-plan-2026-09-14.md` §4. A sofic approximation of
`G_Δ` with `[Δ,Δ]` not LEF needs one of the following.
- **(M1) No genuine cover action.** The letters' permutations are not the Kazhdan cut-down of any genuine `H`-set with
  a common orbitwise gap. The cutting lemma rounds only genuine `H`-sets, so the Steinberg relations of `H` must fail
  on a vanishing but nonzero set of points.
- **(M2′) Genuine `H`-sets that are not column models.** Examples:
  - transitive `H/L` through finite quotients of `H` whose point stabilizers are not vector stabilizers, such as
    projective or flag-type spaces over rings with a radical, or alternating quotients if `H` has them (not checked
    here);
  - affine actions `x ↦ ρ(h)x + c(h)`: on a `T_ij`-orbit the map `a ↦ (a x_j)e_i + c(e_ij(a))` need not be additive, so
    step 1 fails;
  - other linear representations (§3, scope).

  For such sets the fixed-point proportions of the relators of `K` must tend to `1`.
- **Lie-type quotients: partial.** If the relevant finite quotients are simple of Lie type, transitive fixed-point
  ratios are bounded by primitive ones, since fibres of `H/L → H/M` have equal size. A gap would then follow from
  Liebeck–Saxl-type bounds (not read at source). This breaks for elements of normal unipotent radicals, which act
  trivially on the primitive quotients.

## 6. Computation

`experiments/elementary-orbitwise-gap-2026-09-16/orbitwise_gap_check.py`, with output in `output.txt` there:
- **Method.**
  - It builds the ring and module tables and checks all ring and module axioms exhaustively.
  - It computes the `EL_n(𝒜)`-orbits on `W^n` from the generators `e_ij(a)` and checks their invariance.
  - It runs over matrices `g`: all of `M_n(𝒜)` when `|𝒜|^(n²)|V| ≤ 2·10^8`; otherwise 1500 random choices of the
    first `n−1` rows, with the last row exhaustive. In both cases it adds 1500 random words in the generators.
  - It asserts moved fraction `≥ 1/(2n²)` on every orbit where `g` is nontrivial.
- **Cases (17).**
  - `F_2`, `F_2[t]/(t²)`, `Z/4` and `F_2[t]/(t²)` with `W = 𝒜 ⊕ 𝒜/(t)`, for `n = 2, 3`, all exhaustive;
  - `F_2[t]/(t³)`, `F_2[x,y]/(x,y)²`, and `T_2(F_2)` on its natural module and on itself: `n = 2` exhaustive,
    `n = 3` sampled;
  - the noncommutative `F_2⟨x,y⟩/(x², y², yx, deg 3)` for `n = 2`, exhaustive.
- **Result.** The bound holds in all cases. The minimal moved fraction is `2/3` (`n = 2`) or `4/7` (`n = 3`) for the
  commutative local rings, and `1/2` for `T_2(F_2)`. The overall minimum is `1/2`.
- **Scope.** This is evidence for the listed cases only. The theorem rests on the proof in §2.

## 7. Credit and checks

- The argument is an elementary root-subgroup count. No novelty is claimed for the method. What is new is its use to
  remove semisimplicity from Corollary C.
- **Bounded literature check (2026-09-16), abstracts only.** Queries to the arXiv API export interface:
  - `sofic AND Kazhdan`, `sofic AND "property (T)"`, `"linear sofic"`, `"locally embeddable" AND sofic`;
  - `"invariant random subgroups" AND sofic`, `"permutation stable" AND "property (T)"`;
  - `"fixed point ratio" AND "finite rings"`, `sofic AND Steinberg`.

  Relevant hits were arXiv:2608.05362 (Alekseev–Thom), 2511.16515 (Alekseev–Drigalla), 2601.18742 (Alekseev–Bradford)
  and 2603.16591 (Salo). None states an orbitwise gap for elementary groups over rings with a radical, or exhibits a
  finitely generated sofic non-LEF Kazhdan group. This is not a full novelty audit.
- **Not read at source:** Ershov–Jaikin-Zapirain (imported through its claim), Liebeck–Saxl, Caprace–Kassabov.
