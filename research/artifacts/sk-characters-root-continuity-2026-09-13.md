# Characters of G_X: a character that tends to 1 on small root elements is trivial

2026-09-13, lane sk-characters. A written proof; no computation was run. UNREVIEWED.

## 0. Setting and statement

- `X ⊆ A^Z` is an infinite minimal subshift with shift `T`.
- `R = LC(X,F_2) ⋊_T Z`, with `u f u^{-1} = f∘T^{-1}`. Then `u^m e_U u^{-m} = e_{T^m U}`, so `u^m e_U = e_{T^m U} u^m`.
- `G = G_X = EL_3(R)`, the group of the note.
- `M(X,T)` is the set of `T`-invariant Borel probability measures. For clopen `P` put `‖P‖ := sup_{μ∈M(X,T)} μ(P)`.
- A *character* is a positive definite, conjugation-invariant function `χ: G → C` with `χ(e) = 1`.

**Theorem A.** Let `χ` be a character of `G`. Suppose `χ(e_12(e_P)) → 1` as `‖P‖ → 0`: for every `ε > 0` there is `η > 0` with `|1 − χ(e_12(e_P))| < ε` for every clopen `P` with `‖P‖ < η`. Then `χ ≡ 1`.

Contrapositive: every character other than `1` (the regular character `δ_e` included) is bounded away from 1 at some root elements `e_12(e_{P_n})` with `‖P_n‖ → 0`.

Contrast with the topological full group. For the commutator subgroup `Γ'` of the topological full group of a Cantor minimal system, Dudko–Medynets (arXiv:2602.16885v1, 18 Feb 2026, Theorem 1.1) prove that every indecomposable character is `1`, the regular character, or `γ ↦ ∏_{i=1}^k μ_i(Fix γ)` for ergodic invariant measures `μ_i`. The last family is continuous in the uniform metric `D(g,h) = sup_μ μ{x : gx ≠ hx}` (their p. 5). By Theorem A, `G_X` has no matrix analogue of this family: the amenable simple group of `X` has a character for every invariant measure, and the Kazhdan simple group `G_X` has no character that is continuous in measure.

## 1. Imports

**(I1) Carderi–Thom**, "An exotic group as limit of finite special linear groups", Ann. Inst. Fourier 68 (2018) 257–273. Quoted from arXiv:1603.00691v3, pp. 5–6, read 2026-09-13:

> "Lemma 1.4. Let q be a prime power and let ψ: SL_n(q) → C be a positive definite function. If there exists a non-central element g ∈ SL_n(q) such that |1 − ψ(x^{-1}gx)| < ε for some ε ∈ (0,1) and for all x ∈ SL_n(q), then |1 − ψ(h)| < 9(2ε + 16/q)^{1/2}, ∀h ∈ SL_n(q)."

Their Definition 1.1 includes `ψ(1) = 1`. The proof rests on "a result of Gluck [16, Theorem 3.4 and Theorem 5.3]": for every non-central `h ∈ SL_n(q)` and every non-trivial normalized irreducible character `χ_π`, `|χ_π(h)| < 8/q`. Gluck is D. Gluck, Sharper character value estimates for groups of Lie type, J. Algebra 174 (1995).

**(I2)** Every positive definite `ψ` with `ψ(e) = 1` satisfies `|ψ(g) − ψ(h)|² ≤ 2(1 − Re ψ(g^{-1}h))`. This is (⋆) in Carderi–Thom p. 4, where it is attributed to Bekka–de la Harpe–Valette, *Kazhdan's property (T)*, Prop. C.4.2.

**(I3)** Every normal subgroup of `G` is central or all of `G`, and `Z(G) = 1`. See the note, and the Cairn claim `simple-kazhdan-lef-group-from-minimal-subshift`.

## 2. Proof of Theorem A

Fix a nonempty clopen `B ⊆ X`. We prove `χ(e_12(e_B)) = 1`.

**Step 1: Kakutani–Rokhlin columns adapted to B.**
- Fix `J ≥ 1`. Pick `x ∈ X` and a clopen neighborhood `b` of `x` with `T^j b ∩ b = ∅` for `0 < j < J`. This is possible because `T` has no periodic points.
- Forward orbits of a minimal homeomorphism are dense, so the return time `r(x) = min{j ≥ 1 : T^j x ∈ b}` is finite on `b`.
- Each set `{x ∈ b : r(x) = j} = b ∩ T^{-j}b ∖ ⋃_{0<i<j} T^{-i}b` is clopen. By compactness only finitely many are nonempty, and `r ≥ J`.
- With `C_j = {r = j}`, the levels `T^a C_j` (`0 ≤ a < j`) partition `X`.
- Refine each `C_j` into finitely many clopen pieces according to the word `(1_B(T^a x))_{0≤a<j}`. Call the refined columns `c`, with bases `C_c` and heights `H_c ≥ J`. Every level `T^a C_c` is then contained in `B` or disjoint from `B`.
- The sets `b, Tb, …, T^{J−1}b` are disjoint with equal measure, so `μ(b) = Σ_c μ(C_c) ≤ 1/J` for every `μ ∈ M(X,T)`.

**Step 2: K equivalent pieces.**
- Fix integers `k, K' ≥ 1` and put `K = kK'`.
- For each column let `J_c = {a < H_c : T^a C_c ⊆ B}` and `m_c = ⌊|J_c|/K⌋`.
- Choose disjoint `J_c^{(1)}, …, J_c^{(K)} ⊆ J_c` of size `m_c`, and bijections `φ_c^{(i)}: J_c^{(1)} → J_c^{(i)}` with `φ^{(1)} = id`.
- Put `piece_i := ⊔_c ⊔_{a∈J_c^{(i)}} T^a C_c`, `B' := ⊔_i piece_i` and `E := B ∖ B'`.

Two consequences:
- `E` contains fewer than `K` levels of each column, so `‖E‖ ≤ K·sup_μ μ(b) ≤ K/J`.
- `μ(piece_i) = Σ_c m_c μ(C_c)` does not depend on `i`, so `‖piece_i‖ ≤ 1/K`.

**Step 3: a copy of GL_{3K}(F_2) in G containing e_12(e_{B'}).**

For levels of one column put `w^c_{a',a} := e_{T^{a'}C_c} u^{a'−a} = u^{a'−a} e_{T^a C_c}`. These satisfy:
- `w^c_{a'',a'} w^c_{a',a} = w^c_{a'',a}` and `(w^c_{a',a})^* := w^c_{a,a'}`;
- `w^{c'}_{b',b} w^c_{a',a} = u^{b'−b} e_{T^b C_{c'}} e_{T^{a'} C_c} u^{a'−a} = 0` unless `(c',b) = (c,a')`, because distinct levels are disjoint.

Define:
- `v_{i1} := Σ_c Σ_{a∈J_c^{(1)}} w^c_{φ_c^{(i)}(a), a}`,
- `v_{1i} := v_{i1}^*`,
- `v_{ij} := v_{i1} v_{1j}`.

Cross terms vanish because the ranges of distinct summands are distinct levels, and `J^{(j)} ∩ J^{(k)} = ∅` for `j ≠ k`. So `v_{ij} v_{kl} = δ_{jk} v_{il}` and `v_{ii} = e_{piece_i}`. The F_2-span `A` of the `v_{ij}` is a subring isomorphic to `M_K(F_2)`, with unit `e_{B'}`. The rule `E_{(p,i),(q,j)} ↦ v_{ij}E_pq` identifies `M_{3K}(F_2)` with `M_3(A)`.

`ι(x) := (1 − e_{B'}) I_3 + x` is an injective homomorphism `GL_{3K}(F_2) → GL_3(R)`. Its image lies in `G` because `GL_{3K}(F_2) = SL_{3K}(F_2)` is generated by elementary transvections, and each transvection goes into `G`:
- if `p ≠ q`: `ι(I + E_{(p,i),(q,j)}) = e_pq(v_{ij})`;
- if `p = q` and `i ≠ j`: choose `r ≠ p` and put `a = v_{ij}`, `b = v_{jj}`. Then `ab = a`, `ba = 0` and `aba = 0`. With `X = I + aE_pr` and `Y = I + bE_rp` one checks `XY = (I + abE_pp) YX`, so `[e_pr(a), e_rp(b)] = I + v_{ij}E_pp = ι(I + E_{(p,i),(p,j)})`. The convention is `[g,h] = ghg^{-1}h^{-1}`.

**Step 4: an F_{2^k}-structure.**
- Group the indices `1..K` into `K'` blocks `β` of size `k`, and identify `F_2^k` with `F_{2^k}`.
- Restriction of scalars gives a unital embedding `ρ: M_{3K'}(F_{2^k}) → M_{3K}(F_2)`. It sends the scalar `1` to the identity of each block, so `ρ(I + E_{(1,β),(2,β)}) = I + Σ_{i∈β} E_{(1,i),(2,i)}`.
- Put `S := SL_{3K'}(F_{2^k})`.
- `X_0 := ∏_β (I + E_{(1,β),(2,β)}) ∈ S` satisfies `ι ρ(X_0) = I_3 + e_{B'}E_12 = e_12(e_{B'})`.
- `t := I + E_{(1,β_0),(2,β_0)} ∈ S` is a transvection, non-central in `S` since `3K' ≥ 3`. It satisfies `ι ρ(t) = e_12(e_P)` with `P := ⊔_{i∈β_0} piece_i`, and `‖P‖ ≤ k/K = 1/K'`.

**Step 5: Lemma 1.4.**
- `ψ := χ∘ι∘ρ` is positive definite on `S` with `ψ(e) = 1`, since it is a character composed with a homomorphism.
- For `x ∈ S`, `ψ(x^{-1}tx) = χ(e_12(e_P))`, since `χ` is a class function on `G`.
- So if `|1 − χ(e_12(e_P))| < ε < 1`, (I1) gives `|1 − χ(e_12(e_{B'}))| < 9(2ε + 16/2^k)^{1/2}`.

**Step 6: the remainder.**
- `e_12(e_B) = e_12(e_{B'}) e_12(e_E)`, and `e_12(e_{B'})^{-1} = e_12(e_{B'})`.
- (I2) with `g = e_12(e_{B'})` and `h = e_12(e_B)` gives `|χ(e_12(e_B)) − χ(e_12(e_{B'}))|² ≤ 2|1 − χ(e_12(e_E))|`.

**Step 7: parameters.**
- Let `ε ∈ (0,1)` and take `η` from the hypothesis.
- Choose `k` with `16/2^k < ε` and `K' > 1/η`, put `K = kK'`, and choose `J > K/η`.
- Also require `J > 2K/β_B`, where `β_B := inf_μ μ(B) > 0`. This infimum is positive because every invariant measure of a minimal system has full support, `M(X,T)` is weak*-compact, and `μ ↦ μ(B)` is continuous for clopen `B`.
- Then `‖P‖ < η` and `‖E‖ < η`. Also `μ(B') ≥ β_B/2 > 0`, so `piece_1 ≠ ∅` and `P ≠ ∅`.
- Steps 5 and 6 give `|1 − χ(e_12(e_B))| < 9(3ε)^{1/2} + (2ε)^{1/2}`. Since `ε` is arbitrary, `χ(e_12(e_B)) = 1`.

**Step 8: simplicity.**
- Let `(π, H, ξ)` be the GNS triple of `χ`, and `g_0 = e_12(e_B)`.
- For every `k ∈ G`, `‖π(g_0)π(k)ξ − π(k)ξ‖² = 2 − 2 Re χ(k^{-1}g_0k) = 2 − 2 Re χ(g_0) = 0`.
- So `π(g_0) = 1`, and `ker π` is a normal subgroup containing the non-central element `g_0`. By (I3), `ker π = G` and `χ ≡ 1`. ∎

Remarks:
1. The hypothesis concerns only the root elements `e_12(e_P)`. Permutation matrices lie in `G` and `χ` is a class function, so every `e_ij(e_P)` gives the same values.
2. The same proof works for `EL_n(LC(X,F_q) ⋊ Z)/Z` with `n ≥ 3`. Replace `F_{2^k}` by `F_{q^k}`, and use (I3) for normal subgroups.
3. Only the uniform size `‖P‖` enters. A hypothesis for one invariant measure `μ` is stronger, so the theorem covers it.

## 3. Corollaries (proved)

**Corollary B (no measure-type characters).** Suppose `χ(e_12(e_P)) = F(μ(P))` for one invariant `μ` and a function `F` continuous at `0` with `F(0) = 1`. Then `χ ≡ 1`.
- In particular, no character of the form `g ↦ Φ(rk_μ(g − I))`, with `Φ` continuous at 0 and `rk_μ` a Sylvester rank function with `rk_μ(e_U) = μ(U)`, is nontrivial. Ara–Claramunt (arXiv:1902.06476) construct such rank functions.
- Elementary cross-check on `GL_2(F_2) ≅ S_3` over a clopen `W` with `x = Φ(μ(W))`: pairing `g ↦ x^{rank(g−1)}` with the sign character gives `(1−x)(1−2x)/6`, which is negative for `x ∈ (1/2,1)`.

**Corollary C (invariant random subgroups).** Let `ν` be an IRS of `G` with `ν{H : e_12(e_P) ∈ H} → 1` as `‖P‖ → 0`. Then `ν = δ_G`.
- `χ_ν(g) := ν{H : g ∈ H}` is a character, since `1_{g∈H}` is a matrix coefficient of `ℓ²(G/H)`.
- Theorem A gives `χ_ν ≡ 1`, so each `g` lies in `H` almost surely. `G` is countable, so `H = G` almost surely.

**Fact D.** Every finite-dimensional unitary representation of `G` is trivial. Its image is a f.g. linear group, hence residually finite (Mal'cev). The kernel is normal, and an infinite simple group is not residually finite. So every extreme character other than `1` comes from a II_1 factor representation.

## 4. Open: full character rigidity (claim `subshift-elementary-groups-are-character-rigid`)

Conjecture: every extreme character of `G_X` is `1` or `δ_e`. If true:
- operator-algebraic superrigidity: `L(G_X)` is the only II_1 factor generated by a unitary representation of `G_X`;
- `IRS(G_X) = {b δ_G + (1−b) δ_{1}}`, by the general principle in `research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md` §1. Its hypotheses are no proper finite-index subgroup and a character simplex spanned by `1` and `δ_e`. Both hold here once rigidity is known.

Attempts:
- **(a) Automatic continuity, after Dudko–Medynets Theorem 4.2.** Show that a non-regular extreme `χ` satisfies the hypothesis of Theorem A. Several pieces transfer:
  - positions are the points `a(y)` of the orbit of `y`;
  - the derived full group acts through `a ↦ aI_3 ∈ G`, which lies in `G` when `a` is a product of commutators, because `diag(c,1)` is a Whitehead product for a commutator `c`;
  - germ projections `R_Z` are well defined, since `aI_3` commutes with `G_V`-elements supported near a fixed point of `a`;
  - `R_Z` and `R_{Z'}` commute for `Z ≠ Z'`;
  - `T_Q` is central, because `G` is generated by elements supported off any given point.

  DM's endgame, their (4.3)–(4.10), fails here. It needs every group element to permute positions. In `G_X` a general `g` spreads the germ at `y` over `{T^j y : |j| ≤ w}`, so `π(g) R_Z π(g)^{-1}` is not some `R_{Z'}`. A new endgame is needed.
- **(b) Near-constancy on finite simple subgroups.** Gluck's bound shows that for any copy `S ≅ SL_n(F_{2^k})` in `G`, `χ` is within `8/2^k` of `λ_S` at every non-central element of `S`, where `λ_S` is the weight of the trivial representation. So `χ` is almost constant on large finite simple subgroups. Two problems:
  - The block structures carry remainders `E`. Controlling them is exactly the hypothesis of Theorem A: `K^0(X,T)` need not be divisible (Sturmian `K^0 = Z + αZ`), so exact divisions of `B` do not exist.
  - `λ_S > 0` does not by itself give a `G`-invariant vector, because `G` is not locally finite.

  Next idea: property (T) or an angle estimate between the fixed spaces of two such `S`'s containing the generators.
- **(c) Kirillov's Fourier trick** on `U = {I + rE_13 + sE_23} ≅ R^2`. The spectral measure on `R̂^2` is `EL_2(R)`-invariant, but `EL_2(R)` is far from transitive on `R^2 ∖ 0`. Every left ideal `I` gives an invariant subgroup `I^2`, so invariance alone does not force `δ_0` plus Haar.
- **(d) Lattice restriction.** `EL_3(F_2[u^{±1}]) ⊆ G` is an S-arithmetic lattice of higher rank. Character rigidity results there (Bader–Boutonnet–Houdayer–Peterson) would restrict `χ` on it, but its congruence characters would still have to be killed from outside. Not attempted.
- **(e) Limits along the note's finite models.** Limits of normalized irreducible characters of `GL_{3N}(F_2)` are convex combinations of `1` and `δ_e`, since models of `g ≠ 1` have rank `≥ cN`. This constrains only characters that arise as such limits.

## 5. Novelty and credit (bounded check)

The check was six web searches plus reading the introductions of Peterson–Thom (arXiv:1303.4007), Dudko–Medynets (2602.16885), Carderi–Thom (1603.00691) and the abstract of Schneider–Thom (2604.26104). It found no character classification for EL_n over crossed products, Steinberg algebras, or simple Kazhdan LEF groups.
- Theorem A is a short application of Carderi–Thom's Lemma 1.4, placed inside `G_X` by Kakutani–Rokhlin blocks. Credit Carderi–Thom and Gluck.
- The conceptual parallel is Schneider–Thom: the unit group of a non-discrete irreducible continuous ring has no nontrivial SOT-continuous unitary representation. Theorem A is the discrete, root-level analogue, and does not use the rank completion.
