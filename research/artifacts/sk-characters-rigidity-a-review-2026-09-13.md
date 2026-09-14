# sk-characters-rigidity-a: review of character rigidity for G_X (sk-characters-rigidity-b, d78467369d)

2026-09-13, reviewer lane sk-characters-rigidity-a.
- I re-derived every step by hand before reading any other verdict.
- The only computation was fetching the Larsen–Tiep source on MSI.

Target: Theorem R. For every infinite minimal Cantor system X, every character of `G = EL_3(LC(X,F_2) ⋊ Z)` is `a·1 + (1−a)δ_e`.
- Artifacts: `research/artifacts/sk-characters-rigidity-b-proof-2026-09-13-part1.md` and `-part2.md`.
- Claim: `subshift-elementary-groups-are-character-rigid`.
- Route: `subshift-elementary-groups-character-rigid-proof`.

## Verdict: PASS

There is no ERROR and no GAP. The four notes below concern wording and have no effect on correctness.

| Item | Verdict |
|---|---|
| Import (I1), Larsen–Tiep Theorem A | quote VERIFIED against the source |
| Lemma 1 (i)–(iii), nesting, passages | PASS |
| Lemma 1′ (support ≥ ⌊H/L⌋) | PASS |
| Lemma 2 (two points generate G) | PASS |
| Lemma 3 (class size, degree, Larsen–Tiep) | PASS |
| Lemma 4 (constancy on L_y ∖ 1) | PASS |
| Lemma 5 (p_A is central) | PASS |
| Lemma 6 (a)–(g), including (d) and the Bessel step | PASS |
| §6 assembly, corollaries R1–R4 | PASS; R2 re-derived in §6 below |

## 1. Import (I1)
- **Source.** The arXiv:2403.09046v1 e-print (`lt3_arxiv.tex`, 14 Mar 2024), fetched on MSI on 2026-09-13. The abstract page gives the title "Uniform Character Bounds for Finite Classical Groups". Source lines 139–148:
  > "There exists an absolute constant $c>0$ such that for all finite quasisimple groups $G$ of Lie type, irreducible characters $\chi$ of $G$, and elements $g\in G$, we have $|\chi(g)| \le \chi(1)^{1 - c\frac{\log |g^G|}{\log |G|}}$."
- **Scope** (l.136–137): "all finite quasisimple groups $G$ of Lie type, (i.e. $G=[G,G]$ and $G/\ZB(G)$ is a finite simple group of Lie type)". For N ≥ 3, `GL_N(F_2) = SL_N(F_2)` is simple of type A_{N−1}(2), so it is covered. The constant `c` is absolute and does not depend on N.
- **Support** (l.156–157): "the codimension of the eigenspace of g of maximal dimension". This is part 1's definition. Lemma 3 does not use Larsen–Tiep's support, since it computes `log|g^G|` directly.
- **Not checked:** the journal version.

## 2. Lemma 1(iii) and Lemma 1′
- **A nontrivial component.** `h ∈ L_m ∖ 1` has some tower `C_0` of `𝒫_m` with `h[C_0] ≠ 1`.
- **Visit times are constant on each base (N1).** By induction on the nesting, every level of `𝒫_n` lies in a level of `𝒫_m`. So for a tower `C′` of `𝒫_n`, the set of times `c` with `T^cC′ ⊆ C_0` is the same at every point of `C′`. Part 1 uses this without saying it.
- **Counting passages.**
  - Returns to `B_n ⊆ B_m` start `𝒫_m`-towers, so the segment `[0,H_{C′})` is a concatenation of full `𝒫_m`-towers.
  - Each window of length `L` contains a visit to `C_0`, and the `⌊H/L⌋` disjoint windows give that many distinct passage starts.
- **Block structure.** `h[C′]` is the block diagonal sum of the blocks `h[C]` over passages `(C′,c)`, from `E^C_{ab} = Σ E^{C′}_{c+a,c+b}`.
- **Rank count.** For `λ ∈ F̄_2`, `h[C_0] − λ ≠ 0`: equality would give `λ ∈ F_2^× = {1}` and `h[C_0] = 1`. So each `C_0`-block adds at least 1 to the rank of `h[C′] − λ`. Then `dim ker(h[C′]−λ) ≤ 3H_{C′} − #passages`, so `supp(h[C′]) ≥ ⌊H_{C′}/L⌋`.
- **Why every tower matters.** The bound holds for EVERY tower `C′` of `𝒫_n`. Lemma 4 needs this, because the nontrivial tensor factor may sit on any tower.
- **Model test.** Over `F_q` with q > 2 the λ-step fails, since a block can be a scalar `λI ≠ I`. This agrees with part 2 §8.

## 3. Lemma 3, the Larsen–Tiep application
- **Centralizer.**
  - For one eigenvalue with Jordan partition μ, `dim C = Σ_k (μ′_k)² ≤ μ′_1·Σ_k μ′_k`, which is (eigenspace dimension)·(multiplicity). Summing over eigenvalues, `dim_{F̄_2} C_{M_N}(x) ≤ (N − supp x)·N`.
  - The centralizer over `F_2` is the solution space of the same linear system, so it has the same dimension, and `|C_{G_N}(x)| ≤ 2^{N(N−supp x)}`.
- **Class size.**
  - `|GL_N(F_2)| = 2^{N²}∏_{j≤N}(1−2^{−j}) > 2^{N²}·0.288 > 2^{N²}/4`. So `log_2|x^G| ≥ N·supp(x) − 2`, while `log_2|G| ≤ N²`.
  - If `supp ≥ αN` and `N² ≥ 4/α`, the ratio `log|x^G|/log|G|` is at least `α/2`.
- **Degree.**
  - A nontrivial irreducible representation of the simple group is faithful on the elementary abelian radical U of rank `⌊N²/4⌋`.
  - The characters of U that occur have trivial common kernel, so they span `Û`, and at least `⌊N²/4⌋` of them occur.
  - This bound is weak but enough.
- **Combine.** `|χ(x)|/χ(1) ≤ χ(1)^{−c·log|x^G|/log|G|} ≤ χ(1)^{−cα/2} ≤ ⌊N²/4⌋^{−cα/2}`, since `χ(1) > 1` and the exponent is negative.
- **Use in Lemma 4.**
  - Take `α = 1/(4L)` and `N = 3H_{C′}`. Then `⌊H/L⌋ ≥ H/L − 1 ≥ 3H/(4L)` once `H ≥ 4L`.
  - `δ_α` decreases in N, and `min H → ∞` by Lemma 1(ii).
  - The character ratio of a tensor product is the product of the factor ratios, each at most 1.
  - So `|χ(h) − c^{(n)}_triv| ≤ (1 − c^{(n)}_triv)·δ → 0`.

## 4. Lemma 6(d): tower groups at small sets lie in L_{y*}
- **Orthogonality of corners.**
  - `ε_{ab}ε′_{a′b′}` is supported on `T^a(V ∩ T^{a′−b}V′)`, with `|a′−b| ≤ 2w`.
  - The hypothesis "`T^aV ∩ T^bV′ = ∅` for `|a|,|b| ≤ w`" is exactly "`V ∩ T^jV′ = ∅` for `|j| ≤ 2w`".
  - So `ψ_V(M_d)ψ_{V′}(M_d) = 0` in both orders. Then `H_V` and `H_{V′}` commute elementwise and meet trivially.
- **Containment `ε_{ab} ∈ A(𝒫_n)` (N2).** Part 2 gives only "never enters B_n", so here is the full reason. Take n large, so that `T^bV` is a union of levels, and let `D = T^cC ⊆ T^bV` be a level. Then `u^{a−b}e_D = E^C_{c+(a−b),c}` exactly when `0 ≤ c+(a−b) < H_C`.
  - Suppose `a ≥ b` and `c + k = H_C` for some `1 ≤ k ≤ a−b`. Then `T^kx ∈ B_n` for `x ∈ D`. But `T^kx ∈ T^{b+k}V` with `|b+k| ≤ w`, which is disjoint from `B_n`. Contradiction.
  - Suppose `a < b` and `c < b−a`. Then `T^{−c}x ∈ C ⊆ B_n`. But `T^{−c}x ∈ T^{b−c}V` with `a < b−c ≤ b`. Contradiction.
  - So `ε_{ab} = Σ_{D ⊆ T^bV} E^C_{c+(a−b),c} ∈ A(𝒫_n)`, and `ψ_V(M_d) ⊆ M_3(A(𝒫_n))`.
  - `H_V ⊆ GL_3(A(𝒫_n)) = L_n ⊆ L_{y*}`, because the inverse of `I_3 − ψ_V(I_d) + ψ_V(B)` has the same form.
- **The nested system (N3).**
  - The condition `B_n ∩ T^aV_k = ∅` holds automatically for large n: the union of the towers is clopen and misses `y*`.
  - Lemma 4 holds for every nested system, so `χ_2` vanishes on this `L_{y*} ∖ 1`.

## 5. Lemma 6(a)–(c) and the Bessel step (e)–(g)
- **(a)** For small V:
  - `g e_V = Σ γ^{pq}_a e_{T^aV}u^aE_pq` with `γ ∈ F_2`, because `f_a e_{T^aV}` has `(f_a∘T^a)|_V` constant. The same holds for `e_V g` (i = 0).
  - Triviality means `γ = δ_{pq}δ_{a0}`, by uniqueness of coefficients. A nonempty clopen `V′ ⊆ V` has the same γ, so it is trivial iff V is.
  - A finite partition of X into small sets exists, since T has no periodic points and X is compact. Since `g ≠ 1`, one of them is nontrivial.
- **(b)** Suppose g commutes with every `e_ij(e_V)`.
  - Comparing entries of `g e_VE_ij = e_VE_ij g` gives `g_{pi}e_V = 0` for `p≠i`, `e_Vg_{jq} = 0` for `q≠j`, and `g_{ii}e_V = e_Vg_{jj}`.
  - In the last identity the `u^a`-coefficients with `a ≠ 0` live on the disjoint sets `T^aV` and `V`, so both vanish.
  - So `g e_V = diag(ε_i)e_V`. Since g is invertible, `g(e_VE_ii) = ε_ie_VE_ii` forces `ε_i = 1`. The rows are handled the same way, so V is trivial.
- **(c)**
  - `ψ_V` is multiplicative and injective, since `0 < |a′−b| ≤ 2w` gives disjoint supports.
  - The entries of `g^{−1}e_VE_ijg` are sums of terms `f u^a e_V f′u^b = γ·ε_{a,−b}`, because f and `f′∘T^{−a}` are constant on `T^aV`.
  - So `g^{−1}xg ∈ H_V`, since its inverse has the same form, and `x = I + ε_{00}E_ij ∈ H_V`.
- **(e)** V is uncountable because X has no isolated points.
  - Choose K points inductively with pairwise disjoint orbit segments of radius w.
  - Shrink to sets `V_k` whose towers are pairwise disjoint, with `y*` outside all of them. Each `V_k` is small and, by (a), nontrivial.
- **(f)**
  - `⟨v_k,v_l⟩ = χ(g_l^{−1}g_k) = χ(g^{−1}ygy^{−1})`, where `y = x_l^{−1}x_k`.
  - Expanding both sides, `g^{−1}ygy^{−1} = (g^{−1}x_lg·x_l)(g^{−1}x_kg·x_k)`. The expansion uses `x_k^{−1} = x_k`, `x_l^{−1} = x_l`, and that `g^{−1}x_kg ∈ H_{V_k}` commutes with `x_l ∈ H_{V_l}`.
  - The second factor is 1 iff `x_k` commutes with g. The product lies in the direct product `H_{V_l}×H_{V_k}`, so it is ≠ 1, and by (d) it lies in `L_{y*} ∖ 1`.
- **(g)** `⟨ξ,v_k⟩ = \overline{χ(g)}`, and Bessel's inequality gives `K|χ(g)|² ≤ 1` for every K.

## 6. Lemmas 2 and 5, §6, corollaries
- **Lemma 2.**
  - The top levels of `𝒫_n` are `T^{−1}B_n`.
  - A level of `𝒫′_m` inside `T^{−1}B_n` is not a top level of `𝒫′_m`, because `T^{−1}B_n ∩ T^{−1}B′_m = ∅`. The argument for `u^{−1}` is the same with base levels.
  - The subring argument needs three distinct indices, which n = 3 provides.
- **Lemma 5.**
  - `A = ⋃A_n ⊆ L_y` and `τ(p_{A_n}) = (1+(|A_n|−1)c)/|A_n| → c`.
  - τ is faithful (part 1 §0, through cyclicity of ξ). So `p_{L_y} ≤ p_A` with equal traces forces `p_{L_y} = p_A = p_{L_{y′}}`.
  - By Lemma 2, `p_A` is then G-invariant, hence central.
- **§6.**
  - Since `p_A` is central, `χ_2` is a normalized positive definite class function.
  - `χ_2(h) = (χ(h)−c)/(1−c) = 0` on `L_y ∖ 1` for every y and every nested system, because `c = χ(e_12(e_P))` depends on neither.
- **R2, re-derived.**
  - Let `σ = ∫^⊕ λ_{G/H}dν(H)` and `F(H) = δ_H`. Then `⟨σ(g)F,F⟩ = ν{H ∋ g}`.
  - The central trivial part of `χ_ν` gives a σ-invariant vector v with `‖v‖² = ⟨v,F⟩ = a`.
  - A σ-invariant field is supported on subgroups of finite index, so on `{H = G}`, and Cauchy–Schwarz gives `a² ≤ a·ν{G}`.
  - Since `ν{H ∋ g} = a` for `g ≠ 1`, we get `ν{G} = a`, and `H = 1` almost surely on the complement (G is countable).
- **Sanity check.** Theorem R implies that G is simple. For a normal subgroup `N`, `1_N` is a positive definite class function. It must be constant on `G ∖ 1`, so `N = 1` or `N = G`. The proof never uses simplicity, so nothing is circular.

## 7. Notes on wording
- **N1.** Lemma 1(iii) should say that visit times to `C_0` are constant on each base `C′`.
- **N2.** Lemma 6(d) should give the two-case tower-boundary argument of §4.
- **N3.** The condition "take a nested system at `y*` with `B_n ∩ T^aV = ∅`" holds automatically for large n, and the text should say so.
- **N4.** R5 can add that simplicity of `G_X` also follows from Theorem R (§6).

## 8. Model tests (the reviewer's own)
- **Both extremes pass.** `δ_e` is the case `a = 0`, and `1` is the case `a = 1`.
- **Periodic X.** Lemma 1(ii) fails, and congruence characters exist, as §8 of part 2 says.
- **Derived topological full group.** The fixed-point characters decay only in the moved fraction, not in absolute support, so the analogue of Lemma 3 fails. This is consistent with the Dudko–Medynets characters.

## Status
- PASS on second-lane review:
  - `subshift-elementary-groups-are-character-rigid` and its route `subshift-elementary-groups-character-rigid-proof`;
  - `subshift-tower-unit-group-characters-are-constant` (Lemmas 1–4);
  - `subshift-elementary-groups-have-trivial-irs`.
- VERIFIED against the source: the `larsen-tiep-uniform-character-bound` quote.
- Not re-searched: novelty (the lane's bounded search stands) and the journal version of Larsen–Tiep.
