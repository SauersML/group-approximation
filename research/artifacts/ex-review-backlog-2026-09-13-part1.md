# EX review, backlog, part 1: L²-acyclicity of Leavitt unit groups (2026-09-13)

Lane `ex-verify-backlog`. Index: `ex-review-backlog-2026-09-13.md`. Owning lane: `ex-lueck-approximation`.
- **Landings:** 912ea9ef17, afeb2d0090, fdf9d8f7f3, ffe5863325, 078c7a7529, e08c416389, 70cf39c9ff,
  296191d3d6, 5c1e12caf7, 14cc8e071b.
- **Artifacts:**
  - `leavitt-unit-l2-acyclicity-2026-09-12.md`: Theorems A and D, Corollaries B and C.
  - `leavitt-unit-l2-acyclicity-any-field-2026-09-12.md`: Theorem E.
  - `leavitt-path-unit-l2-acyclicity-2026-09-12.md`: Theorem F.

## 1.1 Theorem D, `l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers`: PASS after two corrections

**Re-derivation.**
- *Double complex.* `D_(t,p) = M ⊗_(ZG) (P_t ⊗ C_p(X))`, with `P_* -> Z` projective, diagonal action,
  and `M` flat over `Z`.
- *Columns.* `P_* ⊗ C_p(X)` is a projective resolution of the permutation module
  `C_p(X) = ⊕_[σ] Z[G/G_σ]`. By Shapiro, the column homology is `⊕_[σ] H_t(G_σ; M)`.
- *Rows.*
  - The untwisting `g ⊗ n ↦ g ⊗ g^(-1) n` is natural in `N`. So
    `M ⊗_(ZG) (P_t ⊗ C_*(X)) ≅ (M ⊗_(ZG) P_t) ⊗_Z C_*(X)` as complexes.
  - Flatness gives row homology `(M ⊗_(ZG) P_t) ⊗ H_p(X)`.
  - With `H_0(X) = Z` and `H_p(X) = 0` for `1 <= p <= m`, the only `E^2` term in total degree `n <= m`
    is `E^2_(n,0) = H_n(G; M)`.
  - A differential `d^k` leaving `(n,0)` lands in `(n-k, k-1)`. There `1 <= k-1 <= n-1 < m`, a zero
    row, and no differential enters row `0`. So `H_n(Tot) = H_n(G; M)` for `n <= m`.
- *Dimensions.*
  - For `H <= G`, flatness gives `Tor_t^(ZH)(N(G), Z) ≅ N(G) ⊗_(N(H)) Tor_t^(ZH)(N(H), Z)`, whose
    `N(G)`-dimension is `β_t^(2)(H)`.
  - Additivity and cofinality give dimension zero for arbitrary direct sums, subquotients and finite
    filtrations of dimension-zero modules.
  - Every `E^∞_(p,n-p)` with `n <= m` is a subquotient of such a sum.

**Finding (a). FAIL of wording: empty `X`.**
- For `X = ∅`, the hypothesis `H̃_d(X; Z) = 0` for `0 <= d <= m` holds; only `H̃_(-1)(∅) = Z` is nonzero.
- The stabilizer hypothesis is vacuous.
- For finite `G`, the conclusion `β_0^(2)(G) = 0` fails, since `β_0^(2)(G) = 1/|G|`.
- The proof uses `H_0(X) = Z`.
- **Fix:** `X` nonempty. No application is affected, since every frame complex contains the standard
  frame.

**Finding (b). GAP of scope: countability.**
- The node assumes `G` countable. But Theorem A allows any infinite ring, and Theorem E covers uncountable
  fields, so both apply Theorem D to uncountable groups.
- The proof never uses countability. Lück's survey states Theorems 1.11, 1.18 and 6.4 (i)--(ii) for
  arbitrary groups.
- **Fix:** "a group `G`".

Both fixes are landed on the claim node with this part.

**Citations, checked.** Source: `/scratch.global/sauer354/ex/ex-lueck-approximation/lit/math_0310489.txt`,
read with `grep -a`.
- Line 334: "Theorem 1.11. (Dimension function for arbitrary N(G)-modules)".
- Line 461: "Theorem 1.18 (Induction and dimension). Let i: H → G be an injective group homomorphism".
- Line 1877: the class `B_d`, (6.3).
- Line 1880: "Theorem 6.4. Let d be a non-negative integer or d = ∞. Then: (i) The class B∞ contains all
  inﬁnite amenable groups; (ii) If G contains a normal subgroup H with H ∈ Bd, then G ∈ Bd".
- The only countability hypotheses in the text are in 6.4 (vii) and §8. Neither is used.

## 1.2 Theorem A, `frame-acyclic-rings-have-low-degree-l2-acyclic-gl`: PASS

- **Lemma 2.1.**
  - `g e_i = e_i` for `i <= k` fixes the first `k` columns, so `g = [[I_k, b],[0, d]]`, and `g^(-1)` has
    the same shape.
  - `[[I,b],[0,d]] [[I,b'],[0,d']] = [[I, b' + b d'],[0, d d']]`. This gives `d d' = d' d = I` and shows
    that `g ↦ d` is a homomorphism.
  - Its kernel `U ≅ (M_(k x (r-k))(A), +)` is abelian, and infinite for infinite `A` and `1 <= k <= r-1`.
  - Cheeger--Gromov vanishing is 6.4 (i) and (ii) with `d = ∞`.
- **Lemma 2.2.**
  - A splitting `A^r = v_1 A ⊕ ... ⊕ v_k A ⊕ C` with `C ≅ A^(r-k)` gives `g in GL_r(A)` with `g e_i = v_i`,
    and the stabilizer is `g J g^(-1)`.
  - Faces are frames: the complement of `(v_1..v̂_i..v_k)` is `v_i A ⊕ C ≅ A^(r-k+1)`.
- **Range.** A `p`-simplex with `p <= r-3` has `k <= r-2` vectors.
- **Model tests** (artifact §7), re-checked:
  - `A = F_2`: `U` is finite and `β_0^(2) != 0`;
  - `SL_2(Z)`: `β_1^(2) = 1/12`, which lies outside the range.

## 1.3 Corollary B, `binary-leavitt-unit-group-is-l2-acyclic`: PASS

- **Hypothesis.** Khanh Corollary 4.3 for `R = L_(F_2)(1,2)`, `r >= 3`, through
  `binary-leavitt-frame-complexes-acyclic-citation`.
  - The second pass of `khanh-2609-08428-leavitt-gl-verified-2026-09-11.md` confirms field, algebra and
    ranks.
  - I did not re-read Khanh's text. §1.4 re-derives the frame-extension step independently, and that
    derivation also covers `F_2`.
- **Rank change.** `M_r(R) ≅ R` for every `r >= 1`, through a complete binary prefix code with `r` leaves.
  Each split adds one leaf. This agrees with `M_r(L(1,n)) ≅ L(1,n)` iff `gcd(r, n-1) = 1`.
- **`distinct_from` check.** Higman's group is acyclic but not L²-acyclic. Its presentation complex is
  aspherical with `χ = 1 - 4 + 4 = 1`, and `β_0^(2) = 0`, so `β_2^(2) >= 1`.

## 1.4 Corollary C, Theorem E, Theorem F: PASS

**Corollary C, `leavitt-tensor-host-unit-groups-are-l2-acyclic`.**
- Inputs: tensor-host Corollary 2.5, reviewed PASS in `review-boone-higman-leavitt-tensor-hosts-2026-09-12.md`
  §1.
- Rank change: `M_r(B ⊗ L) = B ⊗ M_r(L) ≅ B ⊗ L`.

**Theorem E, `leavitt-unit-groups-over-every-field-are-l2-acyclic`.**
- **(4.1).** Let `μ_i != μ_j` have length `<= D < M`.
  - Suppose `μ_i e^M f` were a proper prefix of `μ_j e^M f = μ_i e^M f v`. Then `1 <= |v| <= D < M`, and
    the letter `f` at position `|v| + 1` from the end would sit inside the terminal block `e^M`.
  - Equal lengths force `μ_i = μ_j`.
- **Lemma 4.1_K.**
  - `a_i γ_j` is a combination of paths, since `β* γ_j` is `0` or a suffix.
  - The words of `(a_i γ_j) t_j`, with `t_j = e^(j(L+1)) f`, have lengths in pairwise disjoint windows.
  - So `P_i = a_i x_0` has nonzero coefficients on distinct words.
  - With `x = x_0 e^M f`, `η_i* a_i x = c_i != 0`.
- **Frame extension, re-derived without Khanh's text.**
  - Take frames `W_i` with complements `C_i ≅ S^(q_i)`, `q_i >= 2`. Let `ρ_i : S^r -> S` have kernel
    `W_i` and section `σ_i`, and let `Φ : S ≅ S^r`. Then `a_i = ρ_i Φ(1) != 0`.
  - Put `v = Φ(x)`, `y_i = a_i x` and `u_i = c_i^(-1) η_i*`. Then `u_i y_i = 1`, and
    `S^r = W_i ⊕ vS ⊕ σ_i(ker u_i)`, because `v - σ_i(y_i) in W_i`.
  - `ker(η*·) = (1 - η η*) S ≅ S^(|η|) ≅ S^(q_i - 1)`. So `(v, W_i)` is a simplex.
  - Coning from `v` kills cycles of dimension `d <= r-3`; the case `d = 0` uses the augmentation.
  - Only `u_i y_i = 1` and the size of the kernel are used, as the artifact says.

**Theorem F, `leavitt-path-unit-groups-with-trivial-unit-class-are-l2-acyclic`.**
- **The rank change.** From `[1] = 0` and Ara--Goodearl--Pardo Proposition 2.2 we get `L ≅ L²`, a unital
  Leavitt family, and `M_r(L) ≅ L`.
- **Nonzero kernels.**
  - `u y = 1` splits `L = yL ⊕ ker(u·)`, so `[ker u] = 0`.
  - Replacing `u_i` by `u'_i = e_0 u_i` and `X` by `X' = X f_0` keeps `u'_i a_i X' = 1` and puts
    `a_i X f_1 != 0` in the kernel.
  - A nonzero kernel of class `0` is `≅ L ≅ L^(q-1)`, and then the extension computation above applies.
- **Inputs established.** Simultaneous strong division is PASS in `review-backlog-2026-09-12.md` §14.
  The AGP import (`agp-purely-infinite-simple-rings-have-cancellative-projectives`) and the Abrams--Aranda
  Pino import are established, but I did not re-read either source.
- **Example.** For `N_E = [[2,3],[1,2]]`, `I - N_E^t` has determinant `-2`, and its image contains
  `(1,1)`. So `K_0 = Z/2` and `[1] = 0`.
- Theorem E over an uncountable `K` depends on correction 1.1(b).

## 1.5 The lane's other established nodes: PASS

**`binary-leavitt-unit-tracial-rank-functions-are-mixtures`.** Conditional on
`binary-leavitt-full-character-simplex`, which is a `requires` edge.
- For `0 < α < 1`, `triv` and `λ` are disjoint, because `ℓ²G` has no invariant vectors. So the von Neumann
  algebra is `C ⊕ L(G)`.
- The central projections put both summand vectors in the cyclic subspace, and range projections are
  computed componentwise.
- Part 2:
  - the limit is a positive-definite class function;
  - the moments of `σ_n(A)^*σ_n(A)` converge;
  - portmanteau applies to `(s², ∞)` away from atoms, and to the closed set `{0}` for the kernel bound.

**`lamplighter-cube-embeds-in-binary-leavitt-unit-group`.**
- `t = (0w↦00w, 10w↦01w, 11w↦1w)` lies in `F`. For `n >= 1`, `t^n[10] = [0^n 1]` and
  `t^(-n)[10] = [1^(n+1) 0]`, and these cylinders are pairwise disjoint.
- With `a` the swap `[100] ↔ [101]`, `⟨a, t⟩ ≅ Z/2 ≀ Z`.
- The cube comes from the disjoint cylinders `[00], [01], [1]`.

**`binary-leavitt-unit-group-has-irrational-l2-betti-numbers`.** Exact induction preserves kernel dimension.
- **Wording note, no verdict change.** "The strong Atiyah conjecture then predicts only rational
  dimensions" is loose.
  - The strong conjecture assumes bounded orders of finite subgroups (Lück, book, Conjecture 10.2), so it
    predicts nothing for `G`.
  - What `G` refutes is the rationality form of Atiyah's question.
- The node already says there is no new mechanism.

**`decidable-groups-have-right-computable-l2-betti-numbers`.**
- `a_n = (Tr ⊗ τ)((1 - S/c)^n)` decreases to `μ({0})`.
- The determinant conjecture gives `μ_(A^*A)((0,ε]) <= k log c' / log(1/ε)`, and rescaling by `N²`
  transfers the bound to `S`.
- Credit to Löh--Uschold and Groth, as recorded.

**`binary-leavitt-unit-group-has-undecidable-l2-kernel-problem`.** Conditional on the Grabowski import, which
I did not re-read.
- `H_3, H_4 <= V`: conjugates supported in disjoint cylinders commute.
- `Z[G] = ⊕_i Z[H_4] g_i` as left `Z[H_4]`-modules, so `MY = 0` splits componentwise.

**`kun-thom-wreath-is-l2-acyclic`.** A finite-index infranormal subgroup is normal. So `[G:Γ] = ∞`, and the
lamp group is infinite, normal and abelian.

**`kun-thom-wreath-and-double-have-fixed-price-one`.** Conditional on
`fpbs-elementary-matrix-semidirect-fixed-price-one`.
- In stage two, `x'_ij(a)` commutes with the infinite `x_ij(F_q[x_1..x_d]) ⊆ Γ`.
- In stage three, the added generators normalize `EL_r(F_q[x^±])'`.
- "Neither is residually finite" follows from nonsoficity.

**`kun-thom-double-has-vanishing-first-l2-betti-number`.** Gaboriau's inequality `β_1^(2) <= C - 1`.

## 1.6 Open nodes of the lane: status correct

- `kun-thom-double-is-l2-acyclic` and `decidable-group-with-noncomputable-l2-betti-number` have no route.
- `determinant-counterexample-via-noncomputable-l2-betti-number` requires the second of these, so it does
  not fire into `determinant-conjecture-counterexample-exists`.
