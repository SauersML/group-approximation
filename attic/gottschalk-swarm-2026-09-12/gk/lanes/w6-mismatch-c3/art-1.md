# Depth-monotone Leavitt units: a stably finite firewall for mismatched transvections

Lane `w6-mismatch-c3` (WAVE 6, multi-letter factors; verifier `w4-vf-gate`). Main read at `d0f2b3f64`.

Nodes:
- `depth-monotone-leavitt-subalgebras-are-stably-finite` (Sections 1 and 2);
- `depth-monotone-configurations-cannot-force-ternary-minus-one` (Section 3);
- an Attempts entry on `ternary-leavitt-units-have-no-weakly-finite-representation`.

Decision status: proved on paper here, landed **OPEN** until `w4-vf-gate` passes it.

## 0. Setting and summary

- `R = L_K(1,2)` over a field `K`, with `t_i s_j = δ_ij` and `s_0 t_0 + s_1 t_1 = 1`. For a word
  `μ = μ_1 ... μ_k` put `s_μ = s_(μ_1) ... s_(μ_k)` and `t_μ = t_(μ_k) ... t_(μ_1)`, so `t_μ s_μ = 1`.
  Every product of generators is `0` or some `s_μ t_ν`, so these span `R`.
- `T_(σ,κ)(λ) = 1 + λ s_σ t_κ` for incomparable words `σ, κ`. `G = L_(F_3)(1,2)^x`, `z = -1`.
- **Weights.** Fix reals `a = ω(0) > 0` and `b = ω(1) > 0`, and put `ω(μ) = a·#_0(μ) + b·#_1(μ)`. Only the
  ratio `θ = b/a` matters. Define
  - `R^ω_≤ = span{ s_μ t_ν : ω(μ) <= ω(ν) }` and `R^ω_≥ = span{ s_μ t_ν : ω(μ) >= ω(ν) }`;
  - `H^ω_≤ = (R^ω_≤)^x` and `H^ω_≥ = (R^ω_≥)^x`, subgroups of `R^x`.
- **Grading.** With `deg s_0 = (1,0)`, `deg s_1 = (0,1)` and `deg t_i = -deg s_i`, the defining relations are
  homogeneous, so `R = ⊕_(n in Z^2) R_n` with `R_n = span{ s_μ t_ν : c(μ) - c(ν) = n }`, where
  `c(μ) = (#_0 μ, #_1 μ)`. Then `R^ω_≤ = ⊕_(ω·n <= 0) R_n`. For `θ = 1` these are the nonpositive and
  nonnegative parts of the usual `Z`-grading `deg s_i = 1`.

Summary:
1. `R^ω_≤` and `R^ω_≥` are stably finite subalgebras of `R` for every weight (Theorem 1). `R` is not, and
   the pair `t_0 s_0 = 1 != s_0 t_0` needs one factor from each side.
2. Over a finite field `H^ω_≤` and `H^ω_≥` are locally residually finite, hence sofic, and embed in the units
   of a weakly finite algebra with `z -> -1` (Corollary 2).
3. `H^1_≤` contains `T_(0,1)`, `T_(1,00)`, their product, every level transvection at every depth, the sign
   group `E`, the level part of `V` and every depth-decreasing transvection. So the mismatched pair is not
   an escaping configuration. No finite certificate for the target has its group elements in a subgroup
   conjugate into some `H^ω_≤` or `H^ω_≥` (Theorem 3).
4. These models send the two-root defect `D` to `0` whenever both roots lie in the subalgebra. They firewall
   the anti-central form of the target and leave the defect form (iv) untouched (Remark 3.2).
5. `V ∩ R^ω_≤` is the part of `V` preserving a Bernoulli measure (Lemma 4.1). Section 4 records which
   transvection sets escape every `H^ω_±` without conjugation, and what is still undecided.

## 1. The function representation and stopping partitions

**The representation.** Let `X = {0,1}^N` and `C = C(X,K)`, the locally constant functions. Put
`(S_i f)(x) = f(y)` if `x = iy` and `0` otherwise, and `(T_i f)(y) = f(iy)`. Then `T_i S_j = δ_ij` and
`S_0 T_0 + S_1 T_1 = id`, so `s_i -> S_i`, `t_i -> T_i` defines `π : R -> End_K(C)` with
`(π(s_μ t_ν) f)(x) = f(νy)` if `x = μy`, and `0` if `x` is not in `[μ]`.

**Lemma 1.1 (faithful).** `π` is injective.

*Proof.*
- Let `x != 0`. Refining with `s_μ t_ν = s_(μ0) t_(ν0) + s_(μ1) t_(ν1)`, write `x` as a combination of
  terms `s_μ t_ν` with all `|ν| = N`. Since `Σ_(|ν|=N) s_ν t_ν = 1`, `x = Σ_ν (x s_ν) t_ν`, so some
  `y = x s_ν` is nonzero. It is a combination `Σ λ_μ s_μ` (use `t_ν' s_ν = δ_(ν'ν)` for `|ν'| = |ν|`).
  `π(y) = π(x) S_ν`, so it suffices to show `π(y) != 0`.
- Choose `μ_0` of maximal length `L` with `λ_(μ_0) != 0`, an integer `M > L`, the word `w = 1 0^M 1` and
  `f = 1_[w]`. Evaluate `π(y) f` at `x = μ_0 w y'`. A term `λ_μ s_μ` contributes only if `μ` is a prefix of
  `x` with `|μ| <= L`, i.e. a prefix of `μ_0`.
  - `μ = μ_0` contributes `λ_(μ_0) f(w y') = λ_(μ_0)`.
  - A proper prefix of length `j < L` contributes `λ_μ f(u w y')` with `u` nonempty and `|u| = L - j <= L`.
    Membership in `[w]` needs letters `2, ..., M+1` of `u w y'` to be `0`, but letter `L - j + 1`, which lies
    in that range, is the first letter `1` of `w`. So the contribution is `0`.
- Hence `(π(y) f)(x) = λ_(μ_0) != 0`. QED

**Stopping partitions.** For `r > 0` and `x in X` let `p_r(x)` be the shortest prefix `u` of `x` with
`ω(u) >= r`; for `r <= 0` put `p_r(x) = ∅`. Let `F_r` be the functions constant on each cylinder `[p_r(x)]`.
- Stopping prefixes have length at most `⌈r / min(a,b)⌉`, so `dim F_r < ∞`.
- `p_r(x)` is a prefix of `p_r'(x)` when `r <= r'`, so `F_r ⊆ F_r'`.
- For `r >= ω(w)` every piece `[p_r(x)]` lies inside `[w]` or is disjoint from it, because weights increase
  strictly along prefixes. So `C = ∪_r F_r`.

**Lemma 1.2 (invariance).** If `ω(μ) <= ω(ν)` and `ω(μ) <= r`, then `π(s_μ t_ν) F_r ⊆ F_r`.

*Proof.* Let `f in F_r`, `g = π(s_μ t_ν) f`, and `p_r(x) = p_r(x') = u`. We show `g(x) = g(x')`.
- **Membership in `[μ]`.** If `μ` is a prefix of `x`, then `ω(μ) <= r` and strict monotonicity make `μ` a
  prefix of `u`, hence of `x'`. By symmetry `x in [μ]` iff `x' in [μ]`. If neither holds, both values are `0`.
- **Otherwise** `x = μy` and `x' = μy'`, and `u = μv` with `v = p_(r-ω(μ))(y) = p_(r-ω(μ))(y')`.
  - Let `v'` be the shortest prefix of `y` with `ω(v') >= r - ω(ν)`. Since `r - ω(ν) <= r - ω(μ)`, `v'` is a
    prefix of `v`, so it is also the shortest such prefix of `y'`.
  - `p_r(νy)` is a prefix of `ν` if `ω(ν) >= r`, and equals `ν v'` otherwise. In both cases
    `p_r(νy) = p_r(νy')`.
  - So `g(x) = f(νy) = f(νy') = g(x')`. QED

## 2. Stable finiteness

**Theorem 1.** For every field `K` and every weight `ω`, `R^ω_≤` and `R^ω_≥` are stably finite unital
subalgebras of `L_K(1,2)`.

*Proof.*
- **Subalgebras.** `R^ω_≤ = ⊕_(ω·n <= 0) R_n` is closed under products and contains `1`. The `K`-linear
  anti-automorphism `*` with `s_i* = t_i` respects both relations and sends `s_μ t_ν` to `s_ν t_μ`, so it maps
  `R^ω_≤` onto `R^ω_≥`.
- **The target algebra.** Let `Q = ∏_(k>=1) End_K(F_k) / ⊕_(k>=1) End_K(F_k)`.
- **The map.** For `x in R^ω_≤` let `x_k = π(x)|_(F_k)` if `F_k` is `π(x)`-invariant, and `0` otherwise, and
  let `φ(x)` be the class of `(x_k)_k`. Writing `x` as a combination of terms with `ω(μ) <= ω(ν)`, Lemma 1.2
  makes `F_k` invariant for all `k` beyond the largest `ω(μ)`.
- **Ring map.** For `x, y`, the coordinates `(xy)_k = x_k y_k` and `(x+y)_k = x_k + y_k` hold for all large `k`,
  and `φ(1) = 1`.
- **Injective.** If `φ(x) = 0`, then `π(x)` vanishes on `F_k` for all large `k`, so on `C`, so `x = 0` by
  Lemma 1.1.
- **`Q` is stably finite.** `M_n(Q) = ∏_k M_n(End F_k) / ⊕_k M_n(End F_k)`. If `AB ≡ I`, then `A_k B_k = I`
  for all large `k`, so `B_k A_k = I` because `F_k` is finite-dimensional, so `BA ≡ I`.
- **Conclusion.** Subrings of stably finite rings are stably finite, so `R^ω_≤` is. `R^ω_≥` is
  anti-isomorphic to it, transpose identifies `M_n(A^op)` with `M_n(A)^op`, and the implication
  `AB = I ⟹ BA = I` passes to opposite rings. QED

**Corollary 2 (units).**
- (a) `φ : H^ω_≤ -> Q^x` and `x -> φ(x*) : H^ω_≥ -> (Q^op)^x` are injective group homomorphisms into units of
  weakly finite algebras. Both send `z = -1` to `-1`.
- (b) If `K` is finite, every finitely generated subgroup of `H^ω_≤` or `H^ω_≥` is residually finite. So both
  groups are locally residually finite, hence sofic.

*Proof of (b).* Let `Γ_0 = ⟨g_1, ..., g_m⟩ <= H^ω_≤`. By Lemma 1.2 some `k_0` makes every `F_k`, `k >= k_0`,
invariant under all `π(g_i^(±1))`. So `Γ_0` acts on each such `F_k` by invertible maps, and
`Γ_0 -> ∏_(k>=k_0) GL(F_k)` is injective by Lemma 1.1. Each `GL(F_k)` is finite. For `H^ω_≥` use the group
isomorphism `g -> (g*)^(-1)` onto `H^ω_≤`. Finitely generated residually finite groups are sofic, and
soficity is local. QED

**Remarks.**
- For `θ = 1` put `R^1_0 = ⊕_(n_0 + n_1 = 0) R_n = span{ s_μ t_ν : |μ| = |ν| }`, the degree-zero part of the
  `Z`-grading. It is the locally finite union of the `M_(2^n)(K)`, while `R^1_≤` contains `t_0` with
  `t_0^n != 0` for all `n` and is not locally finite. Theorem 1 extends finiteness past the degree-zero part.
- `t_0 in R^ω_≤` has the right inverse `s_0`, which lies only in `R^ω_≥`. So Theorem 1 is sharp in the sense
  that the failure of weak finiteness in `R` needs factors from both sides.
