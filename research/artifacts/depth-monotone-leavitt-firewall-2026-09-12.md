# Depth-monotone Leavitt units: a stably finite firewall for mismatched transvections

Lane `w6-mismatch-c3` (WAVE 6, multi-letter factors; verifier `w4-vf-gate`). Main read at `d0f2b3f64`.

Nodes:
- `depth-monotone-leavitt-subalgebras-are-stably-finite` (Sections 1 and 2);
- `depth-monotone-configurations-cannot-force-ternary-minus-one` (Section 3);
- an Attempts entry on `ternary-leavitt-units-have-no-weakly-finite-representation`.

Decision status: passed by `w4-vf-gate` (Sections 30.1 and 30.2 of
`research/artifacts/gk-vf-gate-verification-2026-09-12.md`). Both claims are ESTABLISHED.

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

## 3. The firewall

Notation from `research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md`:
`ε_- = 2(1 - [z])`, `S_- = ε_- F_3[G]`, and the reflection ideal `J_omega` of its Section 1 (the subscript
there is the stage index, unrelated to the weight `ω`).

**Theorem 3.** Let `Γ_0 <= G` contain `z`. Suppose `u Γ_0 u^(-1) ⊆ H^ω_≤` or `u Γ_0 u^(-1) ⊆ H^ω_≥` for some
`u in G` and some weight `ω`. Then `ε_- F_3[Γ_0]` has a nonzero weakly finite image, i.e.
`1 ∉ J_omega(ε_- F_3[Γ_0])`. So no finite certificate for `ternary-anti-central-summand-has-no-weakly-finite-image`
has all its group elements (entries of the pairs, of their defects, and of the ideal multipliers) in `Γ_0`.

*Proof.*
- Conjugation by `u` is a ring automorphism of `F_3[G]` fixing `[z]`, so take `u = 1`.
- **Case `≤`.** `φ` of Corollary 2 extends linearly to a unital ring map `Φ : F_3[Γ_0] -> Q` with
  `Φ([z]) = -1`. Then `Φ(ε_-) = 2·2 = 1` in characteristic three, so `Φ` restricts to a unital ring map
  `ε_- F_3[Γ_0] -> Q` (`ε_-` is the unit of that corner).
- `Q` is weakly finite, so Theorem 1(b) of that artifact gives `Φ(J_omega) = 0`, while `Φ(1) = 1 != 0`.
- **Case `≥`.** The same, with `g -> φ(g*)` into `Q^op`.
- A certificate with all group elements in `Γ_0` is a derivation of `1 in J_omega` inside the subring
  `ε_- F_3[Γ_0]`, since the stages use only the displayed identities. QED

**Relation to the sofic firewall.** By Corollary 2(b) every such `Γ_0` is sofic, so Theorem 3 also follows
from `linear-sofic-group-algebra-is-stably-finite`, since the anti-central summand is a nonzero corner of a
stably finite algebra. What is new is the placement: the configurations below lie in locally residually
finite subgroups, and `φ` is an explicit model.

**Relation to `w6-mismatch-c2`.** `research/artifacts/mismatched-factor-graph-of-groups-firewall-2026-09-12.md`
(Corollary 2.2) realizes `a = T_(0,1)` and `c = T_(1,00)` over `F_2` in a weakly finite rank model of a graph of
locally finite groups. That model keeps `rk(D) != 0`, but only relations inside its vertex groups hold. Theorem 3
is complementary: every relation of the actual subgroup holds, but `D -> 0` (Remark 3.2).
- `ac` also has infinite order over `F_3`. The formulas in the proof of that artifact's Proposition 2.1(1) for
  `ac - 1` on the points `q_n`, `r_m` have all coefficients `+1`, so they hold over `F_3`.
- Modulo lower levels, `(ac - 1)^2` maps the level-`l` pair to the level-`(l-1)` pair by the matrix `[[1,1],[0,1]]`.
  So `ac - 1` is nilpotent on each level space, with unbounded index.
- Suppose `(ac)^m = 1`, and let `3^k` be the largest power of three dividing `m`. Then `U = 1 + (ac - 1)^(3^k)`
  is unipotent on each level space with `U^(m / 3^k) = 1`. Its order is prime to three, so `U = 1`. Then
  `(ac - 1)^(3^k) = 0` on every level space, a contradiction. So `ac` has infinite order.
- So `H^1_≤` over `F_3` holds a non-locally-finite subgroup together with all its relations, and it still has a
  weakly finite model with `z -> -1`.

**What `H^1_≤` contains.**
- `z`, the sign group `E` (units `Σ ε_μ s_μ t_μ`), the level part `∪_n Sym({0,1}^n)` of `V`, and all of
  `(R^1_0)^x = ∪_n GL_(2^n)(K)` (Section 2, Remarks).
- Every transvection `T_(σ,κ)(λ)` with `|σ| <= |κ|`:
  - all level root elements at every depth, in particular `T_(0,1)(λ)`, `T_(1,0)(λ)`, and
    `w_0 = T_(0,1)(1) T_(1,0)(-1) T_(0,1)(1) = s_0 t_1 - s_1 t_0`, with `w_0^2 = z`;
  - the depth-decreasing `T_(1,00)(λ)`, `T_(0,11)(λ)`, `T_(1,000)(λ)`, and so on.
- The mismatched pair and every product of these.

**Task 1: the mismatched pair.** Put `A = s_0 t_1` and `B = s_1 t_00`, so `T_(0,1) = 1 + A` and
`T_(1,00) = 1 + B`. In `R`:
- `A^2 = 0` and `B^2 = 0`;
- `AB = s_0 t_00`, `BA = s_1 t_10`, `ABA = s_0 t_10` and `BAB = s_1 t_000`;
- `(AB)^n = s_0 t_(0^(n+1))` and `(BA)^n = s_1 t_(1 0^n)`, nonzero for every `n` (the contracting partial maps
  `0^(n+1) y -> 0y` and `1 0^n y -> 1y`);
- `T_(0,1) T_(1,00) = 1 + s_0 t_1 + s_1 t_00 + s_0 t_00`.

Every term has degree `<= 0`. So `N_A = φ(A)` and `N_B = φ(B)` satisfy all of these in the weakly finite
algebra `Q`, where `z -> -1`. Any identity derived in `W` from group relations among elements of `H^1_≤`
(root squares, commutators with level roots at both depths, conjugation by `E` and level `V`) holds in this
model. So that computation, confined to those elements, cannot produce a one-sided invertible matrix with
nonzero defect, nor a contradiction with `z = -1`.

**Remark 3.2 (the two-root defect).** In the three-leaf frame, `D = N_23 N_12` in `F_3[G]` evaluates to
`e_23 e_12 = 0` in `M_3(R) ≅ R`. Suppose `x_12(1), x_23(1) in Γ_0` and `u Γ_0 u^(-1) ⊆ H^ω_≤`, and put
`Φ([g]) = φ(u g u^(-1))`. Then `Φ(D) = φ(u e_23 u^(-1)) φ(u e_12 u^(-1)) = φ(u e_23 e_12 u^(-1)) = 0`, and the
same holds on the `≥` side. With the code `(0,10,11)`, `e_12 = s_0 t_10` and `e_23 = s_10 t_11` both
lie in `R^1_≤`.
- So these models violate form (iv) (`D_rho != 0`) of that artifact's Theorem 3. They give no firewall for the
  defect form `ternary-weakly-finite-representations-kill-two-root-defect`.
- They do show that the implication "`D` killed ⟹ trivial" (its Theorem 2) cannot be run inside `H^1_≤`:
  `φ` kills `D` and is injective.
- Whether `H^1_≤` has a weakly finite representation with `z -> -1` and `D != 0` is not decided here.

## 4. What an obstruction must contain

**Lemma 4.1 (Kraft).** Let `g in V` be given by prefix codes `(c_i) -> (d_i)`, so `g = Σ_i s_(d_i) t_(c_i)`.
Let `p in (0,1)` solve `p^a + p^b = 1` and let `μ_ω` be the Bernoulli measure with `μ_ω[w] = p^(ω(w))`.
These are equivalent:
- (i) `g in R^ω_≤`; (ii) `g in R^ω_≥`;
- (iii) `ω(d_i) = ω(c_i)` for all `i`;
- (iv) `g` preserves `μ_ω`.

*Proof.*
- (iii) ⟹ (i), (ii): every term is weight-level.
- (i) ⟹ (iii). The `R_n`-component of `g` is `Σ s_(d_i) t_(c_i)` over the `i` with `c(d_i) - c(c_i) = n`. It
  is nonzero when that index set is nonempty, because `π` of it sends the constant function `1` to the
  indicator of `∪ [d_i]`. So (i) forces `ω(d_i) <= ω(c_i)` for all `i`. The codes partition `X`, so
  `Σ_i p^(ω(c_i)) = 1 = Σ_i p^(ω(d_i))`, and `p < 1` gives `p^(ω(d_i)) >= p^(ω(c_i))` termwise. So equality
  holds termwise. (ii) ⟹ (iii) is the same with the inequalities reversed.
- (iii) ⟺ (iv): `g` maps `[c_i v]` onto `[d_i v]`, and `μ_ω[d_i v] / μ_ω[c_i v] = p^(ω(d_i) - ω(c_i))`. QED

**Consequences.**
- For `θ = 1`, `V ∩ R^1_≤` is the level part of `V`, which is locally finite.
- A non-level element such as `x_0` (`00 -> 0`, `01 -> 10`, `1 -> 11`) lies in no `H^ω_≤` and no `H^ω_≥`: its
  pieces change weight by `-a`, `0` and `+b`.
- `G = ⟨V, 1 + s_00 t_01⟩` (`leavitt-prime-field-units-generated-by-v-and-one-transvection`), and
  `1 + s_00 t_01` lies in `R^1_0`. So the group elements of a certificate must generate a subgroup that no
  conjugation puts inside any `H^ω_≤` or `H^ω_≥`. Candidates are elements of `V` that are weight-level for no `ω`,
  and transvection sets such as the four-element set below. They escape without conjugation only, and no
  conjugation invariant is proved (see Open).

**Depth vectors.** For `λ != 0` put `v(T_(σ,κ)(λ)) = c(σ) - c(κ) in Z^2`. The element `λ s_σ t_κ` is
homogeneous of degree `v` and nonzero, so with `a = 1`, `b = θ`: `T in H^θ_≤` iff `v_0 + θ v_1 <= 0`, and
`T in H^θ_≥` iff `v_0 + θ v_1 >= 0`.

| transvection | `v` | in `H^θ_≤` iff | in `H^θ_≥` iff |
|---|---|---|---|
| `T_(0,1)` | `(1,-1)` | `θ >= 1` | `θ <= 1` |
| `T_(1,0)` | `(-1,1)` | `θ <= 1` | `θ >= 1` |
| `T_(1,00)` | `(-2,1)` | `θ <= 2` | `θ >= 2` |
| `T_(00,1)` | `(2,-1)` | `θ >= 2` | `θ <= 2` |
| `T_(0,10)` | `(0,-1)` | every `θ` | no `θ` |
| `T_(10,0)` | `(0,1)` | no `θ` | every `θ` |

- `{T_(0,1), T_(1,00)} ⊆ H^θ_≤` for `1 <= θ <= 2`.
- `{T_(0,1), T_(1,00), T_(00,1)} ⊆ H^2_≤`, the golden-ratio weight (`p + p^2 = 1`).
- `{T_(0,1), T_(1,0), T_(00,1)} ⊆ H^1_≥`.
- `{T_(0,1), T_(1,0), T_(1,00), T_(00,1)}` lies in no `H^θ_≤` and no `H^θ_≥`: the level pair forces `θ = 1`,
  and at `θ = 1` the last two have degrees `-1` and `+1`.
- **Escaping without conjugation is not enough.** `{T_(10,0), T_(0,10)}` lies in no `H^θ_±`. But the element
  `u in V` with `0 -> 00`, `10 -> 01`, `11 -> 1` gives `u T_(10,0) u^(-1) = T_(01,00)` and
  `u T_(0,10) u^(-1) = T_(00,01)`, both in `R^1_0`.

**Open.**
- Is `⟨E, level V, T_(0,1), T_(1,0), T_(1,00), T_(00,1)⟩` conjugate into some `H^ω_±`, or sofic for another
  reason?
- For elements of `V`, slopes at fixed points are conjugation invariants
  (`research/artifacts/thompson-v-rank-models-torsion-spectra-2026-09-12.md`, Section 3). An invariant of that
  kind for units of `R` that detects the depth vectors above would turn Section 4 into a criterion. None is
  proved here.
- Does `H^1_≤` carry a weakly finite representation with `z -> -1` and `D != 0`?
