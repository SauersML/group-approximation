---
rg: 2
id: planted-lifts-defeat-hilbert-level-gaussian-soficity-proof
kind: route
title: Plant a ball of the coset space in a null region of the lift, read off the Gaussian Bernoulli shift, and separate the planted part from L^2(M) by marginal uniform integrability
target: planted-lifts-defeat-hilbert-level-gaussian-soficity
requires:
  - kun-thom-nonsofic-wreath
  - gaussian-theorem-c-for-ad-sigma-is-equivalent-to-ccr
  - zero-entropy-compressors-preserve-fixed-algebra
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

We use the notation of the claim. Norms on `H_n` are
`‖ξ‖² = |Y|^(-1) Σ_(a,b) |ξ(a,b)|²`, where we write `Y = Y_n`. For
`x ∈ M_Y`, this is `tr(x*x)`. The action is
`(Ad p) ξ (a,b) = ξ(p^(-1)a, p^(-1)b)` for `p ∈ Sym(Y)`, which is conjugation
by the permutation matrix. Each `Ad s_n(g)` is an orthogonal operator on
`H_n`, so `A(g) = [Ad s_n(g)]` is a well-defined orthogonal operator on
`H = ∏_U H_n`. The subspace
`H^eq(s) = {ξ : A(gh)ξ = A(g)A(h)ξ for all g, h}` is closed. Since
`A(g)^(-1) = [Ad s_n(g)^(-1)]` and `A(g^(-1))` agree on `H^eq(s)`, the
subspace is `A(G)`-invariant, and `A` restricts to a representation on it.

For `x ∈ M` with a bounded lift `(x_n)`, the class `[x_n] ∈ H` does not
depend on the lift. Here `sigma(g) x sigma(g)^(-1) = [Ad s_n(g) x_n]`. So
`M → H` is isometric for `‖·‖_2`, and `L^2(M)` is its closure. Because
`sigma` is a homomorphism, `L^2(M) ⊆ H^eq(s)` with `A|_(L^2(M)) = Ad sigma`.

## Step 1: planting (claim part (1))

Since `sigma` is trace-faithful and `G` is infinite, `|Y_n| → ∞`. Write
`Omega = ⊔_i G/H_i` as a union of at most countably many orbits. It is enough
to plant each orbit with each multiplicity into disjoint regions. At stage
`n` only finitely many orbits (the first `R_n` of them) and multiplicities up
to `R_n` are used. So we describe one orbit `G/H` with base point `o` and
multiplicity one. The general case is the disjoint union of such regions, and
the total size is still `o(|Y_n|)`.

Enumerate `G = {g_1 = e, g_2, ...}` and put `F_R = {g_1, ..., g_R}` and
`B_R = F_R · o ⊆ G/H`. Choose `R_n → ∞` so slowly that
`|B_(R_n)| ≤ |Y_n|^(1/2)`. Fix an injection `ι_n : B_(R_n) → Y_n` and put
`P_n = ι_n(B_(R_n))`.

For `g ∈ G` define a partial map `φ_g : P_n → P_n` by
`ι_n(ω) ↦ ι_n(gω)` whenever `ω, gω ∈ B_(R_n)`, and a partial map
`ψ_g = s_n(g)` on `{a ∉ P_n : s_n(g)a ∉ P_n}`. Both are injective. Their
domains are disjoint (inside `P_n`, resp. outside it), and so are their
ranges. So `φ_g ∪ ψ_g` is a partial bijection of `Y_n`. Extend it
arbitrarily to a bijection `s'_n(g)`.

Now `s'_n(g) a = s_n(g) a` unless `a ∈ P_n ∪ s_n(g)^(-1)P_n`. So

```text
d_Hamming(s'_n(g), s_n(g)) ≤ 2|P_n| / |Y_n| ≤ 2 |Y_n|^(-1/2) → 0
```

for every `g`. Hence `[s'_n] = [s_n]` in `∏_U Sym(Y_n)` modulo Hamming-null
sequences. So `sigma_(s') = sigma_s`. The permutation matrices
`s'_n(g), s_n(g)` are at `‖·‖_2`-distance at most
`(2 d_Hamming)^(1/2) → 0`, so `sigma` does not change as a map into `U(M)`
either.

For finitely supported `f` on `G/H`, with `supp f ⊆ B_(R_n)`, put

```text
v_n(f) = |Y_n|^(1/2) Σ_(ω ∈ B_(R_n)) f(ω) δ_(ι_n ω, ι_n ω) ∈ H_n .
```

Then `‖v_n(f)‖² = Σ |f(ω)|² = ‖f‖²`. Fix `g` and `f` with support in
`F_K · o`. For `n` large, `g F_K ⊆ F_(R_n)` and `F_K ⊆ F_(R_n)`. So for
`ω ∈ supp f`, both `ω` and `gω` lie in `B_(R_n)`, hence
`s'_n(g) ι_n ω = ι_n(gω)`. Since `Ad p δ_(a,a) = δ_(pa,pa)`, we get

```text
Ad s'_n(g) v_n(f) = v_n(λ(g) f)      exactly, for all n ≥ n(g, f),
```

where `λ` is the quasi-regular representation on `ℓ^2(G/H)`. Define
`V f = [v_n(f)]`. It is linear and isometric on finitely supported
functions, so it extends to an isometry `V : ℓ^2(G/H) → H`. We have
`A'(g) V = V λ(g)` on a dense set, hence everywhere. So
`A'(gh) V = V λ(gh) = A'(g)A'(h) V`, that is, `V(ℓ^2(G/H)) ⊆ H^eq(s')`, and
`V` is equivariant. Every `v_n(f)` is supported on `P_n × P_n`, and so is
every vector of the image, in the ultraproduct sense: it is a limit of
classes of vectors supported there. Replacing the pair space by `ℓ^2(Y_n)`
with weight `1/|Y_n|` and `δ_(ι ω)` by `|Y_n|^(1/2)δ_(ι ω)` gives the same
statement for the permutation representation itself. This proves (1).

## Step 2: HGS fails (claim part (2))

Apply Step 1 with `Omega = G/Gamma` and `m = 1`, and let
`K = V(ℓ^2(G/Gamma)) ⊆ H^eq(s')`. It is `A'`-invariant and separable, and
`A'|_K ≅ λ_(G/Gamma)`. The Gaussian action of `λ_(G/Gamma)` is the shift on
`R^(G/Gamma)` with the product of standard Gaussians: the canonical basis
`δ_(gGamma)` is orthonormal and permuted by `G`, so the linear observables
`X_(gGamma)` are i.i.d. `N(0,1)` and permuted. The observable
`X_Gamma = X_(δ_Gamma)` is fixed by `Gamma`. Pick `u ∈ N ∖ Gamma`; this exists
because `Gamma` is not normal, so `N ≠ Gamma`. Then `u·X_Gamma = X_(uGamma)`
is independent of `X_Gamma`, so it is not equal to it. The algebra
`L^∞^Gamma` therefore contains `1_(X_Gamma > 0)` but is not `N`-invariant.
Since it is fixed by every conjugate of `Gamma` once it is `G`-invariant
(Step 5 below), it is not `G`-invariant.

By Theorem C (verbatim in the artifact) the Gaussian action is not sofic. If
it were a factor `Z → R^(G/Gamma)` of a sofic `Z`, then
`1_(X_Gamma>0) ∈ L^∞(Z)^Gamma` would be moved by `u`, contradicting Theorem C
for `Z` (again by Step 5). Corollary D is the same statement with base
`(R, N(0,1))`.

This holds for every lift `s` of every sofic `sigma`. So if `G` has a sofic
approximation, HGS fails; if it has none, HGS is vacuous. This proves (2).

## Step 3: compressor entropy (claim part (3))

Let `F_Gamma` be the `Gamma`-fixed sigma-algebra of `N(0,1)^(G/Gamma)`. By
Step 2 it is not `G`-invariant. Since `Gamma` is infranormal, `G` is
generated by `Gamma` and `S = P_Gamma = {s : sGamma s^(-1) ≤ Gamma}`. If every
`s ∈ S` had `F_Gamma` in its Pinsker algebra, then (ZE3) of
`zero-entropy-compressors-preserve-fixed-algebra` would make `F_Gamma`
invariant under `⟨Gamma, S⟩ = G`, which is false. So some compressor has
positive entropy relative to a set of `F_Gamma`. For the Theorem E pair,
(ZE4) there identifies the substitutions `s_ij` as a sufficient family, so
one of them works. Orthogonality to `L^2(M)` is Step 4(iii).

## Step 4: the MUI part (claim part (4a), and orthogonality)

For `ξ = [ξ_n] ∈ H` and `δ > 0` put

```text
ρ_ξ(δ) = lim_U  max_(E ⊆ Y_n, |E| ≤ δ|Y_n|)  max( ‖1_(E×Y) ξ_n‖ , ‖1_(Y×E) ξ_n‖ ).
```

Here `‖1_(E×Y)ξ_n‖² = |Y|^(-1) Σ_(a∈E) r_n(a)`. The vector `ξ` is MUI
exactly when `ρ_ξ(δ) → 0` as `δ → 0`, which is the usual small-set form of
uniform integrability of `r_n` and `c_n`. By Minkowski's inequality,
`ρ_(ξ+η) ≤ ρ_ξ + ρ_η` and `ρ_ξ ≤ ‖ξ‖`. Also, `ρ` does not change when
`ξ_n` is altered by a norm-null sequence, so `ρ` is well defined on `H`.

(i) *MUI vectors form a closed subspace, invariant under every `A(g)`.* The
subspace property follows from subadditivity. Closedness: if `ξ^k → ξ`, then
`ρ_ξ(δ) ≤ ρ_(ξ^k)(δ) + ‖ξ − ξ^k‖`. Invariance: `Ad p` permutes rows and
columns, so it maps sets of size `≤ δ|Y|` to sets of the same size, and
`ρ_(A(g)ξ) = ρ_ξ`.

(ii) *Lift independence.* Let `s, s'` be equivalent lifts, fix `g`, and put
`D_n = {a : s_n(g)^(-1) a ≠ s'_n(g)^(-1) a}`, so that `|D_n| / |Y_n| → 0`.
The vector `(Ad s_n(g) − Ad s'_n(g)) ξ_n` vanishes off
`(D_n × Y) ∪ (Y × D_n)`. So its norm is at most

```text
‖1_(D×Y) Ad s_n(g)ξ_n‖ + ‖1_(Y×D) Ad s_n(g)ξ_n‖ + (same for s')
   ≤ 4 · max_(|E| ≤ |D_n|) max(‖1_(E×Y)ξ_n‖, ‖1_(Y×E)ξ_n‖),
```

because `1_(D×Y) Ad p ξ = Ad p (1_(p^(-1)D × Y) ξ)`. For MUI `ξ`, the
ultralimit is `≤ 4ρ_ξ(δ)` for every `δ > 0`, hence `0`. So `A(g) = A'(g)` on
MUI vectors. Since `A(h)ξ` is again MUI, `A(g)A(h)ξ = A'(g)A'(h)ξ`, and
therefore `H^eq(s) ∩ MUI = H^eq(s') ∩ MUI =: H^eq_MUI`, with the same
representation.

(iii) *Planted vectors are orthogonal to MUI vectors.* Let `ξ_n` be supported
on rows in `P_n`, with `|P_n| / |Y_n| → 0`, and let `η` be MUI. Then
`|⟨ξ_n, η_n⟩| ≤ ‖ξ_n‖ ‖1_(P_n×Y) η_n‖`, and the ultralimit is
`≤ ‖ξ‖ ρ_η(δ)` for every `δ`, hence `0`. This passes to the closed span, so
`V(ℓ^2(Omega)^(⊕m)) ⊥ H^eq_MUI`.

(iv) *`L^2(M)` is MUI.* If `‖x_n‖_∞ ≤ C`, then `r_n(a) = (x_n x_n*)_(aa) ≤ C²`
and `c_n(b) = (x_n* x_n)_(bb) ≤ C²`, so `ρ_x(δ) ≤ C δ^(1/2)`. Now apply (i).

So `L^2(M) ⊆ H^eq_MUI ⊥ (planted part)`. In particular, planting creates no
element of `M` and no enemy, which is claim part (3). It also shows that the
planted Gaussian Bernoulli shift of Step 2 is invisible to every argument
that sees only `L^2(M)`.

## Step 5: Gaussian criterion and representation Theorem C (claim part (4b), (4c))

We use these standard facts.

- **(G)** For a real orthogonal representation `π` on a separable `K` there
  is the Gaussian action `G ↷ (Omega_K, μ_K)` and an equivariant linear
  isometry `ℓ : K → L^2_R(Omega_K)`. Its image consists of jointly
  Gaussian centered variables and generates the sigma-algebra. For vectors
  `v_i` and a finite `F ⊆ G`, the law of `(ℓ(π(g)v_i))` is the centered
  Gaussian law with covariance `⟨π(g)v_i, π(h)v_j⟩`.
- **(S1)** Factors of Păunescu-sofic actions are sofic. A `G`-invariant
  subalgebra gives a trace-preserving inclusion of crossed products;
  restrict the embedding.
- **(S2)** Finite and countable products of sofic actions are sofic. Tensor
  the diagonal-plus-permutation embeddings and pass to the inverse limit.
  Finite actions with trivial `G`-action are sofic.
- **(S3)** Let `A` be compact metrizable. The set of shift-invariant
  measures `ν` on `A^(G×ℕ)` for which the shift is sofic is weak-star
  closed. This follows from the microstate description of Păunescu-soficity
  (Păunescu arXiv:1002.0605; Elek--Lippner), whose conditions are open in
  finitely many marginals, together with a diagonal argument. It is (C3) of
  `hyperlinear-action-distills-to-stabilizer-coset-bernoulli-proof` in its
  sofic form.

We apply (S3) after composing coordinates with `arctan`, so real-valued
processes with convergent finite-dimensional laws are covered.

**Fixed-algebra lemma.** If `A = L^∞(Z)^Gamma` is `G`-invariant, then `A` is
fixed by `N`. Indeed, for `f ∈ A`, `g ∈ G` and `γ ∈ Gamma`, we have
`g^(-1)f ∈ A`, so `γ g^(-1) f = g^(-1) f`, that is, `(gγg^(-1)) f = f`. The
conjugates of `Gamma` generate `N`. The same holds for `L^2(Z)^Gamma`, since a
`Gamma`-invariant `L^2` function is the `L^2`-limit of its truncations, which
lie in `A`.

**(4b), ⇒ direction.** If `Omega_K` is a factor of a sofic `Z`, then
`ℓ(K) ⊆ L^2(Omega_K) ⊆ L^2(Z)` is an embedding into a sofic Koopman
representation. So `K ∈ K_sof`.

**(4b), ⇐ direction.** Suppose `π ≺ L^2(X)` with `X` sofic.

*Reduction to centered functions.* Put `X' = X × {0,1}`, with `G` trivial on
`{0,1}` and the uniform measure there. `X'` is sofic by (S2), and
`f ↦ f ⊗ ε` with `ε(j) = (−1)^j` embeds `L^2(X)` equivariantly into
`ρ := L^2_0(X')`. So `π ≺ ρ`.

*Gaussian(ρ) is sofic.* Let `{f_i}` be bounded real functions dense in
`L^2_0(X')`. On the diagonal action `X'^m`, which is sofic by (S2), consider
the equivariant factor map

```text
Φ_m(x)_((g,i)) = m^(-1/2) Σ_(k ≤ m) f_i(g^(-1) x_k).
```

For finite `F ⊆ G × ℕ`, the vector `(Φ_m)_F` is `m^(-1/2)` times a sum of `m`
i.i.d. bounded centered vectors. Their covariance is
`⟨ρ(g)f_i, ρ(h)f_j⟩`. By the multivariate central limit theorem the laws of
`Φ_m` converge in finite-dimensional distributions to the law of
`(ℓ(ρ(g)f_i))`. By (G) and density of `{f_i}`, that process generates the
Gaussian action of `ρ`. By (S1) and (S3) it is sofic.

*Gaussian(π) is sofic.* Let `{v_i}` be dense in `K`. Weak containment
`π ≺ ρ`, in its matrix-coefficient form, gives vectors `w_i^(k)` in
`ρ^(⊕∞)` with

```text
⟨ρ^∞(g) w_i^(k), w_j^(k)⟩ → ⟨π(g) v_i, v_j⟩
```

for all `g, i, j` as `k → ∞` (diagonal enumeration). The processes
`(ℓ(ρ^∞(g) w_i^(k)))_(g,i)` are factors of
`Omega_(ρ^(⊕∞)) = Omega_ρ^ℕ`, which is sofic by (S2). They are centered
Gaussian with converging covariances, so they converge in finite-dimensional
laws to the Gaussian process of `π`. By (S1) and (S3), `Omega_π` is sofic.

**(4c) Representation Theorem C.** Let `π ∈ K_sof`. By (4b), `Omega_π` is
sofic. By Theorem C, `L^∞(Omega_π)^Gamma` is `G`-invariant, so by the lemma
`L^2(Omega_π)^Gamma` is `N`-fixed. For `v ∈ π^Gamma`, the vector `ℓ(v)` lies
in `L^2^Gamma`. So it is `N`-fixed, and since `ℓ` is an equivariant
isometry, `v ∈ π^N`.

**Consequence for enemies.** Let `x ∈ C_sigma` be an enemy. Its real and
imaginary parts lie in `C_sigma`, which is a `*`-algebra because
`sigma(Gamma)` consists of unitaries, and one of them is an enemy. For a
self-adjoint enemy `x`, `x ∈ K_x^Gamma ∖ K_x^N`, so `K_x ∉ K_sof` by (4c).
Hence "`K_x ∈ K_sof` for all `x ∈ C_sigma`" implies no enemy, and so CCR.
By (4b) this is the same as Gaussian soficity of every `K_x`, the input
isolated in `gaussian-theorem-c-for-ad-sigma-is-equivalent-to-ccr`.

## Step 6: flat vectors are in K_sof (claim part (4), flat case)

Let `f_n = |Y_n|^(1/2) ξ_n`, viewed as a function on `Y_n²` with the uniform
probability `μ_n`. Then `‖f_n‖_(L^2(μ_n)) = ‖ξ_n‖`. Suppose `|f_n|²` is
uniformly integrable along `U`, that is, `ξ` is flat.

*Flat implies MUI.* We have `r_n(a) = E_(μ_n)(|f_n|² | a)`, and conditional
expectations of a uniformly integrable family are uniformly integrable.

*The Loeb pair action.* Let `(L, λ)` be the Loeb space of `(Y_n², μ_n)`.
The maps `T_g = [s_n(g) × s_n(g)]` are measure-preserving on `L`. Their
defects `T_g T_h ≠ T_(gh)` live on sets of density at most
`2 d_Hamming(s_n(g)s_n(h), s_n(gh)) → 0`, so `T` is an action on the measure
algebra. A uniformly integrable, `L^2`-bounded internal sequence has a
standard part `F ∈ L^2(L)` with `⟨F, F'⟩ = lim_U ⟨f_n, f'_n⟩`. Also
`T_g F` is the standard part of `f_n ∘ (s_n(g) × s_n(g))^(-1)`, which is the
flat vector `A(g)ξ`. So `ξ ↦ F` intertwines the cyclic representation of `ξ`
with a cyclic subrepresentation of the Koopman representation of `T`.

*Restrict to a separable factor.* Let `B` be the sigma-algebra generated by
the `G`-translates of countably many level sets of `F`. The factor `(L, B)`
is sofic. Send `d ∈ L^∞(B)` to a diagonal lift in `∏_U D_(Y_n²)`, and `g` to
the permutation matrices `s_n(g) ⊗ s_n(g)`. For `g ≠ e`,

```text
|τ(d u_g)| ≤ ‖d‖_∞ · (fixed-point density of s_n(g) on Y_n)² → 0,
```

by trace-faithfulness. So the generated von Neumann algebra is a
trace-preserving copy of `L^∞(B) ⋊ G`. That is a Păunescu embedding. Hence
the cyclic representation of `ξ` lies in the Koopman representation of a
sofic action, and it is in `K_sof`.

The identity `1 ∈ M` is MUI but not flat: its entries are `|Y|^(1/2)` on a
diagonal of density `1/|Y|`. Diagonal elements are handled by the Loeb action
on `Y` instead. Elements that are neither flat nor built from
finite-propagation diagonal and permutation pieces are what the claim calls
the mesoscopic, infinite-hull part. It is the same class that
`hamming-enemies-escape-finite-hull-pair-loeb-scales` isolates.

## Step 7: sharpness (claim part (5))

`Gamma` is Kazhdan, hence finitely generated, say by a finite set `S`. Fix
`u ∈ N` and put

```text
E_n = { a ∈ Y_n : s_n(σ)a = a for all σ ∈ S,  and s_n(u)a ≠ a }.
```

Consider the graph on `E_n` with edges `a — s_n(u)a` (when both ends lie in
`E_n`). Its maximum degree is `2`, and it has no loops, so it is
`3`-colourable. Let `A_n` be a largest colour class. Then `|A_n| ≥ |E_n|/3`
and `A_n ∩ s_n(u)A_n = ∅`.

Let `A = [A_n]` in the Loeb space of `(Y_n, uniform)`, with the Loeb action
`[s_n]`. Every `γ ∈ Gamma` is a word in `S^(±1)`, and `s_n(γ)` agrees with the
corresponding product off a null set. So `A` is `Gamma`-invariant. The
sigma-algebra generated by `G·A` is separable and invariant, and its factor
is sofic, exactly as in Step 6 with `Y_n` in place of `Y_n²`. By Theorem C
and the fixed-algebra lemma, `T_u 1_A = 1_A`. But `A ∩ T_u A = [∅]`. So
`λ(A) = 0`, and `lim_U |E_n| / |Y_n| ≤ 3λ(A) = 0`.

If instead a positive-density set of points looked `Gamma`-fixed and
`u`-moved, `1_A` would be a diagonal projection in `L^∞(Y) ⊆ M`. It would
commute with `sigma(Gamma)` (a diagonal `d` commutes with a permutation
matrix `p` exactly when `d ∘ p = d`) and would not be fixed by `Ad sigma(u)`.
That is a diagonal enemy. So planting has exactly two regimes: density
`o(1)`, where it always succeeds (Step 1) but is orthogonal to `L^2(M)`
(Step 4), and positive density, where Theorem C forbids it.

## Step 8: the killed class and calibration

*The failing step.* Every argument of the following form fails at step (b):

- (a) represent a vector of `L^2(M)`, or of any subrepresentation, by an
  asymptotically equivariant sequence in `ℓ^2(Y_n)` or `ℓ^2(Y_n²)`;
- (b) produce sofic microstates for its Gaussian suspension from equivariance
  alone.

This covers Gaussian microstates `R^(Y_n)` driven by `s_n`, "the Gaussian of
the sofic representation `∏_U ℓ^2(Y_n)`", and Hayes-type Gaussian models over
the sofic approximation. The vector
`ξ = [|Y_n|^(1/2) δ_(p_n,p_n)]`, where `p_n = ι_n(Gamma)`, satisfies (a)
exactly for the planted lift `s'`, and its Gaussian suspension is not a factor
of a sofic action by Step 2. Such an argument therefore proves a false
statement. The correct form must use `ρ_ξ(δ) → 0` (MUI), or the operator
norm, at step (b). By Step 4(ii), MUI is also exactly what makes the argument
independent of the lift, which any statement about `sigma` must be.

*Calibration.*

- Groups whose generalized Bernoulli shifts are all sofic, such as amenable
  groups: planting produces only sofic Gaussians there, so nothing false
  follows, as it should.
- If `Gamma` is normal, `N = Gamma` and the planted `Gamma`-fixed vector is
  `N`-fixed, so there is no contradiction.
- At the Kun--Thom pair, planting plus Theorem C reproduces Corollary D.
  Step 7 reproduces Theorem C at the level of points.
- The flat case (Step 6) agrees with
  `hamming-enemies-escape-finite-hull-pair-loeb-scales`: Loeb pair spaces of
  finite measure are exactly where Theorem C already applies to enemies.

*What stays open.* Whether `K_x ∈ K_sof` for non-flat MUI
`x ∈ sigma(Gamma)' ∩ M`, and the weaker (MUI-C), namely that
`Gamma`-invariant vectors of `H^eq_MUI` are `N`-invariant. Planting cannot
touch either statement.
