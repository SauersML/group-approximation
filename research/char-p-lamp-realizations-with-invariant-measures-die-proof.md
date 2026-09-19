---
rg: 2
id: char-p-lamp-realizations-with-invariant-measures-die-proof
kind: route
title: "Explicit Reiter functions make the lagged tail relation Borel amenable; CFW passes this to the lifting subgroup's orbits; averaging over the fibres of an invariant measure pushes it to the affine action; freeness on Haar makes EL_2(F_p[t^±]) amenable, contradicting relative (T)"
target: char-p-lamp-realizations-with-invariant-measures-die
requires:
  - elementary-linear-semidir-pair-relative-t
---

Notation is as in the target. `σ` is the left shift on `C = {0,1}^N`. For a Borel probability
vector `f` on a countable set, `‖·‖` is the `ℓ^1` norm.

## Imported, verbatim

G. Elek and Á. Timár, *Uniform Borel Amenability*, arXiv:2408.12565, TeX source `rand_submit.tex`.
The quotes below are copied from `co-amenable-hyperfinite-transfer-proof`, where they were fetched
on 2026-09-17.

- l.201–206: "Then $\cE$ is \textbf{Borel amenable} if the following two conditions are
  satisfied. (1) For every $n$ there exist non-negative Borel functions
  $\{p_n:\cE\to\R\}_{n=1}^\infty$ such that for all $x\in \X$ we have
  $\sum_{y\equiv_\cE x} p_n(x,y)=1\,,$ and (2) for all pairs $x\equiv_\cE z$:
  $$\lim_{n\to \infty} \sum_{y\equiv_\cE x} |p_n(x,y)-p_n(z,y)|\to 0\,,$$"
- l.296: "$\cE$ is called \textbf{$\mu$-amenable} if there exists a Borel subset $A\subset X$
  with $\mu(A)=1$ such that the restriction $\cE|_A$ of $\cE$ on $A$ is Borel amenable.
  Similarly, $\cE$ is \textbf{$\mu$-hyperfinite} if there exists a Borel subset
  $A\subset X$, $\mu(A)=1$, such that $\cE|_A$ is hyperfinite."
- l.299–300: "\textbf{Connes-Feldman-Weiss Theorem.} Let $\cE$ be a countable Borel equivalence
  relation on $X$ and $\mu$ a Borel probability measure on $X$. Then $\cE$ is $\mu$-amenable
  if and only if it is $\mu$-hyperfinite."
- l.212–214: "$\cE$ is \textbf{hyperfinite} if $\cE=\cup_{i=1}^\infty \cE_i$ for some finite
  equivalence relations $\cE_1\subset \cE_2\subset \cE_3 \subset\dots$ with the property that
  all equivalence classes of $\cE_n$ have bounded size."

## Step 1: the lagged tail relation is Borel amenable

**The relation on `C`.** For `x, y ∈ C`, set `x ~ y` if `σ^a x = σ^b y` for some `a, b ≥ 0`.
- This is an equivalence relation. Each class is countable.
- It is Borel, being a countable union of closed sets.

**The relation on `C^n`.** `E` is the coordinatewise product:
`x E y` if and only if `x_j ~ y_j` for every `j`. It is a countable Borel equivalence relation, and
its class is `[x]_E = Π_j [x_j]_~`.

**`nV` preserves `E`.** Take `g ∈ nV` with a table sending `Π_j C(u_j)` to `Π_j C(v_j)` by
`(u_j s_j)_j ↦ (v_j s_j)_j`. Then `σ^|v_j| (g x)_j = s_j = σ^|u_j| x_j`. So `g x E x` for every
`x`. Hence for every `Λ ≤ nV`, the orbit relation `R_Λ` is contained in `E`.

**Reiter functions on `C`.** For `m ≥ 1` and `x ~ y` put

`p_m(x, y) = (m+1)^-2 · Σ_{K=m}^{2m} Σ_{J=m}^{2m} 2^-K · 1[σ^K y = σ^J x]`.

- **Borel.** It is a finite sum of Borel indicators.
- **Probability.** Fix `K` and `J`. Exactly `2^K` points `y` satisfy `σ^K y = σ^J x`, one for
  each prefix `w` of length `K`, namely `y = w σ^J x`. All of them lie in `[x]_~`. So
  `Σ_y p_m(x, y) = 1`.
- **Pushforward form.** `p_m(x, ·)` is the law of `W σ^J x`, where `K` and `J` are independent and
  uniform on `{m, ..., 2m}`, and given `K`, `W` is a uniform word of length `K`.

**Asymptotic invariance on `C`.** Let `x ~ y`, say `σ^a x = σ^b y`, and put `d = a − b`.
- For `m ≥ b` and `J ≥ m` we have `σ^J y = σ^(J+d) x`.
- So `p_m(y, ·)` is the law of `W σ^(J+d) x` with `J` uniform on `{m, ..., 2m}`.
- Hence `p_m(x, ·)` and `p_m(y, ·)` are images of two laws of `(K, J', W)` under **the same** map
  `(K, J', W) ↦ W σ^(J') x`. The two laws differ only in `J'`, which is uniform on `{m, ..., 2m}` in
  one and on `{m+d, ..., 2m+d}` in the other.
- Images do not increase `ℓ^1` distance, so `‖p_m(x,·) − p_m(y,·)‖ ≤ 2|d|/(m+1) → 0`.

**On `C^n`.** Put `P_m(x, y) = Π_j p_m(x_j, y_j)` for `x E y`.
- It is Borel.
- It sums to `1` over `[x]_E = Π_j [x_j]_~`.
- It satisfies `‖P_m(x,·) − P_m(y,·)‖ ≤ Σ_j ‖p_m(x_j,·) − p_m(y_j,·)‖ → 0` for every pair `x E y`.

So `E` is **Borel amenable** in the sense of l.201–206. This holds for all pairs, with no
aperiodicity assumption.

## Step 2: the orbit relation of the lifting subgroup is ν-amenable

Let `ν` be a `Λ`-invariant Borel probability on `C^n`.
- **`E` is `ν`-hyperfinite.** By Step 1, `E` is Borel amenable, hence `ν`-amenable (take the
  conull set to be `C^n`). By Connes–Feldman–Weiss (l.299–300), `E` is `ν`-hyperfinite. So there
  is a Borel `A_0` with `ν(A_0) = 1` and `E|A_0 = ∪_i E_i`, with `E_i` increasing finite Borel
  equivalence relations whose classes have bounded size.
- **An invariant conull set.** `Λ` is countable and preserves `ν`, so `A_1 = ∩_{λ∈Λ} λ A_0` is
  conull and `Λ`-invariant.
- **`R_Λ` is hyperfinite on `A_1`.** On `A_1` we have `R_Λ|A_1 ⊆ E|A_0`. So
  `R_Λ|A_1 = ∪_i (E_i ∩ R_Λ|A_1)`. These are increasing finite Borel equivalence relations with
  bounded class sizes, and `R_Λ|A_1` is the full orbit relation of `Λ` on the invariant set `A_1`.
- **Reiter functions.** Let `r_i(x, ·)` be the uniform probability on the
  `E_i ∩ R_Λ`-class of `x ∈ A_1`.
  - It is Borel. On a finite Borel equivalence relation, the class size and the class membership
    indicator are Borel.
  - Take `x R_Λ z` in `A_1`. They lie in one class of `E_i ∩ R_Λ` for all large `i`, so
    `r_i(x,·) = r_i(z,·)` eventually.

Summary: `r_i(x,·)` is a probability on the orbit `Λx` for each `x ∈ A_1`. It is Borel in `(x, y)`,
and `‖r_i(x,·) − r_i(λx,·)‖ → 0` for every `x ∈ A_1` and every `λ ∈ Λ`.

## Step 3: pushing Reiter functions through the factor map

Put `μ = φ_*ν` and `A = q(Λ)`.
- `μ` is `A`-invariant: `q(λ)_* μ = φ_* λ_* ν = φ_* ν`.
- **Disintegration (Rokhlin).** There is a Borel family `z ↦ ν_z` of probabilities with
  `ν_z(φ^-1 z) = 1` and `ν = ∫ ν_z dμ(z)`. It is unique up to `μ`-null sets.
- **Equivariance.** Fix `λ`, with `γ = q(λ)`. Then `ν = λ_*ν = ∫ λ_*ν_z dμ(z) = ∫ λ_*ν_(γ^-1 w) dμ(w)`,
  using `γ_*μ = μ`. Here `λ_*ν_(γ^-1 w)` is carried by `λ φ^-1(γ^-1 w) = φ^-1(w)`. By uniqueness,
  `λ_*ν_z = ν_(γz)` for `μ`-a.e. `z`. Since `Λ` is countable, this holds for all `λ` at once on a
  `μ`-conull set.
- **The pushed functions.** `φ` maps `Λx` into `A φ(x)`. For `x ∈ A_1` and `w ∈ A φ(x)` let
  `s_i(x, w) = Σ_{y ∈ Λx, φ(y) = w} r_i(x, y)`.
  - This is Borel. Enumerate `Λ = {λ_1, λ_2, ...}` and sum `r_i(x, λ_l x)` over those `l` with
    `φ(λ_l x) = w` and `λ_l x ≠ λ_(l') x` for all `l' < l`.
  - `s_i(x,·) = φ_* r_i(x,·)` is a probability on `A φ(x)`.
  - `‖s_i(x,·) − s_i(λx,·)‖ ≤ ‖r_i(x,·) − r_i(λx,·)‖`.
- For `z` in the conull set where `ν_z(A_1) = 1`, put `F_i(z, ·) = ∫ s_i(x, ·) dν_z(x)`. It is a
  probability on the orbit `Az`.
- **Asymptotic invariance.** Let `γ = q(λ)`. For `μ`-a.e. `z`,
  `F_i(γz, ·) = ∫ s_i(x', ·) dν_(γz)(x') = ∫ s_i(λx, ·) dν_z(x)`.
  Hence `‖F_i(z,·) − F_i(γz,·)‖ ≤ ∫ ‖r_i(x,·) − r_i(λx,·)‖ dν_z(x) → 0`. The limit is by dominated
  convergence: the integrand is at most `2` and tends to `0` on `A_1`, which is `ν_z`-conull.
- This holds for every `γ ∈ A` on one conull set, because `A` is countable.

**Where invariance is used.** The equality `ν_(γz) = λ_*ν_z` is the only place `Λ`-invariance of
`ν` enters, and it cannot be dropped. For the free group acting on `∂F_2 × Y`, the orbit relation is
amenable, but its factor `Y` (free and measure-preserving) is not. There the fibre measures are not
equivariant.

## Step 4: freeness turns orbit Reiter functions into group Reiter functions

Assume `A` acts `μ`-essentially freely. `A` is countable, so on a conull set `Z_0` every stabilizer
is trivial, and `b ↦ bz` is a bijection `A → Az`.
- For `z ∈ Z_0`, put `P^z_i(b) = F_i(z, bz)`, a probability on `A`.
- **Coordinates.** For `γ ∈ A`, the point `cz` equals `(cγ^-1)(γz)`. So Step 3 reads
  `‖P^z_i − ρ_γ P^(γz)_i‖ → 0` for a.e. `z`, where `(ρ_γ P)(c) = P(cγ^-1)`.
- **Averaging.** Put `f_i = ∫ P^z_i dμ(z)`, a probability on `A`. By `γ`-invariance of `μ`,
  `∫ ρ_γ P^(γz)_i dμ(z) = ρ_γ f_i`. So `‖f_i − ρ_γ f_i‖ ≤ ∫ ‖P^z_i − ρ_γ P^(γz)_i‖ dμ → 0`, by
  dominated convergence again.
- So `(f_i)` is a Reiter sequence for right translations on the countable group `A`, and `A` is
  amenable. (Reiter's condition; replace `f_i` by `f_i(·^-1)` for left translations.)

`z ↦ P^z_i(b) = ∫ s_i(x, bz) dν_z(x)` is Borel. The integrand is Borel in `(x, z)`, and `z ↦ ν_z` is
a Borel family. So the integrals above make sense.

## Step 5: `EL_2(R)` is nonamenable

Suppose `EL_2(R)` were amenable.
- Then `G = EL_2(R) ⋉ R^2` is amenable, being an extension of an amenable group by an abelian one.
- So the left regular representation `ℓ^2(G)` has almost invariant unit vectors (Reiter/Hulanicki,
  or directly from Følner sets).
- By `elementary-linear-semidir-pair-relative-t`, `(G, R^2)` has relative property (T). So
  `ℓ^2(G)` has a nonzero `R^2`-invariant vector.
- Such a vector is constant on the cosets `R^2 g`. A nonzero `ℓ^2` function constant on a coset
  forces that coset to be finite. But `R^2` is infinite.

So `EL_2(R)` is nonamenable. Here `R = F_p[t,t^-1]` is finitely generated, as the import requires.

## Step 6: Haar measure is free for every affine map (Theorem H(b))

Let `a(ξ) = γ·ξ + v` with `a ≠ 1`.
- **Case `γ = 1`.** Then `v ≠ 0` and `Fix a = ∅`.
- **Case `γ ≠ 1`.** Put `T = γ^-1 − 1 ≠ 0`, an `R`-linear endomorphism of `M`. Then
  `(γ − 1)·ξ = ξ∘T`. So `Fix a` is empty or a coset of `K = {ξ : ξ∘T = 0}`, which is a closed
  subgroup.
  - **The image is infinite.** The image of `ξ ↦ ξ∘T` is identified with `Hom(TM, F_p)`: every
    `F_p`-linear form on the subspace `TM` extends to `M`, and `ξ∘T` depends only on `ξ|TM`.
  - `TM` is a nonzero `R`-submodule of `R^2`. It contains `Rm ≅ R` for some `m ≠ 0`, because `R` is a
    domain and `R^2` is torsion-free. So `TM` is an infinite `F_p`-space, and the image
    `M^/K ≅ Hom(TM, F_p)` is infinite.
  - **So `K` is null.** `K` has infinite index, so it has infinitely many disjoint translates of
    equal Haar measure. Hence `μ_H(K) = 0` and `μ_H(Fix a) = 0`.
- `GL_2(R)` acts faithfully on `M^`, because characters of the discrete group `M` separate points.
  So `a ≠ 1` as a map is the same as `a ≠ 1` in `Aff(M^)`.

## Step 7: assembly

**Theorem H(a).**
- By Steps 2–4, `A = q(Λ)` is amenable.
- The linear-part map `Aff(M^) → GL_2(R)` is a homomorphism. So the linear-part group of `A` is an
  amenable quotient of `A`.
- That group contains `EL_2(R)`, and subgroups of amenable groups are amenable. This contradicts
  Step 5.

**Theorem H(b)** is Step 6.

**Theorem H(c).** Let `φ` be a homeomorphism onto `M^` and put `ν = (φ^-1)_*μ_H`.
- `φ_* λ_* ν = q(λ)_* μ_H = μ_H = φ_* ν`, and `φ` is injective, so `λ_*ν = ν`.
- `φ_*ν = μ_H`, so (b) gives freeness and (a) gives the contradiction.
- **Proposition B, `p = 2`, `k = 2`.** Its `φ` is a homeomorphism `C^2 → (F_2^2)^Z` with
  `φ∘B^2 = h∘φ`. Any `Λ ∋ B^2` together with lifts of `e_12(1)`, `e_12(t)` and `w`, all for this
  `φ` and with any translations, would be such a conjugacy. The linear parts would contain
  `⟨h, e_12(1), e_12(t), w⟩ = EL_2(R)`, since `e_21(r) = w e_12(−r) w^-1`. So no such lifts exist.

**Theorem H(d).** `ν = β` is `Λ`-invariant because the generators preserve it. And `φ_*β = μ_H` by
hypothesis. Apply (a) and (b). The baker map preserves `β`: the brick `C(aw) × C(w')` has the
same measure as its image `C(w) × C(aw')`. ∎

## Checks

- Theorem H is consistent with Farley's theorem that `V` is Haagerup. It forbids more
  realizations, and it does not claim that any realization exists.
- It is consistent with Theorem K(i). For `p ≥ 3`, K already rules out conjugacies. H recovers
  this by a different invariant (amenability rather than fixed-point germs) and extends it to
  `p = 2`.
- Nothing in Steps 1–4 uses `p`, `n` or the ring. So the same kill applies to the general-`R`
  version of Theorem R. There `R` is any finitely generated infinite commutative `F_p`-algebra. If
  `R` is a domain, Step 6 holds verbatim. Otherwise freeness has to be checked separately.
