# Vertex rounding fails at the affine-symplectic product pair (2026-09-16)

Lane `swarm-hs-stable-vertex-rounding-for-every-model`. Proof artifact for
`vertex-rounding-fails-at-symplectic-product-pair` (route
`vertex-rounding-fails-at-symplectic-product-pair-proof`).

**Result.** The general form of `hs-stable-vertex-rounding-for-every-model` is false. There is an
infranormal, non-normal pair `Γ < G` of residually finite Kazhdan groups and a trace-preserving
`σ : G -> U(prod_U M_n)` at which (H1) fails for every finite generating set of `Γ`, under every
padding convention in use.

**Inputs (all ESTABLISHED in the graph).**
- `kun-thom-nonsofic-wreath` (Kun--Thom Theorem E, arXiv:2608.06222): for a prime power `q` and
  `r, d >= 3`, `K = EL_r(F_q[x_1..x_d]) < H = EL_r(F_q[x_1^(±1)..x_d^(±1)]) ⋊ SL_d(Z)` are residually finite
  Kazhdan groups, and `K` is infranormal but not normal in `H`.
- `rf-kazhdan-group-not-flexibly-hs-stable`, item 1: `Γ_g = Z^(2g) ⋊ Sp_(2g)(Z)`, `g >= 2`, is residually
  finite and has property (T). Item 2 supplies the models `α_k`.
- `bdhv-central-extension-property-t`: a countable group with finite abelianization which is a central
  extension of a Kazhdan group has (T).

Nothing else is imported. Every other step is proved below.

## 0. Conventions

- **Norms.** For an `N × D` matrix `X`, `||X||_(2,N) = (Tr(X*X)/N)^(1/2)`. Multiplying on either side by a
  unitary does not change `||X||_(2,N)`. `||AB - CD||_(2,N) <= ||B - D||_(2,N) + ||A - C||_(2,N)` when
  `A` and `D` are unitary.
- **Models.** `M = prod_U M_n` is the tracial ultraproduct over a nonprincipal ultrafilter `U` on `N`, with
  trace `τ`. A homomorphism `σ : G -> U(M)` has coordinates `σ_n : G -> U(n)`: any choice of
  representatives. It is **trace-preserving** when `τ(σ(x)) = lim_U tr σ_n(x) = δ_(x,e)`, with
  `tr = Tr/n`. Two choices of coordinates differ by `o(1)` in `||·||_(2,n)` along `U`, so (H1) does not
  depend on the choice.
- **(H1) at `σ` for a finite generating set `F` of `Γ`.** Two readings occur in the graph and the
  literature.
  - *(Pad)* There are genuine `π_n : Γ -> U(n')`, `n'/n -> 1` along `U`, and padded dimensions
    `n'' >= max(n, n')` with `n''/n -> 1`, such that
    `max_(s∈F) ||σ_n(s) ⊕ 1_(n''-n) - π_n(s) ⊕ 1_(n''-n')||_(2,n'') -> 0` along `U`. (The smallest choice is
    `n'' = max(n, n')`. Normalizing by `n` instead of `n''` changes the norm by a factor tending to 1.)
  - *(Comp)* (Dogon, arXiv:2211.10492, Definition 1.2) There are genuine `π_n : Γ -> U(D_n)`, `D_n >= n`,
    `D_n/n -> 1`, with `max_(s∈F) ||σ_n(s) - P π_n(s) P*||_(2,n) -> 0`, where `P : C^(D_n) -> C^n` keeps the
    first `n` coordinates.

**Lemma 0.1 (both readings give (P)).** Each reading implies:

> **(P)** There are genuine `π'_n : Γ -> U(D_n)` with `D_n >= n`, `D_n/n -> 1` along `U`, such that
> `X_n(s) := σ_n(s) ⊕ 1_(D_n - n)` satisfies `||X_n(s) - π'_n(s)||_(2,D_n) -> 0` along `U` for `s ∈ F`.

*Proof.* From (Pad), take `D_n = n''` and `π'_n = π_n ⊕ 1_(n''-n')`. From (Comp), take `π'_n = π_n`.
Write `Y = π_n(s)` in blocks along `C^n ⊕ C^(D_n - n)`, so `Y_11 = PYP*`. Then

```text
Tr((X_n(s) - Y)*(X_n(s) - Y)) = ||σ_n(s) - Y_11||_HS^2 + ||Y_12||_HS^2 + ||Y_21||_HS^2 + ||1 - Y_22||_HS^2
                              <= n ||σ_n(s) - Y_11||_(2,n)^2 + (D_n - n) + (D_n - n) + 4(D_n - n).
```

Here `Y_12*Y_12 <= 1` and `Y_21 Y_21* <= 1` on `C^(D_n - n)`, and `1 - Y_22` has rank at most `D_n - n`
and norm at most 2. Dividing by `D_n` gives `||X_n(s) - Y||_(2,D_n)^2 <= ||σ_n(s) - Y_11||_(2,n)^2 +
6(D_n - n)/D_n -> 0`. ∎

*Referee remark (2026-09-16).* If (Pad) is read with arbitrary unitary padding blocks `W_n` in place of
`1_(n''-n)` (and likewise on the `π_n` side), nothing changes: replacing a block of dimension `n''-n` by `1`
moves the matrix by at most `2((n''-n)/n'')^(1/2) -> 0` in `||·||_(2,n'')`.

**Lemma 0.2 (propagation).** If (P) holds for `s ∈ F` and `F` generates `Γ`, then
`||X_n(x) - π'_n(x)||_(2,D_n) -> 0` along `U` for every `x ∈ Γ`.

*Proof.* Let `S` be the set of `x` for which this holds. Since `σ` is a homomorphism into `U(M)`,
`||σ_n(xy) - σ_n(x)σ_n(y)||_(2,n) -> 0` and `||σ_n(e) - 1||_(2,n) -> 0` along `U`. Padding by `1` multiplies
these defects by `(n/D_n)^(1/2) <= 1`. So `e ∈ S`. If `x, y ∈ S`, then

```text
||X_n(xy) - π'_n(xy)|| <= ||X_n(xy) - X_n(x)X_n(y)|| + ||X_n(x) - π'_n(x)|| + ||X_n(y) - π'_n(y)|| -> 0.
```

Also `||X_n(x)X_n(x^(-1)) - 1|| -> 0`, so `||X_n(x^(-1)) - X_n(x)*|| -> 0`, and
`||X_n(x)* - π'_n(x)*|| = ||X_n(x) - π'_n(x)||`. Hence `S` is a subgroup containing `F`, so `S = Γ`. ∎

## 1. Three standard facts about property (T), proved

A **Kazhdan pair** `(Q, κ)` for a countable group `Λ` is a finite `Q ⊂ Λ` and `κ > 0` such that every
unitary representation with a unit vector `ξ`, `max_(x∈Q) ||π(x)ξ - ξ|| < κ`, has a nonzero invariant vector.

**Lemma 1.1 (a Kazhdan set generates).** If `(Q, κ)` is a Kazhdan pair for `Λ`, then `Q` generates `Λ`.

*Proof.* Let `L = <Q>` and suppose `L ≠ Λ`. On `ℓ^2(Λ/L)` the vector `δ_L` is fixed by `Q`. An invariant
vector is constant on the single orbit `Λ/L`. If `[Λ:L] = ∞` there is none, which contradicts the pair. If
`[Λ:L] < ∞`, the complement of the constants is invariant, contains no nonzero invariant vector, and
contains the nonzero `Q`-fixed vector `δ_L - |Λ/L|^(-1)·1`. Again a contradiction. ∎

**Lemma 1.2 (finite abelianization).** A Kazhdan group has finite abelianization.

*Proof.* By Lemma 1.1, `Λ` is finitely generated, so `A = Λ^ab` is a finitely generated abelian group. (T)
passes to quotients: pull representations back. If `A` were infinite it would surject onto `Z`, which
would then have (T). But in `ℓ^2(Z)` the vectors `ξ_m = m^(-1/2) 1_([0,m))` satisfy
`||λ(±1)ξ_m - ξ_m||^2 = 2/m -> 0`, so by the triangle inequality `ξ_m` is almost invariant under every
finite subset of `Z`, and `ℓ^2(Z)` has no nonzero invariant vector. ∎

**Lemma 1.3 (products).** If `(Q_1, κ_1)` and `(Q_2, κ_2)` are Kazhdan pairs for `Λ_1` and `Λ_2`, then
`(Q_1 × {e} ∪ {e} × Q_2, min(κ_1, κ_2)/2)` is a Kazhdan pair for `Λ_1 × Λ_2`.

*Proof.* Let `π` act on `ℋ`, let `ξ` be a unit vector, and let `δ < min(κ_1, κ_2)/2` bound the
displacements over the set. Let `P_2` be the projection onto `ℋ^(Λ_2)`, the vectors fixed by `{e} × Λ_2`.
- `ℋ^(Λ_2)` and its complement are `Λ_2`-invariant, and the complement has no nonzero invariant vector.
  Put `η = ξ - P_2ξ`. For `x ∈ Q_2`, `π(x)ξ - ξ = π(x)η - η`. If `η ≠ 0`, then the pair gives some `x ∈ Q_2`
  with `||π(x)η - η|| >= κ_2 ||η||`. So `||η|| <= δ/κ_2 < 1/2`.
- `Λ_1 × {e}` commutes with `{e} × Λ_2`, so `ℋ^(Λ_2)` is `Λ_1`-invariant and `P_2` commutes with `π(Λ_1)`.
  Put `ζ = P_2 ξ`. Then `||ζ|| > 1/2`, and for `x ∈ Q_1`, `||π(x)ζ - ζ|| = ||P_2(π(x)ξ - ξ)|| <= δ`.
- The unit vector `ζ/||ζ||` has displacement `< 2δ < κ_1` over `Q_1`. So `ℋ^(Λ_2)` contains a nonzero
  `Λ_1`-invariant vector, which is `Λ_1 × Λ_2`-invariant. ∎

## 2. The pair

Fix `g >= 2`, a prime power `q` and `r, d >= 3`. Let `(K < H)` be the Theorem E pair and `Γ_g` the affine
symplectic group. Put

```text
Γ = Γ_g × K   <   G = Γ_g × H.
```

**Proposition 2.1.** `Γ` and `G` are residually finite Kazhdan groups, and `Γ` is infranormal but not normal
in `G`.

*Proof.*
- **(T).** `Γ_g`, `K` and `H` have (T) (inputs). Apply Lemma 1.3 twice.
- **Residual finiteness.** A nontrivial `(a, h)` has a nontrivial coordinate. Separate that coordinate in
  a finite quotient of its factor and compose with the projection.
- **Compression semigroup.** `(a,h)(γ,k)(a,h)^(-1) = (aγa^(-1), hkh^(-1))`, so
  `(a,h) Γ (a,h)^(-1) = Γ_g × hKh^(-1)`. This lies in `Γ` iff `hKh^(-1) <= K`. Hence
  `P_Γ = Γ_g × P_K`.
- **Infranormal.** `P_Γ` contains `Γ_g × {e}` and `{e} × P_K`. So `<P_Γ> ⊇ Γ_g × <P_K> = Γ_g × H = G`.
- **Not normal.** Some `h ∈ H` has `hKh^(-1) ≠ K`, and then `(e,h)Γ(e,h)^(-1) ≠ Γ`. ∎

By Lemma 1.1 every Kazhdan pair `(F, κ)` of `Γ` has `F` generating `Γ`. So (H1) at `σ` in the sense of
`hs-stable-vertex-rounding-for-every-model` is an instance of §0 with a generating set `F`.

## 3. Property (T) of the Heisenberg cover

This repeats `rf-kazhdan-group-not-flexibly-hs-stable-proof` §3, with one change: finite abelianization of
`Sp_(2g)(Z)` is taken from item 1 of `rf-kazhdan-group-not-flexibly-hs-stable` through Lemma 1.2, so only
the claim, not its route, is imported.

Let `ω(x,y) = Σ_i (x_i y_(g+i) - x_(g+i) y_i)` and `Γ~_g = Z^(2g) × Z × Sp_(2g)(Z)` with

```text
(v,s,A)(w,t,B) = (v + Aw, s + t + ω(v,Aw), AB).
```

**Lemma 3.1.** `Γ~_g` is a group, `z = (0,1,1)` is central, `q(v,s,A) = (v,A)` is a surjective homomorphism
`Γ~_g -> Γ_g` with kernel `<z>`, and `Γ~_g` has property (T).

*Proof.*
- **Group law.** The identity is `(0,0,1)` and `(v,s,A)^(-1) = (-A^(-1)v, -s, A^(-1))`: indeed
  `ω(v, A(-A^(-1)v)) = -ω(v,v) = 0`. For associativity, both bracketings of `(v,s,A)(w,t,B)(u,r,C)` have
  first and third coordinates `v + Aw + ABu` and `ABC`. The second coordinates are
  `s+t+r + ω(v,Aw) + ω(v+Aw, ABu)` and `s+t+r + ω(w,Bu) + ω(v, A(w+Bu))`. These agree because
  `ω(Aw, ABu) = ω(w, Bu)` for symplectic `A`.
- **Centre and quotient.** `(0,1,1)(w,t,B) = (w, t+1, B) = (w,t,B)(0,1,1)`, since `ω(0,·) = ω(·,0) = 0`.
  `q` is a homomorphism by inspection, and `ker q = {(0,s,1)} = {z^s}`.
- **Generators.** Put `x_w = (w,0,1)` and `y_A = (0,0,A)`. Then `x_v z^s y_A = (v,s,A)`, `y_A y_B = y_(AB)`,
  `y_A x_w y_A^(-1) = x_(Aw)` and `x_w x_u = z^(ω(w,u)) x_(w+u)`.
- **Finite abelianization.** Let `Ab = Γ~_g^(ab)` and write `[·]` for images.
  - From `x_w x_u = z^(ω(w,u)) x_(w+u)` and `x_u x_w = z^(ω(u,w)) x_(w+u)`, the commutator is
    `[x_w, x_u] = z^(2ω(w,u))`. With `ω(e_1, e_(g+1)) = 1` this gives `2[z] = 0`.
  - `w -> [x_w]` is a homomorphism `Z^(2g) -> Ab/<[z]>`, and it is constant on `Sp_(2g)(Z)`-orbits. The
    transvection `T_u(x) = x + ω(u,x)u` is symplectic and `T_u(x) - x = ω(u,x)u`. Taking `(u,x)` equal to
    `(e_i, e_(g+i))` and `(e_(g+i), -e_i)` shows that every basis vector is of the form `T x - x`. So the
    homomorphism vanishes, and `[x_w] ∈ <[z]>` for every `w`.
  - The images `[y_A]` form a quotient of `Sp_(2g)(Z)^(ab)`. `Sp_(2g)(Z)` is the quotient `(v,A) -> A` of
    the Kazhdan group `Γ_g`, so it is Kazhdan and, by Lemma 1.2, has finite abelianization.
  - Hence `Ab` is generated by a group of order at most 2 and a finite group, and is finite.
- **(T).** `Γ~_g / <z> ≅ Γ_g` has (T). Apply `bdhv-central-extension-property-t` with `C = <z>`. ∎

**Fixed data.** Fix a Kazhdan pair `(Q~, κ~)` for `Γ~_g`, a finite generating set `S_0` of `Γ_g`, and the
section `s(v,A) = (v,0,A)`. Then `s(a)s(b) = z^(c(a,b)) s(ab)` with `c((v,A),(w,B)) = ω(v,Aw)`, and
`(v,t,A) = z^t s(v,A)`. So `s(S_0) ∪ {z}` generates `Γ~_g`. Fix `L >= 1` such that every element of `Q~` is
a word of length at most `L` in `s(S_0)^(±1) ∪ {z^(±1)}`.

## 4. Amplified non-roundability with uniform constants

**Lemma 4.1.** Let `ρ : Γ~_g -> U(d)` be a genuine representation with `ρ(z) = ζ·1_d` for a scalar `ζ ≠ 1`,
and put `β = ρ∘s : Γ_g -> U(d)`. Let `π : Γ_g -> U(D)` be a genuine representation with `D >= d`, and let
`P : C^D -> C^d` keep the first `d` coordinates. Suppose `ε >= 0` satisfies

```text
max_(a∈S_0) ||β(a) - P π(a) P*||_(2,d) <= ε,     (D - d)/d <= ε,     L·max(ε + √ε, |ζ - 1|) < κ~.
```

This is impossible. The constants `L`, `κ~` do not depend on `d`, `ρ`, `ζ`, `D` or `π`.

*Proof.*
- **Bimodule.** Let `ℋ = M_(d×D)(C)` with `⟨ξ,η⟩ = Tr(η*ξ)/d`, and `Σ(x)ξ = ρ(x) ξ π(q(x))*` for
  `x ∈ Γ~_g`. `Σ` is a genuine unitary representation. `Σ(z)ξ = ζξ`, so `Σ` has no nonzero invariant
  vector.
- **The vector `P`.** `PP* = 1_d`, so `||P||^2 = Tr(P*P)/d = 1`.
- **Letters `s(a)`, `a ∈ S_0`.** Right multiplication by the unitary `π(a)` preserves the norm, so
  `||Σ(s(a))P - P|| = ||β(a)P - Pπ(a)||`. Write `X = β(a) - Pπ(a)P*`. Then

  ```text
  β(a)P - Pπ(a) = XP - Pπ(a)(1 - P*P).
  ```

  The two terms are orthogonal, because `Tr((XP)* Pπ(a)(1 - P*P)) = Tr(X* Pπ(a)(1 - P*P)P*)` and
  `(1 - P*P)P* = 0`. Also `||XP||^2 = Tr(X*X PP*)/d = ||X||_(2,d)^2`, and
  `||Pπ(a)(1 - P*P)||^2 <= Tr(1 - P*P)/d = (D - d)/d`. So `||Σ(s(a))P - P||^2 <= ε^2 + ε`, which is at most
  `(ε + √ε)^2`.
- **Inverses and `z`.** `||Σ(x^(-1))P - P|| = ||P - Σ(x)P||`, and `||Σ(z^(±1))P - P|| = |ζ - 1|`.
- **Words.** `||Σ(xy)P - P|| <= ||Σ(x)(Σ(y)P - P)|| + ||Σ(x)P - P|| = ||Σ(y)P - P|| + ||Σ(x)P - P||`. So
  every `x ∈ Q~` moves `P` by at most `L·max(ε + √ε, |ζ - 1|) < κ~`.
- **Contradiction.** `(Q~, κ~)` is a Kazhdan pair, so `Σ` has a nonzero invariant vector. ∎

Fix `ε_0 ∈ (0, 1)` with `L(ε_0 + √ε_0) < κ~`. Lemma 4.1 then applies whenever `|ζ - 1| < κ~/L`.

## 5. The model

**Symplectic factor.** For `k >= 3`, `ρ~_k : Γ~_g -> U(d_k)` is the genuine representation of item 2 of
`rf-kazhdan-group-not-flexibly-hs-stable`: the left regular representation of `Γ~_g mod k`, cut down to the
subspace where `z` acts by `ζ_k = e^(2πi/k)`. So `ρ~_k(z) = ζ_k·1`. Put `α_k = ρ~_k∘s`. By item 2 and §3,

```text
α_k(a)α_k(b) = ζ_k^(c(a,b)) α_k(ab),     α_k(e) = 1,     tr α_k(a) -> δ_(a,e) as k -> ∞.
```

**Kazhdan factor.** `H` is finitely generated (Lemma 1.1) and residually finite. Enumerate
`H \ {e} = {h_1, h_2, ...}` and choose finite-index normal subgroups `M_i` with `h_i ∉ M_i`. Put
`N'_j = M_1 ∩ ... ∩ M_j`, `m_j = [H : N'_j]`, and let `λ_j : H -> U(m_j)` be the permutation representation on
`ℓ^2(H/N'_j)`. Since `N'_j` is normal, `h` fixes a coset iff `h ∈ N'_j`, so `tr λ_j(h) = 1` if `h ∈ N'_j` and
`0` otherwise. Hence `tr λ_j(h) -> δ_(h,e)`.

**Dimensions and ultrafilter.** Since `d_k >= k^(2g)`, choose `k_j >= j + 3` inductively so that
`N_j = d_(k_j) m_j` is strictly increasing. Put `D = {N_j : j >= 1}`, and fix a nonprincipal ultrafilter `U`
on `N` with `D ∈ U`; one exists because `D` is infinite. Define

```text
σ_n(a, h) = α_(k_j)(a) ⊗ λ_j(h) ∈ U(N_j)   if n = N_j,          σ_n ≡ 1_n   if n ∉ D.
```

**Lemma 5.1.** `σ(x) = (σ_n(x))_U` is a trace-preserving homomorphism `G -> U(prod_U M_n)`.

*Proof.*
- **Homomorphism.** For `x = (a,h)` and `y = (b,h')`, at `n = N_j`,
  `σ_n(x)σ_n(y) = ζ_(k_j)^(c(a,b)) σ_n(xy)`. So `||σ_n(x)σ_n(y) - σ_n(xy)||_(2,n) <= 2π|c(a,b)|/k_j`. Off
  `D` the defect is `0`. For each `ε > 0` the set where the defect is `< ε` contains `D` minus finitely many
  points, which lies in `U` because `U` is nonprincipal. Also `σ_n(e) = 1`.
- **Trace.** Since `D ∈ U` and `j -> N_j` is injective, `lim_U tr σ_n(x)` is a limit of
  `tr α_(k_j)(a)·tr λ_j(h)` along a nonprincipal ultrafilter on `j`. The factors tend to `δ_(a,e)` and
  `δ_(h,e)`, and both are bounded by 1. So `τ(σ(x)) = δ_(x,e)`. ∎

## 6. (H1) fails at σ

**Theorem 6.1.** For every finite generating set `F` of `Γ = Γ_g × K`, (H1) fails at `σ` under (Pad) and
under (Comp). In particular it fails for every Kazhdan pair `(F, κ)` of `Γ`.

*Proof.* Suppose (H1) holds for `F`.
1. **Reduction.** By Lemma 0.1 there are genuine `π'_n : Γ -> U(D_n)` with `D_n >= n` and `D_n/n -> 1` for
   which (P) holds. By Lemma 0.2, `||X_n(a,e) - π'_n(a,e)||_(2,D_n) -> 0` along `U` for each `a ∈ S_0`.
2. **The coordinates at `n = N_j`.** `σ_n(a, e) = α_(k_j)(a) ⊗ 1_(m_j) = β_j(a)`, where
   `β_j = ρ_j∘s` and `ρ_j = ρ~_(k_j) ⊗ 1_(m_j)` is a genuine representation of `Γ~_g` on `C^n` with
   `ρ_j(z) = ζ_(k_j)·1`. Put `π_n(a) = π'_n(a, e)`, a genuine representation of `Γ_g` on `C^(D_n)`.
3. **Compression.** Let `P : C^(D_n) -> C^n` keep the first `n` coordinates. The `(1,1)` block of a matrix
   has Hilbert--Schmidt norm at most that of the matrix, so

   ```text
   ||β_j(a) - P π_n(a) P*||_(2,n)^2  <=  (D_n/n) ||X_n(a,e) - π'_n(a,e)||_(2,D_n)^2  ->  0   along U.
   ```

4. **Choosing a coordinate.** With `ε_0` from §4, the set `E_1` of `n = N_j ∈ D` with
   `max_(a∈S_0) ||β_j(a) - Pπ_n(a)P*||_(2,n) <= ε_0` and `(D_n - n)/n <= ε_0` lies in `U`. The set
   `E_2 = {N_j : |ζ_(k_j) - 1| < κ~/L}` is cofinite in `D`, so it lies in `U`. Pick `n = N_j ∈ E_1 ∩ E_2`.
5. **Contradiction.** Lemma 4.1 with `d = n`, `ρ = ρ_j`, `ζ = ζ_(k_j)`, `D = D_n`, `π = π_n` and
   `ε = ε_0` says this configuration is impossible.

So (H1) fails. By Lemma 1.1 every Kazhdan set of `Γ` is a finite generating set. ∎

**Remark 6.2 (robustness).** Steps 2--5 prove a quantitative statement: for every `j` with
`|ζ_(k_j) - 1| < κ~/L`, which is all but finitely many `j`, and every genuine `π : Γ_g -> U(D)` with
`N_j <= D <= (1 + ε_0)N_j`, one has `max_(a∈S_0) ||σ_(N_j)(a,e) - Pπ(a)P*||_(2,N_j) > ε_0`. So (H1) fails for
every nonprincipal ultrafilter containing `D`, and along every infinite set of indices `j`. Nothing about `H`
is used beyond (T), residual finiteness and the infranormal, non-normal position of `K`: the `H` factor only
makes the pair infranormal and the model trace-preserving.

**Remark 6.3 (every ultrafilter).** If the ultrafilter `U` is fixed in advance, a model with the same
obstruction exists on `prod_U M_n`, for every nonprincipal `U`. Keep `k_j`, `m_j` and `N_j` from §5.
- **The model.** For `n >= N_1^2` let `j(n) = max{j : N_j^2 <= n}`, `t_n = ⌊n/N_(j(n))⌋`,
  `d_n = t_n N_(j(n))` and `r_n = n - d_n < N_(j(n))`. Put
  `σ_n(a,h) = (α_(k_(j(n)))(a) ⊗ λ_(j(n))(h) ⊗ 1_(t_n)) ⊕ 1_(r_n)`, with the first summand on the first
  `d_n` coordinates, and `σ_n ≡ 1_n` for `n < N_1^2`.
- **Growth.** Each `N_j` is finite, so `j(n) -> ∞` as `n -> ∞`. Also `r_n/n < N_(j(n))/n <= 1/N_(j(n)) -> 0`,
  so `d_n/n -> 1`.
- **Homomorphism and trace.** The defect at `(x,y)` is `|ζ_(k_(j(n)))^(c(a,b)) - 1|(d_n/n)^(1/2) <=
  2π|c(a,b)|/k_(j(n))`, and `tr σ_n(x) = (d_n/n)·tr α_(k_(j(n)))(a)·tr λ_(j(n))(h) + r_n/n`. Both converge as
  `n -> ∞`, to `0` and `δ_(x,e)`. So they converge along every nonprincipal `U`, and `σ` is a
  trace-preserving homomorphism `G -> U(prod_U M_n)`.
- **No rounding.** Suppose (P) holds along `U` for a generating set `F`. Lemma 0.2 gives
  `||X_n(a,e) - π'_n(a,e)||_(2,D_n) -> 0` along `U` for `a ∈ S_0`. Put `ρ_n = ρ~_(k_(j(n))) ⊗ 1_(m_(j(n)) t_n)`
  on `C^(d_n)` and `β_n = ρ_n∘s`. Then `β_n(a)` is the `(1,1)` block of `X_n(a,e)` along
  `C^(d_n) ⊕ C^(D_n - d_n)`. With `P''` keeping the first `d_n` coordinates,

  ```text
  ||β_n(a) - P'' π'_n(a,e) P''*||_(2,d_n)^2  <=  (D_n/d_n) ||X_n(a,e) - π'_n(a,e)||_(2,D_n)^2  ->  0   along U,
  ```

  and `(D_n - d_n)/d_n -> 0` along `U`, since `D_n/n -> 1` and `d_n/n -> 1`. Also `|ζ_(k_(j(n))) - 1| -> 0`.
  On a `U`-large set of `n`, Lemma 4.1 with `d = d_n`, `ρ = ρ_n`, `D = D_n`, `π = π'_n(·, e)` and
  `ε = ε_0` gives a contradiction.

So the refutation does not depend on how `U` is chosen.

## 7. Scope and graph effects

**What is refuted.**
- The general form of `hs-stable-vertex-rounding-for-every-model`, over every infranormal, non-normal pair of
  Kazhdan groups. The refutation is unconditional. The earlier scope bullets on that node, the nine-leaf
  Leavitt pair and the Fournier--Facio pair, refute the general form only if a particular group is
  hyperlinear. Here `G` is residually finite and the model is explicit.
- Every reading of (H1) in use: normalized padding (Pad) and Dogon's compression (Comp), at every Kazhdan set
  or finite generating set of `Γ`.
- Every choice of the nonprincipal ultrafilter `U`: Theorem 6.1 picks `U ∋ D`, and Remark 6.3 builds a model
  for a `U` fixed in advance.

**What is not touched.**
- **The Theorem E instance.** (H1) at `K < H` for every trace-preserving model of `H` is not decided. The
  failure above lives entirely on the `Γ_g` factor. The instance is recorded as the open claim
  `theorem-e-vertex-rounds-at-every-actor-model`.
- **Normalization.** Whether `σ(G)` normalizes `σ(Γ)' ∩ M` at this model, and so the general claim
  `kt-centralizer-normalization-hs`, is not examined here.

**The mechanism, and why the general form was too strong.**
- The only feature used is that the vertex contains a direct factor `Λ` which is Kazhdan, and which carries
  trace-preserving asymptotic representations whose non-roundability survives amplification by
  `1_m`.
- For `Λ = Γ_g` this comes from the Kazhdan non-split central extension `Γ~_g` (Lemma 4.1).
- Any such `Λ` can be multiplied onto an infranormal, non-normal Kazhdan pair with a trace-preserving model.
  So a true general version must restrict the vertex beyond (T), residual finiteness and infranormality.
- Finite `H_1` and `H_2` of the vertex is a natural candidate restriction.
  `finite-multiplier-projective-models-round-strictly` voids scalar-cocycle models there, and `Γ_g × K`
  violates it, since `Γ_g` carries a non-torsion class in `H^2(Γ_g; R)`. Whether that restriction suffices
  is not addressed: it does not exclude non-scalar instability mechanisms.
- At the Theorem E pair in the stable range `r >= d + 3`, `H_2(K; Z) = 0` (see
  `kt-actor-model-with-totally-non-roundable-vertex`, unverified imports), so scalar-cocycle models of `K`
  round strictly there, and the mechanism used here has no analogue on `K` itself.

**Graph effects.**
- `theorem-e-vertex-unit-type-via-deep-root-mass` required the general claim. It applied it only at the
  Theorem E pair, so it is restated as `theorem-e-unit-type-via-instance-vertex-rounding`, with the instance
  claim as premise and the other four premises unchanged.
- `hs-normalization-via-vertex-rounding-and-actor-gap` and `hs-normalization-via-vertex-rounding-and-liftable-masa`
  required the general claim for the general target `kt-centralizer-normalization-hs`. A Theorem E-only
  replacement would need a Theorem E instance of that target, which is not created here.
- `kt-actor-model-with-totally-non-roundable-vertex` listed the general claim as `refuted_by`. That link
  becomes inert once the general claim is refuted. The logically matching refuter is the instance claim, and
  the link is moved there.
