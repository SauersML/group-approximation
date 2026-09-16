# Σ^∞ near the fibre characters of a mapping torus: a bounded-displacement criterion

Swarm lane on Zaremsky Problem 1.13 (`zaremsky-1-13-sigma-infinity-is-open`),
2026-09-16. This artifact proves
`bounded-displacement-mapping-torus-sigma-infinity-open`. It also records a
general "uniform certificate" form of the perturbation argument (§5) and what
the criterion forces on a negative answer (§6).

## 0. Setting and notation

- `N` is a group of type `F_∞`, `φ ∈ Aut(N)`, and
  `G = N ⋊_φ Z = ⟨N, t | t n t^{-1} = φ(n)⟩`. `G` is of type `F_∞`.
- `χ : G → Z` is the fibre character: `χ(N) = 0`, `χ(t) = 1`.
- `V = Hom(N,R)^φ = {ψ : ψ∘φ = ψ}`, a finite-dimensional space since `N` is
  finitely generated. Every `ψ ∈ V` extends to a character of `G` by
  `ψ(n t^k) = ψ(n)`. This is a homomorphism because
  `ψ(n t^k · m t^l) = ψ(n φ^k(m)) = ψ(n) + ψ(m)`. Conversely, every character of
  `G` restricts on `N` to a `φ`-invariant character. So
  `Hom(G,R) = Rχ ⊕ V`, `χ' ↦ (χ'(t), χ'|_N)`.
- Fix a norm `‖·‖` on `V`, and for `g ∈ G` put
  `|g|_V = sup{|ψ(g)| : ψ ∈ V, ‖ψ‖ ≤ 1}`. So `|ψ(g)| ≤ ‖ψ‖·|g|_V`.
- A *based resolution* of `N` is a free resolution `P_* → Z` over `ZN` of
  finite type with a chosen finite basis `e_{i,1}, …, e_{i,r_i}` of each `P_i`.
- Let `θ ∈ Aut(N)`. A *lift of `θ`* is a family of additive maps
  `f_i : P_i → P_i` such that:
  - `f_i(n x) = θ(n) f_i(x)`;
  - `d f_i = f_{i-1} d`;
  - `ε f_0 = ε`.

  Write `f_i(e_{i,j}) = Σ_k c^{(i)}_{jk} e_{i,k}` with `c^{(i)}_{jk} ∈ ZN`.
- The *displacement* of the lift is
  `Δ(f) = sup_i max{|g|_V : g ∈ supp c^{(i)}_{jk}, 1 ≤ j,k ≤ r_i} ∈ [0, ∞]`.
  Each degree contributes a finite number. The condition `Δ(f) < ∞` asks for
  a bound that is uniform over all degrees.
- **Novikov rings.** For a nonzero character `ξ` of a group `Γ`, let
  `Nov_ξ(Γ)` be the ring of formal sums `λ = Σ λ_g g` such that
  `{g ∈ supp λ : ξ(g) < c}` is finite for every `c ∈ R`. It carries the
  valuation `v_ξ(λ) = min ξ(supp λ)`, with `v_ξ(0) = +∞`. It is a ring with
  `v(λ+μ) ≥ min(v(λ), v(μ))` and `v(λμ) ≥ v(λ) + v(μ)`. It is a right
  `ZΓ`-module by right multiplication. For a matrix `T` over `Nov_ξ(Γ)`, put
  `v(T) = min` over its entries. Then `v(ST) ≥ v(S) + v(T)`.

  If `v(T) > 0` and `T` is square, the series `Σ_{n≥0} T^n` converges
  entrywise: the coefficient at `g` receives contributions only from the
  finitely many `n` with `n·v(T) ≤ ξ(g)`, each contributing a finite sum, and
  the support condition is preserved. It is a two-sided inverse of `I − T`.

## 1. Imported facts

- **(I1) Novikov–Sikorav criterion.** For `Γ` of type `F_∞` and `ξ ≠ 0`,
  `[ξ] ∈ Σ^m(Γ;Z)` iff `Tor_i^{ZΓ}(Nov^±, Z) = 0` for all `i ≤ m`. Here
  `Nov^±` is one of `Nov_ξ(Γ)` or `Nov_{−ξ}(Γ)`, fixed once and for all by the
  convention. This is the same import used in
  `bnsr-invariants-stabilize-at-cohomological-dimension-proof` (Suciu,
  arXiv:2010.07499, abstract; Sikorav for `m = 1`; Bieri; Farber–Geoghegan–Schütz).
  §2 checks that the correct choice is `Nov_ξ(Γ)`, but the main claim is
  stated so that it does not depend on the sign.
- **(I2) Comparison.** For `Γ` of type `F_∞` and `m ≥ 2`,
  `Σ^m(Γ) = Σ^2(Γ) ∩ Σ^m(Γ;Z)` (Molyneux–Nucinkis–Santos Rego,
  arXiv:2309.12213, equation (2.1), going back to Renz and Bieri–Renz). Hence
  `Σ^∞(Γ) = Σ^2(Γ) ∩ Σ^∞(Γ;Z)`.
- **(I3) Openness.** `Σ^2(Γ)` is open in `S(Γ)` (Bieri–Neumann–Strebel, Renz;
  recorded in Ershov–Zaremsky arXiv:2505.18826 §2.1).
- **(I4) Kernel criterion.** For `Γ` of type `F_m` and `K ◁ Γ` containing
  `[Γ,Γ]`: `K` is of type `F_m` iff every character vanishing on `K` lies in
  `Σ^m(Γ)` (Zaremsky arXiv:1502.02620, Citation 1.2, from
  Bieri–Geoghegan–Kochloukova). For `G = N ⋊ Z` the kernel `N` contains
  `[G,G]`, and the characters vanishing on `N` are `±χ`. So `±[χ] ∈ Σ^∞(G)`.

## 2. Pinning the sign in (I1)

Take `Γ = BS(1,2) = ⟨a, t | t a t^{-1} = a^2⟩` and `χ(t) = 1`, `χ(a) = 0`. The
presentation complex is aspherical, so its cellular chain complex is a free
resolution. The Fox derivatives of `r = t a t^{-1} a^{-2}` are
`∂r/∂a = t − a − 1` and `∂r/∂t = 1 − a^2`. For a right module `M` the
complex `M ⊗ C_*` is
`M → M^2 → M`, with `λ ↦ (λ(t−a−1), λ(1−a^2))` and
`(x,y) ↦ x(a−1) + y(t−1)`.

- **Geometric side.** `Γ_χ`, the subgraph of the Cayley graph on
  `{g : χ(g) ≥ 0}`, is not connected. The elements of `N = Z[1/2]` reachable
  from `1` inside it form the smallest set containing `a^{±1}` and closed under
  products and `x ↦ t x t^{-1}`, namely `Z`, so `a^{1/2} = t^{-1} a t` is not
  reached. Hence `[χ] ∉ Σ^1`. For `−χ` the same recursion uses
  `x ↦ t^{-1} x t` and reaches all of `Z[1/2]`, so `[−χ] ∈ Σ^1`.
- **Over `Nov_{−χ}(Γ)`.** Here `v_{−χ}(t^{-1}) = 1`, so the following are
  units:
  - `t − 1 = t(1 − t^{-1})`;
  - `t − a − 1 = t(1 − t^{-1}(1+a))`, since `v_{−χ}(t^{-1}(1+a)) = 1 > 0`.

  Then `H_0 = 0`. Using the relation `(1−a^2)(t−1) = −(t−a−1)(a−1)` in `ZΓ`,
  every cycle `(x, −x(a−1)(t−1)^{-1})` is the boundary of
  `λ = x(t−a−1)^{-1}`, so `H_1 = 0`. This matches `[−χ] ∈ Σ^1`.
- **Over `Nov_χ(Γ)`.** The ring map `Nov_χ(Γ) → Z((s))` induced by `a ↦ 1`,
  `t ↦ s` sends `t − a − 1` to `s − 2`, which is not a unit of `Z((s))`. So the
  cycle `(1, −(a−1)(t−1)^{-1})` is not a boundary, and `H_1 ≠ 0`. This matches
  `[χ] ∉ Σ^1`.

The other choice would put `[χ]` in `Σ^1`, which is false. So (I1) holds with
`Nov^± = Nov_ξ(Γ)`: *ξ is in Σ^m(Γ;Z) iff Novikov homology vanishes for the
completion that allows infinite sums towards `+∞` of ξ.*

## 3. Theorem A (bounded displacement)

**Theorem A.** In the setting of §0, let `P_*` be a based resolution of `N`
and `f'` a lift of `φ^{-1}` with `Δ(f') < ∞`. Put `χ' = aχ + ψ` with `ψ ∈ V`
and `a > ‖ψ‖·Δ(f')`. Then `Tor_i^{ZG}(Nov_{χ'}(G), Z) = 0` for every `i ≥ 0`.
Symmetrically, a lift `f` of `φ` with `Δ(f) < ∞` gives
`Tor_*^{ZG}(Nov_{χ'}(G), Z) = 0` whenever `χ' = aχ + ψ` with
`−a > ‖ψ‖·Δ(f)`.

*Proof.* We prove the first statement. The second is the same argument with
`t^{-1}` in place of `t`.

**Step 1: a resolution of Z over ZG.**
- Put `F_* = ZG ⊗_{ZN} P_*`. This is a free `ZG`-resolution of
  `ZG ⊗_{ZN} Z = Z[G/N]`, since `ZG` is free as a right `ZN`-module. `F_i` has
  basis `1 ⊗ e_{i,j}`.
- Define `τ(g ⊗ x) = g t ⊗ f'(x)`. It is well defined:
  `τ(g n ⊗ x) = g t (t^{-1} n t) ⊗ f'(x) = g t ⊗ φ^{-1}(n) f'(x) = τ(g ⊗ n x)`.
- `τ` is `ZG`-linear and a chain map. It lifts the `ZG`-map
  `ρ : Z[G/N] → Z[G/N]`, `gN ↦ g t N`.
- Under `Z[G/N] ≅ Z[s^{±1}]`, with `gN ↦ s^{χ(g)}`, the map `ρ` is
  multiplication by `s`. So `1 − ρ` is injective with cokernel the trivial
  module `Z`.
- Hence the mapping cone `C_* = Cone(1 − τ)`, with `C_i = F_i ⊕ F_{i-1}`, is a
  free resolution of `Z` of finite type. This is the long exact sequence of the
  cone: `H_0(C) = coker(1−ρ) = Z`, `H_1(C) = ker(1−ρ) = 0`, and `H_i(C) = 0` for
  `i ≥ 2`.

**Step 2: after tensoring with the Novikov ring.** Let `M = Nov_{χ'}(G)`.
- `M ⊗_{ZG} C_* = Cone(1 − τ_M)`, where `τ_M = M ⊗ τ` acts on
  `M ⊗_{ZG} F_i ≅ M^{r_i}` (`m ⊗ g ⊗ e_{i,j} ↦ mg` in slot `j`).
- Since `τ(1 ⊗ e_{i,j}) = Σ_k t c^{(i)}_{jk} ⊗ e_{i,k}`, where `c^{(i)}` are
  the matrix entries of `f'_i`, the map `1 − τ_M` is right multiplication by
  `I − T_i` with `T_i = (t c^{(i)}_{jk})_{j,k}`.
- For `g ∈ supp c^{(i)}_{jk} ⊆ N` we have
  `χ'(t g) = a + ψ(g) ≥ a − ‖ψ‖·|g|_V ≥ a − ‖ψ‖·Δ(f') > 0`.
  So `v_{χ'}(T_i) ≥ a − ‖ψ‖Δ(f') > 0`, with the same positive bound in every
  degree `i`.
- By §0, `I − T_i` is invertible over `M` for every `i`. So `1 − τ_M` is a
  chain map that is bijective in each degree, i.e. a chain isomorphism.
- The cone of a chain isomorphism is contractible. Hence
  `Tor_i^{ZG}(M, Z) = H_i(M ⊗_{ZG} C_*) = 0` for all `i`. ∎

**Corollary A1.** With `f` a lift of `φ` and `f'` a lift of `φ^{-1}`, both of
finite displacement, put `Δ = max(Δ(f), Δ(f'))`. The open double cone
`U = {[aχ + ψ] : ψ ∈ V, |a| > ‖ψ‖Δ}` is a neighbourhood of `{[χ], [−χ]}` in
`S(G)`, and `U ⊆ Σ^∞(G;Z)` and `U ∩ W ⊆ Σ^∞(G)` for some neighbourhood `W` of
`±[χ]`. In particular `Σ^∞(G)` contains open neighbourhoods of `[χ]` and of
`[−χ]`.

*Proof.*
- `U` is open and contains `±[χ]`, because `Hom(G,R) = Rχ ⊕ V`.
- For `[ξ] ∈ U`, Theorem A gives `Tor_*(Nov_ξ(G), Z) = 0`. Since `−[ξ] ∈ U`
  too, it also gives `Tor_*(Nov_{−ξ}(G), Z) = 0`.
- So whichever sign convention (I1) uses, `[ξ] ∈ Σ^m(G;Z)` for all `m`, and
  `U ⊆ Σ^∞(G;Z)`.
- By (I4), `±[χ] ∈ Σ^2(G)`. By (I3) there is an open `W ∋ ±[χ]` with
  `W ⊆ Σ^2(G)`. By (I2), `U ∩ W ⊆ Σ^2(G) ∩ Σ^∞(G;Z) = Σ^∞(G)`. ∎

**One-sided refinement (uses §2).** With the sign pinned in §2, a lift `f'`
of `φ^{-1}` of finite displacement alone gives
`{[aχ + ψ] : a > ‖ψ‖Δ(f')} ⊆ Σ^∞(G;Z)`, a neighbourhood of `[χ]`. A lift of
`φ` alone gives the same near `[−χ]`.

**Remarks on the hypothesis.**
- **Depends only on the outer class.** If `φ_2 = c_{n_0} ∘ φ_1`, then
  `f_2 = n_0 · f_1` is a lift of `φ_2`, and `Δ(f_2) ≤ Δ(f_1) + |n_0|_V`.
- **Finite length.** If `P_*` has finite length, which happens when `N` is of
  type `F`, every lift has finite displacement. This recovers openness at
  `±[χ]` in that case (compare
  `bnsr-invariants-stabilize-at-cohomological-dimension`).
- **Inner automorphisms.** If `φ = c_{n_0}`, then `f(x) = n_0 x` is a lift of
  `φ` with `Δ(f) = |n_0|_V`, and `f'(x) = n_0^{-1} x` is a lift of `φ^{-1}`
  with the same displacement.
- **Degreewise radius.** Each degree `i` alone gives an explicit radius
  `1/Δ_i` for `Σ^i(G;Z)`. The hypothesis `Δ < ∞` is exactly what stops these
  radii from shrinking to `0`, which is the failure mode recorded in the
  Attempts of `every-f-infinity-group-has-open-sigma-infinity`.

## 4. Corollary C (a power suffices)

**Corollary C.** Let `k ≥ 1`. Suppose `φ^k` and `φ^{-k}` have lifts `f`, `f'`
on a based resolution of `N`, of finite displacement `Δ = max(Δ(f), Δ(f'))`
(measured with the norm of `V`). Then every `[aχ + ψ]` with `ψ ∈ V` and
`k|a| > ‖ψ‖Δ` lies in `Σ^∞(G;Z)`, and `Σ^∞(G)` contains open neighbourhoods of
`±[χ]`. In particular this holds when `φ` has finite order in `Out(N)`.

*Proof.* Let `H = ⟨N, s⟩ ≤ G` with `s = t^k`. This subgroup has index `k` and
`H = N ⋊_{φ^k} Z`.

1. **Restricted characters.** For `ξ = aχ + ψ` with `ψ ∈ V`, the restriction
   is `ξ|_H = (ka)χ_H + ψ|_N`, where `χ_H(s) = 1`. Moreover
   `ψ|_N ∈ Hom(N,R)^{φ^k}`, and the estimate `|ψ(g)| ≤ ‖ψ‖|g|_V` is unchanged.
2. **Vanishing on `H`.** Theorem A applied to `H`, with lifts of `φ^{∓k}`, gives
   `Tor_*^{ZH}(Nov_{±ξ|_H}(H), Z) = 0` when `k|a| > ‖ψ‖Δ`.
3. **Passing to `G`.** Choose right coset representatives, `G = ⊔_{i=1}^k H g_i`.
   - Splitting supports by cosets gives an isomorphism of right `ZG`-modules
     `Nov_ξ(G) ≅ ⊕_i Nov_{ξ|_H}(H) g_i = Nov_{ξ|_H}(H) ⊗_{ZH} ZG`. This works
     because `ξ(h g_i) = ξ(h) + ξ(g_i)`, so the support condition is checked
     coset by coset.
   - `ZG` is free as a left `ZH`-module, and a `ZG`-resolution of `Z` restricts
     to a `ZH`-resolution. Shapiro's lemma for Tor then gives
     `Tor_*^{ZG}(Nov_ξ(G), Z) ≅ Tor_*^{ZH}(Nov_{ξ|_H}(H), Z) = 0`, and the same
     for `−ξ`.
4. **Conclusion.** Finish as in Corollary A1.
5. **Finite order in `Out(N)`.** If `φ^k = c_{n_0}` is inner, the lifts
   `x ↦ n_0^{±1} x` have displacement `|n_0|_V`. ∎

## 5. Proposition B (uniform certificate, any character)

The mechanism is not special to mapping tori.

**Proposition B.** Let `Γ` be of type `F_∞` and `ξ ≠ 0` a character. Let
`F_* → Z` be a free `ZΓ`-resolution of finite type with finite bases, and
`φ : F_* → F_*` a `ZΓ`-chain map lifting `id_Z`, with matrices `(λ^{(i)}_{jk})`.
Fix a norm on `Hom(Γ,R)` and put `|g| = sup_{‖η‖≤1} |η(g)|`. Suppose

- `c = inf_i v_ξ(φ_i) > 0`, and
- `R = sup_i max{|g| : g ∈ supp λ^{(i)}_{jk}} < ∞`.

Then `Tor_*^{ZΓ}(Nov_{ξ'}(Γ), Z) = 0` whenever `‖ξ' − ξ‖ < c/R`. If
`−ξ` also has such a certificate, with constants `c', R'`, the ball of radius
`min(c/R, c'/R')` around `ξ` lies in `Σ^∞(Γ;Z)` whichever sign convention (I1)
uses; with the sign pinned in §2, the certificate for `ξ` alone suffices. With `[ξ] ∈ Σ^2(Γ)`, (I2) and (I3) then show that `Σ^∞(Γ)` is a
neighbourhood of `[ξ]`.

*Proof.*
1. **Valuation survives perturbation.** `v_{ξ'}(φ_i) ≥ c − ‖ξ'−ξ‖R > 0` in
   every degree, so `u_i = Σ_n φ_i^n` converges over `M = Nov_{ξ'}(Γ)` and
   inverts `1 − φ_i`.
2. **Chain homotopy.** `1 − φ` lifts the zero map of `Z`, so it is chain
   homotopic to `0` by some `h` (comparison theorem). In degree 0 this reads
   `1 − φ_0 = d_1 h_0`. After tensoring with `M`, `u = (1 − φ)^{-1}` commutes
   with `d`, so `1 = u(dh + hd) = d(uh) + (uh)d`.
3. **Conclusion.** `M ⊗ F_*` is contractible, so all Tor groups vanish. The
   last sentence follows from (I1), (I2) and (I3) as in Corollary A1. ∎

**What Proposition B says about Problem 1.13.**
- **Closing the Attempt.** Openness of `Σ^∞(Γ)` at `[ξ]` follows from one
  certificate that is uniform in all degrees at once. The failed Attempt only
  has certificates degree by degree.
- **Why the converse is not automatic.** Even if degreewise certificates
  exist (Bieri–Renz valuation criterion, not re-verified here), nothing known
  forces the ratio `v_ξ(φ_i)/R_i` to stay bounded below.
- **Where Theorem A fits.** Theorem A is a concrete, checkable instance at the
  fibre characters. There the ratio is controlled by the displacement of a
  lift of the monodromy.

## 6. Consequences for a negative answer

Let `G = N ⋊_φ Z` with `N` of type `F_∞`. A non-openness point of `Σ^∞(G)` at
a fibre character `±[χ]` (the one-sided refinement shows which sign) requires
all of the following.

1. Every lift of every power `φ^{-k}` (resp. `φ^k`), on every based resolution
   of `N`, has unbounded displacement.
2. `φ` has infinite order in `Out(N)`.
3. `V ≠ 0`, i.e. `N` has a nonzero `φ`-invariant character. Otherwise
   `S(G) = {±[χ]}`.
4. `N` is not of type `F`.

In terms of the leads in `research/artifacts/zp-sigma-infinity-openness-2026-09-13-part1.md`:

- **Arithmetic depth (M3).** A rank-2 slope group `N_0 ⋊ Z^2` is a mapping
  torus in two ways. At each discrete character with `F_∞` kernel, a witness
  must defeat item 1.
- **Periodic germs in Brin's `Aut(F)`.** For conjugation by `h` with periodic
  germs at `0` and `1`, `V = Hom(F,R)` (both endpoint slope characters are
  invariant). By Theorem A, `Σ^∞(F ⋊_h Z)` is open at `±[χ]` as soon as some
  lift of `h^{∓1}` on a finite-type resolution of `F` (for instance the
  Brown–Geoghegan complex, two cells in each positive dimension) has bounded
  endpoint-slope displacement. We did not compute such a lift. This is the
  first test case to settle in this family.

## 7. What remains open

- **Converses.**
  - Does openness of `Σ^∞(G)` at `[χ]` force some lift of finite
    displacement?
  - Does openness of `Σ^∞(Γ)` at `[ξ]` force a uniform certificate?
- **Discrete fibre characters in general.** Is `Σ^∞(N ⋊ Z)` open at `±[χ]`
  for every `N` of type `F_∞`? Theorem A reduces this to constructing lifts
  of bounded displacement. We found neither a general construction nor an
  obstruction.
- **Non-discrete characters.** At irrational characters and at characters
  with `−[ξ] ∉ Σ^∞`, only Proposition B applies. The negative answer is not
  excluded there by anything in this artifact.
