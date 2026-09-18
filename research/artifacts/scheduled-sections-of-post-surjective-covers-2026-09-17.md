# Scheduled sections of strongly post-surjective SFT covers

Agent `swarm-0917-w8-w8-gs-follow`, wave swarm-0917. Target cone: `gottschalk-surjunctivity-conjecture`,
through `constant-point-sft-domains-admit-no-post-surjective-covers` (CP).

## 0. Conventions

- `G` is a group, `A` a finite alphabet with `q = |A| >= 2`. The shift is `(g.x)(h) = x(g^-1 h)`, so
  `(g^-1 . x)(w) = x(gw)`, as in `strict-pairs-give-dual-failures-on-bounded-defect-domains`.
- `X ⊊ A^G` is an SFT given by a finite window `W ∋ 1` and an allowed set `Adm ⊊ A^W`:
  `x ∈ X` iff `(g^-1 . x)|_W ∈ Adm` for every `g`.
- `F : X → A^G` is an automaton with memory `M ∋ 1` and local rule `f : A^M → A`,
  `F(x)(g) = f((g^-1 . x)|_M)`. Enlarging `M` to contain `1` changes nothing.
- `F` is **strongly post-surjective with lifts in `X`** with constant `Φ` (finite, `1 ∈ Φ` after enlarging).
  This means: for all `x ∈ X` and `z ~ F(x)` there is `x' ∈ X` with `x' ~ x`, `F(x') = z` and
  `Δ(x, x') ⊆ Δ(F(x), z) Φ`. This is the definition used in
  `strict-pairs-give-dual-failures-on-bounded-defect-domains`.

Put

    N = Φ W^-1 W  ∪  Φ M^-1 M,        E = N Φ^-1 ∪ Φ N^-1 ∪ {1},        k = |E|.

`E` is finite and symmetric, and `Φ ⊆ N` (since `1 ∈ W`). Let `C = C_{E,k} ⊆ [k]^G` be the closed invariant
set of **proper colourings**: `κ(h) ≠ κ(he)` for all `h` and all `e ∈ E \ {1}`.

## 1. The single-site lift rule

Fix a total order on `A^Φ`. For `x ∈ X` and `a ∈ A`, define `L_1(x, a)` as follows.
- If `F(x)(1) = a`, put `L_1(x, a) = x`.
- Otherwise, let `Q(x, a)` be the set of `p ∈ A^Φ` such that the configuration `x^p` (equal to `p` on `Φ` and
  to `x` off `Φ`) satisfies:
  (i) `(h^-1 . x^p)|_W ∈ Adm` for every `h ∈ Φ W^-1`;
  (ii) `F(x^p)(h) = F(x)(h)` for every `h ∈ Φ M^-1 \ {1}`, and `F(x^p)(1) = a`.
  Put `L_1(x, a) = x^p` for the least `p ∈ Q(x, a)`.

**Lemma 1.** `Q(x, a)` is nonempty, `L_1(x, a) ∈ X`, `F(L_1(x, a)) = F(x)` off `{1}`, and
`F(L_1(x,a))(1) = a`. Whether `p ∈ Q(x, a)` depends only on `p`, `a` and `x|_N`.

*Proof.* Let `z` equal `F(x)` except `z(1) = a`, so `Δ(F(x), z) = {1}`. Strong post-surjectivity gives
`x' ∈ X` with `F(x') = z` and `Δ(x, x') ⊆ Φ`. So `x' = x^p` for `p = x'|_Φ`, and `p` satisfies (i) and (ii).
Hence `Q(x, a)` is nonempty.

Take any `p ∈ Q(x, a)`. A window `hW` that misses `Φ` sees the same letters in `x^p` as in `x ∈ X`. A window
that meets `Φ` has `h ∈ Φ W^-1` and is covered by (i). So `x^p ∈ X`.

The value `F(x^p)(h)` reads `hM`. If `hM` misses `Φ`, it equals `F(x)(h)`. Otherwise `h ∈ Φ M^-1`, and (ii)
applies. So `F(x^p)` agrees with `F(x)` off `{1}` and takes the value `a` at `1`.

Condition (i) reads `x` on `Φ W^-1 W ⊆ N`. Condition (ii) reads `x` on `Φ M^-1 M ⊆ N`. The test
`F(x)(1) = a` reads `M ⊆ Φ M^-1 M` (using `1 ∈ Φ ∩ M`). `∎`

For `g ∈ G`, put `L_g(x, a) = g . L_1(g^-1 . x, a)`. Then:
- `L_g` changes `x` only on `gΦ` and depends only on `x|_{gN}` and `a`;
- `L_g(x, a) ∈ X`, `F(L_g(x,a))(g) = a`, and `F(L_g(x,a)) = F(x)` off `{g}`;
- `h . L_g(x, a) = L_{hg}(h . x, a)` (equivariance).

## 2. Simultaneous lifts at separated sites

**Lemma 2.** Let `x ∈ X`, `z ∈ A^G`, and let `S ⊆ G` satisfy `g^-1 g' ∉ E` for distinct `g, g' ∈ S`. Define
`x^S` by `x^S = L_g(x, z(g))` on `gΦ` for each `g ∈ S`, and `x^S = x` off `SΦ`. Then:
1. `x^S` is well defined, and `x^S ∈ X`;
2. `F(x^S)(g) = z(g)` for `g ∈ S`, and `F(x^S)(h) = F(x)(h)` for `h ∉ S`.

*Proof.* For distinct `g, g' ∈ S`: if `gΦ` met `g'N`, then `g^-1 g' ∈ Φ N^-1 ⊆ E`. So `gΦ ∩ g'N = ∅`, and in
particular `gΦ ∩ g'Φ = ∅` (as `Φ ⊆ N`). So the write regions are disjoint and `x^S` is well defined.

*Windows.* Suppose a window `hW` meets `g'Φ`. Then `hW ⊆ g'Φ W^-1 W ⊆ g'N`, so `hW` misses every other `gΦ`.
On `hW` the configuration `x^S` therefore agrees with `L_{g'}(x, z(g'))`, which lies in `X`. A window that
meets no write region sees `x`. So `x^S ∈ X`. (Only the local check is used, not closedness of `X`.)

*Outputs.* Suppose `hM` meets `g'Φ`. Then `hM ⊆ g'Φ M^-1 M ⊆ g'N`, so `hM` misses every other write region,
and `F(x^S)(h) = F(L_{g'}(x, z(g')))(h)`. By Lemma 1 this is `z(g')` if `h = g'`, and `F(x)(h)` otherwise. If
`hM` meets no write region, then `F(x^S)(h) = F(x)(h)`. For `h = g ∈ S`, `gM` meets `gΦ` (both contain `g`),
so this last case never applies to `h ∈ S`. `∎`

The same-colour classes `S_i = κ^-1(i)` of a proper colouring `κ ∈ C` satisfy the hypothesis of Lemma 2:
`g' = ge` with `e ∈ E \ {1}` forces `κ(g') ≠ κ(g)`.

## 3. Theorem A (scheduled sections)

**Theorem A.** Let `Ω` be a compact metrizable space with a continuous `G`-action, and let
`κ : Ω → C` and `ξ : Ω → X` be continuous and equivariant. For `(z, ω) ∈ A^G × Ω` put `x_0 = ξ(ω)` and
`x_i = (x_{i-1})^{S_i}` with `S_i = κ(ω)^-1(i)`, for `i = 1, ..., k` (Lemma 2 with target `z`). Put
`s(z, ω) = x_k`. Then:
1. `s` is equivariant for the diagonal action, and `s(z, ω) ∈ X`;
2. `F(s(z, ω)) = z` for all `(z, ω)`;
3. `s(z, ω)(1)` depends only on `z|_P` and on `(κ(ω)|_P, ξ(ω)|_P)`, where `P = (Φ^-1 N)^k` depends only on
   `W, M, Φ`. In particular `s` is continuous.

*Proof.* By Lemma 2 and induction on `i`, each `x_i ∈ X`. After round `i`, `F(x_i) = z` on
`κ^-1({1, ..., i})`: round `i` sets the value on `κ^-1(i)` and does not touch the values on `κ^-1(j)`,
`j ≠ i`. So `F(x_k) = z`.

*Locality.* Distinct `g, g' ∈ hΦ^-1` have `g^-1 g' ∈ Φ Φ^-1 ⊆ E`, so at most one site of each colour class
writes at `h`. Hence `x_i(h)` depends only on `x_{i-1}` on `hΦ^-1 N`, on `z` on `hΦ^-1` and on `κ` on
`hΦ^-1`. Since `1 ∈ N`, `Φ^-1 ⊆ Φ^-1 N`, and induction gives item 3 with `P = (Φ^-1 N)^k`.

*Equivariance.* Every `L_g` is equivariant, and the colour classes of `h . κ` are the `h`-translates of
those of `κ`. `∎`

**Corollary A1 (controlled form).** Suppose in addition that `Ω` is zero-dimensional. Then
`Σ(z, ω) = (s(z, ω), ω)` is an `Ω`-controlled automaton in the sense of
`compressible-base-controlled-automata-are-strict` and `measured-controlled-surjunctivity-is-envelope-invariant`,
by item 3. The cell of `ω` is the value of `(κ(ω)|_P, ξ(ω)|_P)`, and the partition into these cells is finite
and clopen. `Σ` is **strict**:
- every fibre `s(·, ω)` is injective, because `F ∘ s(·, ω) = id`;
- no fibre is surjective, because its image lies in `X ⊊ A^G`.
Its decoder `F` does not depend on the base point.

**Remark (why a colouring is needed).** At a `G`-fixed point of `Ω`, a continuous equivariant `κ` would give a
`G`-invariant proper colouring. None exists unless `E = {1}`. So the base can never be a point, and `κ(Ω)`
avoids the constants. This is the obstruction recorded in Section 6.

## 4. Borel proper colourings of Bernoulli shifts

Let `G` be countably infinite and `B` a finite alphabet with `|B| >= 2`, and let `u_B` be the uniform product
measure. Let `Fr ⊆ B^G` be the free part, `{w : g . w ≠ w for all g ≠ 1}`.

**Lemma 3.** `Fr` is Borel, invariant and `u_B`-conull.

*Proof.* Borel and invariant are clear. Fix `g ≠ 1`. The right cosets `⟨g⟩h` partition `G`, and a
`g`-fixed `w` is constant on each of them.
- If `g` has infinite order, each coset is infinite, so `u_B(Fix g) = 0`.
- If `g` has finite order `n >= 2`, there are infinitely many cosets, each of size `n`, and `w` must be
  constant on each. That has probability `|B|^(1-n) < 1` per coset, independently, so `u_B(Fix g) = 0`.
`G` is countable, so `Fr` is conull. `∎`

**Lemma 4 (greedy Borel colouring).** For every finite symmetric `E ∋ 1` there is a Borel equivariant
`β : Fr → C_{E,|E|}`.

*Proof.* This is the standard Kechris–Solecki–Todorcevic argument (Proposition 4.6 of *Borel chromatic
numbers*, Adv. Math. 141 (1999); not re-read at source here), written out so that nothing is imported.

Let `(U_n)` be a countable clopen basis of `B^G`. Put
`A_n = {w ∈ U_n ∩ Fr : e . w ∉ U_n for all e ∈ E \ {1}}`.
- Each `A_n` is Borel.
- Each `A_n` is independent: `w` and `e . w` (with `e ∈ E \ {1}`) cannot both lie in `A_n ⊆ U_n`.
- The `A_n` cover `Fr`. For `w ∈ Fr` the finitely many points `e . w` with `e ≠ 1` differ from `w`, so some
  `U_n` contains `w` and none of them.

Put `B_n = A_n \ ∪_{m<n} A_m`, a Borel partition of `Fr`. Define `c : Fr → [k]`, `k = |E|`, by recursion on `n`:
for `w ∈ B_n`, `c(w)` is the least colour not in `{c(e . w) : e ∈ E \ {1}, e . w ∈ ∪_{m<n} B_m}`. At most
`k - 1` colours are excluded, so this is well defined. It is Borel by induction on `n`.

Since `E` is symmetric, `w' = e . w` iff `w = e^-1 . w'`. So whichever of the two points is coloured later
avoids the colour of the other, and points of one `B_n` are never neighbours. Hence
`c(e . w) ≠ c(w)` for all `w ∈ Fr` and `e ∈ E \ {1}`.

Put `β(w)(h) = c(h^-1 . w)`. Then:
- `β(g . w)(h) = c(h^-1 g . w) = β(w)(g^-1 h) = (g . β(w))(h)`, so `β` is equivariant;
- `β(w)(he) = c(e^-1 . (h^-1 . w)) ≠ c(h^-1 . w) = β(w)(h)` for `e ∈ E \ {1}` (as `e^-1 ∈ E \ {1}`), so
  `β(w) ∈ C`. `∎`

## 5. Theorem B (measured consequences)

Let `S : A^G × C × X → X` be the section of Theorem A for the universal base `Ω = C × X`, with `κ` and `ξ` the
two coordinate projections. `S` is continuous and equivariant, and `F(S(z, κ, x_0)) = z`. Let `p ∈ A^{Ω_0}` be
a pattern with `[p] ∩ X = ∅`. It exists because `X` is closed, invariant and proper: if every pattern occurred
in `X`, then `X` would be dense, hence equal to `A^G`.

**Theorem B.** Let `G` be countably infinite, `X ⊊ A^G` an SFT, and `F : X → A^G` strongly post-surjective with
lifts in `X`.

1. **(Invariant measure.)** If `X` carries a `G`-invariant Borel probability `μ`, then `G` carries a strict
   `Ω`-controlled automaton over the alphabet `A`. Its base `Ω` is compact, metrizable and zero-dimensional, and
   carries an invariant probability of full support. So `G` is not measured-controlled surjunctive in the sense of
   `measured-controlled-surjunctivity-is-envelope-invariant`.
2. **(Bernoulli-factor measure.)** Suppose there are a finite `B`, `|B| >= 2`, and a Borel equivariant
   `ψ : Y → X` defined on an invariant `u_B`-conull Borel set `Y ⊆ B^G`. Put `A' = A × B`, `q' = q|B|`,
   `δ = -log(1 - q'^(-|Ω_0|))` and `D = |Ω_0 Ω_0^-1|`. Then for every `k >= 1`

       h^Rok_G(((A')^k)^G, uniform) <= k (log q' - δ/D) + log 3,

   which is `< k log q'` once `k > D log 3 / δ`. So the uniform Bernoulli shift over `G` with alphabet
   `(A')^k` does not have maximal Rokhlin entropy.
3. **(Constant points.)** If `X` contains a constant configuration `c`, both conclusions hold, with `μ = δ_c` in
   item 1 and `ψ ≡ c` in item 2.

*Proof of 1.* Take `β : Fr → C` from Lemma 4 for `B = A`, and `λ = β_* u_A`, an invariant probability on `C`.
Let `Ω = supp λ × supp μ ⊆ C × X`, with the invariant probability `λ ⊗ μ`. The support of a product measure on
a second countable space is the product of the supports, so `λ ⊗ μ` has full support on `Ω`. `Ω` is closed and
invariant in the zero-dimensional compact metrizable space `[k]^G × A^G`. Apply Corollary A1 with the
restrictions of the two projections. `∎`

*Proof of 2.* Let `Y' = Y ∩ Fr ⊆ B^G`, invariant and conull by Lemma 3. Take `β : Fr → C` from Lemma 4. Define,
on `A^G × Y'`,

    Θ(z, w) = ( S(z, β(w), ψ(w)), w ).

`Θ` is Borel and equivariant. It has the Borel left inverse `(x, w) ↦ (F(x), w)`, so it is injective. Identify
`A^G × B^G` with `(A')^G`. Then `ν = Θ_* (u_A ⊗ u_B)` is an invariant probability on `(A')^G`, and `Θ` is an
isomorphism from `((A')^G, u_{A'})` to `((A')^G, ν)`. The `A`-coordinate of `ν`-a.e. point lies in `X`. So
`ν([p']) = 0` for any `p' ∈ (A')^{Ω_0}` whose `A`-part is `p`. The displayed bound is the ESTABLISHED
`strict-automaton-lowers-bernoulli-rokhlin-entropy` for the alphabet `A'` and the measure `ν`. That claim is
stated for every invariant `ν` isomorphic to the uniform Bernoulli shift and missing a cylinder (Theorem 1 of
`research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md`). `∎`

*Proof of 3.* `c` is shift-fixed, so `δ_c` is invariant and `ψ ≡ c` is equivariant. `∎`

**Variant for item 2 at constant points, with no amplification of the alphabet.**
`Θ(z) = S(z, β(z), c)` on `Fr ⊆ A^G` is a Borel equivariant injection into `X`. So `Θ_* u_A` is isomorphic to
`u_A` and misses `[p]`. The bound then holds with `q`, `|Ω_0|` in place of `q'`.

## 6. The gap between CP and Gottschalk is exactly de-colouring

Call `(X, F)` a **cover pair** over `A^G` if `X ⊊ A^G` is an SFT and `F : X → A^G` is strongly post-surjective
with lifts in `X`. A **section** of a cover pair is a continuous equivariant `s : A^G → X` with `F ∘ s = id`.

**Proposition C.** For every group `G`, the following are equivalent:
1. `G` is not surjunctive;
2. over some `A^G` there is a cover pair with a section;
3. over some `A^G` there is a cover pair with a section whose domain `X` contains a constant configuration.

*Proof.*
- (1 ⇒ 3). A strict automaton `τ` has a decoder `σ`, a cellular automaton with `σ ∘ τ = id`
  (`gottschalk-via-proper-domain-duality`, step 1). By `strict-pairs-give-dual-failures-on-bounded-defect-domains`
  (items 1, 2 and 5, as used in `gottschalk-via-constant-point-domains`), `(X_R, σ|_{X_R})` is a cover pair with `τ(A^G) ⊆ X_R`. So `τ` is a section, and
  `τ(a^G) ∈ X_R` is constant.
- (3 ⇒ 2) is trivial.
- (2 ⇒ 1). A section `s` is continuous and equivariant `A^G → A^G`, hence a cellular automaton
  (Curtis–Hedlund–Lyndon, valid for every group). It is injective because `F ∘ s = id`, and not surjective
  because `s(A^G) ⊆ X ≠ A^G`. `∎`

So CP(G) says that no cover pair with a constant point exists, and Gottschalk(G) says that no cover pair has a
section. Theorem A says that **every cover pair has a section over the colouring base `C`**. In other words,
`s(·, κ)` depends continuously and equivariantly on the pair `(z, κ)`. Hence:

> For a surjunctive group `G`, CP(G) holds iff every cover pair over `G` with a constant point has a section
> (both sides then say that there are no such pairs). A section is exactly the colouring-free form of the
> scheduled section that Theorem A always provides.

This is the same step at which the supplement of `irs-surjunctivity-iff-pmp-graphing-surjunctivity` stays open:
table processes that are proper subshifts, here the colourings.

**Obstruction 1 (fixed points).** A section must satisfy `Stab(s(z)) ⊇ Stab(z)` for every `z`. So for every
subgroup `H ≤ G`, `F` must map `Fix_H(X)` onto `Fix_H(A^G)`. In particular, every constant `a^G` must be the
image of a constant of `X`. Scheduled lifts give no such thing: at `z = a^G`, `s(z, κ)` has only the symmetry of
`κ`. So a cover pair in which some constant `a^G` is not `F` of a constant of `X` has no section at all. Such a pair is not a
Gottschalk counterexample by itself; only CP excludes it.

As a consequence, CP can be weakened without losing the route
`gottschalk-via-constant-point-domains`. It suffices to exclude cover pairs for which
`F(Fix_H(X)) = Fix_H(A^G)` for every `H`, because domains from strict pairs have this property (their section is
`τ`). This is recorded as a remark only.

**Obstruction 2 (buffers).** Suppose one tries to de-colour by lifting on a region `R` and leaving the rest at
`c`. The interface sites of `R` must keep `F = F(c)` there, so their `z`-data is lost. Over a nonamenable `G`,
the interface of every finite region is a fixed fraction of its volume. And `F` has no spare capacity per site:
- the iterate `F^n` is again a cover pair on `X_n = X ∩ F^-1 X ∩ ... ∩ F^-(n-1) X`;
- but `F^n` has the same alphabet on both sides, so iterating gains no room in which to store the lost interface
  data.

This is the same boundary term that stops every model-free Rokhlin lower bound
(`bernoulli-rokhlin-entropy-maximal-for-every-group`, Attempts). Theorem B converts it into that problem rather
than resolving it.

**Dead attempt (converse via dual failures).** One would like to replace each lifted site by a canonical
representative avoiding a fixed forbidden word `u`. The replacements have to be iterated, and the iteration need
not terminate: a defect can be pushed off to infinity along a ray, and no finite window certifies that the
process has stopped. So it gives no continuous section. Where it dies: termination of the replacement process.

## 7. Reduction of CP to countably infinite finitely generated groups

**Lemma 5.** Let `(X, F)` be a cover pair over `A^G` with a constant point `c`, window `W`, memory `M` and lift
constant `Φ`. Put `H = ⟨W ∪ M ∪ Φ⟩`, let `X_H ⊆ A^H` be the SFT with the same window and allowed set, and let
`F_H` be the automaton with the same local rule. Then `(X_H, F_H)` is a cover pair over `A^H` with the constant
point `c|_H`. If `H` is finite, no such pair exists.

*Proof.*
- **Proper.** `X_H` is proper, because the allowed set is not all of `A^W` (otherwise `X = A^G`).
- **Extension.** Given `x ∈ X_H` and `z ~ F_H(x)`, define `x̃ ∈ A^G` to be `x` on `H` and `c` off `H`. Every
  window `gW` lies in the single left coset `gH`, so `x̃ ∈ X`, and `F(x̃)|_H = F_H(x)`.
- **Lift.** Let `z̃` be `z` on `H` and `F(x̃)` off `H`. A lift `x'` of `z̃` has
  `Δ(x̃, x') ⊆ Δ(F(x̃), z̃) Φ ⊆ HΦ = H`. So `x'|_H ∈ X_H` is the required lift for `F_H`, with the same `Φ`.
- **Finite `H`.** If `H` is finite, every `z ∈ A^H` is asymptotic to `F_H(x)`, so `F_H` is onto `A^H`. But
  `|X_H| < |A^H|`, a contradiction. `∎`

So a counterexample to CP at any group gives one at a countably infinite finitely generated subgroup.

## 8. Consistency checks

- **Sofic and amenable `G`.** Bernoulli Rokhlin entropy is maximal there, and CP is known there
  (`proper-sft-covers-exclude-finite-orbits-and-sofic-constants`, and the entropy sketch on the CP claim).
  Theorem B agrees with both.
- **Arrow shifts.** `nonamenable-groups-carry-arrow-shift-strict-automata` gives strict controlled automata over
  every nonamenable group, based on the arrow shift `X_S`. `X_S` carries no invariant probability, by mass
  transport: under the map `f_φ`, every site sends one unit of mass and receives at least two. So these do not
  violate MCS, and they are consistent with Theorem B.1, which produces only measured bases.
- **Measureless bases.** `compressible-base-controlled-automata-are-strict` builds strict controlled automata over
  measureless bases. Theorem B.1 needs the measure `λ ⊗ μ`, which exists exactly because the base is a colouring
  shift of a Bernoulli process. This is why Theorem B does not collapse into that swindle.
