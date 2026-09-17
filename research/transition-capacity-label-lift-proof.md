---
rg: 2
id: transition-capacity-label-lift-proof
kind: route
title: Give each letter as many label copies as its capacity and carry labels along by inclusion; the lift is injective with a missing cylinder, and a numerical semigroup count gives the sizes
target: transition-digraph-capacity-lifts-give-nonsurjunctive-sizes
requires:
  - finite-injective-charge-noncreation-forces-surjectivity
---

Complete proof. Notation as in the target. The import is used only in item 4.

## Item 1. The capacity lift

Let `n` be a capacity. Put `B = {(a, i) : a ∈ A, 0 <= i < n(a)}`, so `|B| = Σ_a n(a)`, and let `r(a, i) = a`,
applied sitewise as `r : B^G -> A^G`. For `y ∈ B^G` write `y(g) = (x(g), i_g)`, so `x = r(y)`. Define

    Φ(y)(g) = ( τ(x)(g), i_g ).

- **Well defined.** `(x(g), τ(x)(g)) ∈ R(τ)`, so `i_g < n(x(g)) <= n(τ(x)(g))`. Hence `Φ(y)(g) ∈ B`.
- **Cellular automaton.** `Φ(y)(g)` depends only on `y|_{gM}`, since `1 ∈ M` and `τ(x)(g)` depends on `x|_{gM}`.
  The rule is the same at every site, so `Φ` is `G`-equivariant.
- **Lift.** `r ∘ Φ = τ ∘ r` by construction.
- **Injective.** If `Φ(y) = Φ(y')`, apply `r`: `τ(r y) = τ(r y')`, so `r y = r y'` by injectivity of `τ`. The
  second coordinates give `i_g = i'_g` for all `g`. So `y = y'`.
- **Not surjective.** Choose `v ∈ A^G \ τ(A^G)` and any `w ∈ B^G` with `r(w) = v`, e.g. `w(g) = (v(g), 0)`. If
  `w = Φ(y)`, then `v = r(Φ(y)) = τ(r(y))`, a contradiction.

So `Φ` is strict over `|B| = Σ_a n(a)` symbols, and `Σ_a n(a) ∈ NS(G)`.

## Item 2. Upsets

If `U` is an upset, then `n = s·1_{A \ U} + m·1_U` with `1 <= s <= m` is a capacity. For `(a, b) ∈ R(τ)`, either
`a ∈ U`, so `b ∈ U` and `n(a) = n(b) = m`, or `a ∉ U`, so `n(a) = s <= n(b)`. The sum is `bm + zs`. The
equivalence of upsets with sitewise absorbing sets is the definition of `R(τ)`: its pairs are exactly the
`(x(g), τ(x)(g))`.

## Item 3. Arithmetic

**Classes and upsets.** Every upset is a union of classes, since `a` and `a'` in one class reach each other. So
`g(τ)` divides every upset size. Conversely, for a class `C` let `↑C` be the set of letters reachable from `C`. It is
an upset. So is `↑C \ C`: if `a ∈ ↑C \ C` and `(a, b) ∈ R(τ)`, then `b ∈ ↑C`, and `b ∈ C` would put `a` in `C`,
because `C` reaches `a` and `a` reaches `b ∈ C`. Hence `|C| = |↑C| - |↑C \ C|`, and the gcd of upset sizes divides
every class size.

**All large multiples.** For upsets `U_1, ..., U_p` and integers `c_i >= 0`, `n = 1 + Σ c_i 1_{U_i}` is a capacity,
since each indicator of an upset is monotone along `R(τ)`. Its sum is `k + Σ c_i |U_i|`. The upset sizes generate a
numerical semigroup in `dZ`, `d = g(τ)`, which contains every large multiple of `d` (Schur). Since `d | k`,
`k + (that semigroup)` also contains every large multiple of `d`.

**Explicit bound for one upset.** Let `d = gcd(b, z)`, `b = d b'`, `z = d z'`, and `n' >= b'(b' + z')`. Since
`gcd(b', z') = 1`, there is `s ∈ {1, ..., b'}` with `z' s ≡ n' (mod b')`. Put `m = (n' - z' s)/b'`. Then
`m >= (b'^2 + b' z' - z' b')/b' = b' >= s`, so item 2 gives `d n' = bm + zs ∈ NS(G)`.

**Powers of two.** If `d = 2^i`, every `2^j` with `2^(j-i) >= b'(b' + z')` is such a multiple. The artifact checks
the bound for all `1 <= b, z <= 15` up to `1200`, and checks `64 = 7·7 + 3·5`.

## Item 4. No singleton upset

Suppose `U = {a}` is an upset of a strict `τ`. Then `τ(a^G)(g) = a` at every site, so `τ` fixes `a^G`. Give charge
`w(a) = 0` and `w(c) = 1` for `c != a`. For a finitely supported `x` (relative to `a`), every site with `x(g) = a`
has `τ(x)(g) = a`. So the support of `τ(x)` lies inside that of `x`, and `W(τ x) <= W(x)`. `τ` is injective, hence
injective on finitely supported configurations. The import
`finite-injective-charge-noncreation-forces-surjectivity` reads: "let tau:A^G->A^G be a cellular automaton fixing
0^G. Give each nonzero symbol a strictly positive real charge w(a), and put w(0)=0. [...] Suppose tau is injective on
finitely supported configurations and W(tau(x)) <= W(x) for every finite x. Then equality holds for every finite x.
Moreover, tau is bijective on each finite-configuration charge sector, and is surjective on A^G." So `τ` is
surjective, a contradiction.

## Item 5. Equivalences

- If a strict `τ` has `g(τ) = 2^i`, item 3 gives `2^j ∈ NS(G)`. This contradicts binary-power surjunctivity, and
  it supplies the witness asked for by the bridge.
- Conversely, the classes partition `A`, so `g(τ) | k`. A strict automaton on `2^j` symbols therefore has `g(τ)` a
  power of two.

## Item 6. Exactness for sitewise labels

Let `r : B -> A` have fibers `Q_a`, and let `Φ` lift `τ` with `Φ(y)(g) = (τ(x)(g), λ(x|_{gN}, i_g))`, where
`i_g ∈ Q_{x(g)}` is the label of `y(g)` and `λ(x|_{gN}, ·)` is injective into `Q_{τ(x)(g)}` for each base
pattern. For `(a, b) ∈ R(τ)` pick `x` with `x(g) = a` and `τ(x)(g) = b`. The injection `Q_a -> Q_b` gives
`|Q_a| <= |Q_b|`. So `n(a) = |Q_a|` is a capacity and `|B| = Σ n(a)`. Item 1 realizes every capacity sum in this
form, with `λ` the inclusion.

## Checks

- **The capacity condition is needed only on realized pairs.** The local rule reads `x(g)` because `1 ∈ M`, so
  `R(τ)` is computable from the table `μ`.
- **Finite sanity model.** The artifact also enumerates random rules with memory `{0, 1}` on `Z/4` over three letters,
  including permutation and shift-permutation rules. It checks that upsets are sitewise absorbing, that the gcd of
  class sizes equals the gcd of upset sizes, that `r ∘ Φ = τ ∘ r`, and that `Φ` is injective exactly when `τ` is.
