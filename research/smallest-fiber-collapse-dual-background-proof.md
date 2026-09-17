---
rg: 2
id: smallest-fiber-collapse-dual-background-proof
kind: route
title: With the smallest fiber as background the window count reverses sign, and charge noncreation for the inverse base finishes
target: smallest-fiber-collapse-lifts-are-surjective
requires:
  - bijective-ca-preserve-uniform-bernoulli-measure
  - finite-injective-charge-noncreation-forces-surjectivity
---

Complete proof. Notation as in the target. Automata act by `Φ(y)(h) = φ((h^{-1} y)|_N)`, so `Φ(y)(h)` depends only
on `y|_{hN}`. By Curtis–Hedlund–Lyndon, which holds over every group, a bijective automaton has a cellular inverse.
A configuration `u ∈ A^G` is *finite* if `E(u) = {g : u(g) != a0}` is finite. Write `Q0 = Q_{a0}`, `q = s = |Q0|`.

The argument follows `collapse-lift-bernoulli-window-count-proof` with the background moved to the smallest fiber.
Steps 0, 2, 3 and 5 are restated, because only their hypotheses (not the fiber comparison) matter.

## Step 1'. Fixing the constants

`Φ` sends constant configurations to `G`-invariant configurations, which are constant, and it is injective. So it
permutes the finitely many constants, and some power `Φ^j` fixes every constant. `Φ^j` is an injective automaton,
`r ∘ Φ^j = τ^j ∘ r`, `τ^j` is bijective, and `Φ^j` is surjective iff `Φ` is. Replace `Φ, τ` by `Φ^j, τ^j`. Then
`τ(a^G) = r(Φ(p^G)) = a^G` for `p ∈ Q_a`, so `τ` fixes `a0^G`.

`Φ` maps `Q0^G = r^{-1}(a0^G)` injectively and equivariantly into `r^{-1}(τ(a0^G)) = Q0^G`; call the map `T_0`.
- If `s >= 2` and `T_0` is not surjective, then `T_0` is a strict automaton on `s` letters and `s ∈ NS(G)`. Done.
- Otherwise `T_0` is bijective. For `s = 1` this is trivial. Let `S = T_0^{-1}`, with memory `N'`.
  `bijective-ca-preserve-uniform-bernoulli-measure` states "Let `G` be any group, `A` a finite alphabet, `mu` the
  uniform product measure on `A^G`, and `tau: A^G -> A^G` a bijective cellular automaton. Then `tau_* mu = mu`." So
  `(T_0)_* μ = μ` for the uniform measure `μ` on `Q0^G`. For `s = 1`, `μ` is a point mass and this also holds.

## Step 0. `τ` has memory `N`

Let `x, x'` agree on `hN`. Choose `y, y'` with `r y = x`, `r y' = x'` and `y = y'` on `hN`. Then
`τ(x)(h) = r(Φ(y)(h)) = r(Φ(y')(h)) = τ(x')(h)`.

## Step 2. The fiber maps

Fix a finite `u`. Write `E = E(u)`, `E' = E(τ u)`, `F1 = E N^{-1}`. If `h ∉ F1` then `hN ∩ E = ∅`, so by Step 0
`τ(u)(h) = τ(a0^G)(h) = a0`. Hence `E' ⊆ F1`, and `τ u` is finite. Identify `r^{-1}(u) = Π_g Q_{u(g)}`. Restricting
`Φ` gives an injective map `T_u : r^{-1}(u) -> r^{-1}(τ u)`.

Fix `p0 ∈ Q0`.
- For `z ∈ r^{-1}(u)`, let `z̃ ∈ Q0^G` equal `z` off `E` and `p0` on `E`. For `h ∉ F1`, `z` and `z̃` agree on `hN`,
  so `T_u(z)(h) = T_0(z̃)(h)`.
- For `y ∈ r^{-1}(τ u)`, let `ȳ ∈ Q0^G` equal `y` off `E'` and `p0` on `E'`.

Put `ψ(z) = (S(ȳ), y|_{E'})` with `y = T_u(z)`. It is injective, since `S` is a bijection, `(ȳ, y|_{E'})` determines
`y`, and `T_u` is injective.

- **Far from the defect.** Put `F = F1 N'^{-1} ∪ E`, and let `g ∉ F`. Every `h ∈ gN'` lies outside `F1 ⊇ E'`, so
  `ȳ(h) = y(h) = T_0(z̃)(h)`. Hence `S(ȳ)(g) = S(T_0 z̃)(g) = z̃(g) = z(g)`.
- **A fixed pattern.** `T_0(S(ȳ)) = ȳ`, which equals `p0` on `E'`.

## Step 3. The window count, with reversed sign

Choose a finite `V ⊇ F ∪ E'N`, and fix `c ∈ Q0^{G \ V}`.
- **Domain.** `D_c = {z ∈ r^{-1}(u) : z|_{G \ V} = c}` has `|D_c| = q^{|V| - |E|} Π_{g ∈ E} |Q_{u(g)}|`.
- **Target.** For `z ∈ D_c`, write `ψ(z) = (w, e)`. Then `w|_{G \ V} = c`, `T_0(w)|_{E'} = p0^{E'}`, and
  `e ∈ Π_{E'} Q_{τu(g)}`. `T_0(w)|_{E'}` depends only on `w|_{E'N}`, and `E'N ⊆ V`. So the set
  `R = {w_V ∈ Q0^V : T_0(w_V ∪ c)|_{E'} = p0^{E'}}` does not depend on `c`, and by Step 1'
  `|R| = q^{|V|} μ(T_0^{-1}[p0^{E'}]) = q^{|V|} μ([p0^{E'}]) = q^{|V| - |E'|}`.
- **Injection.** `z ↦ (ψ(z)_1|_V, ψ(z)_2)` is injective on `D_c`, since `ψ(z)_1|_{G \ V} = c` there. So

      q^{|V| - |E|} Π_{g ∈ E} |Q_{u(g)}|  <=  q^{|V| - |E'|} Π_{g ∈ E'} |Q_{τu(g)}|.            (*)

Take logarithms, with `w'(a) = log(|Q_a| / s)`. This is `0` at `a0` and strictly positive at every `a != a0`, by
uniqueness of the smallest fiber. Then

    W'(u) = Σ_{g ∈ E} w'(u(g))  <=  Σ_{g ∈ E'} w'(τu(g)) = W'(τ u)      for every finite u.

## Step 4. Charge noncreation for the inverse base

Here the bijectivity of `τ` is used. Let `σ = τ^{-1}`, a cellular automaton with some memory `M`. It fixes `a0^G`.
- **Finite to finite.** If `v` is finite and `h ∉ E(v) M^{-1}`, then `v` agrees with `a0^G` on `hM`, so
  `σ(v)(h) = a0`. So `σ` maps finite configurations to finite ones.
- **Charge.** For finite `v`, `u = σ v` is finite, and Step 3 gives `W'(σ v) = W'(u) <= W'(τ u) = W'(v)`.
- **Injectivity.** `σ` is injective.

`finite-injective-charge-noncreation-forces-surjectivity` has these hypotheses: "let tau:A^G->A^G be a cellular
automaton fixing 0^G. Give each nonzero symbol a strictly positive real charge w(a), and put w(0)=0. ... Suppose tau
is injective on finitely supported configurations and W(tau(x)) <= W(x) for every finite x." Its conclusion is:
"Then equality holds for every finite x." Apply it to `σ`, with quiescent symbol `a0` and charge `w'`. Then
`W'(σ v) = W'(v)` for every finite `v`, that is, `W'(τ u) = W'(u)` for every finite `u`.

Also, `τ` and `σ` both preserve finiteness, so `τ` restricts to a bijection of the finite configurations.

## Step 5. `Φ` is surjective

By Step 4, equality holds in `(*)`. So the injection of Step 3 maps `D_c`, which has
`q^{|V|-|E|} Π_E |Q_{u(g)}| = q^{|V|-|E'|} Π_{E'} |Q_{τu(g)}|` elements, onto `R × Π_{E'} Q_{τu(g)}`.

Let `y' ∈ r^{-1}(τ u)`. Put `w = S(ȳ')` and `c = w|_{G \ V}`. Then `T_0(w)|_{E'} = ȳ'|_{E'} = p0^{E'}`, so
`(w|_V, y'|_{E'}) ∈ R × Π_{E'} Q_{τu(g)}`. Hence there is `z ∈ D_c` with `ψ(z)_1|_V = w|_V` and
`ψ(z)_2 = y'|_{E'}`. Since `ψ(z)_1|_{G \ V} = c = w|_{G \ V}`, we get `ψ(z) = (w, y'|_{E'})`. With `y = T_u(z)` this
gives `S(ȳ) = S(ȳ')`, so `ȳ = ȳ'`, and `y|_{E'} = y'|_{E'}`. So `y = y'`. Thus `Φ(r^{-1}(u)) = r^{-1}(τ u)`.

Every finite `v` equals `τ u` for the finite `u = σ v`. So `Φ(B^G)` contains `r^{-1}(v)` for every finite `v`, which
is every `y` with finitely many sites outside `Q0`. These are dense in `B^G`: extend any finite pattern by `p0`
outside it. `Φ(B^G)` is compact, hence closed, so `Φ` is surjective.

Undo the replacement of Step 1': the original `Φ` is surjective because its power is. ∎

## Where each hypothesis is used

- **Unique smallest fiber.** It makes `w'` vanish only at `a0`. That is needed in Step 4.
- **Bijectivity of `τ`.** Used only in Step 4. The sign of `(*)` controls `τ^{-1}`, not `τ`.
  - Largest fiber: `(*)` says `τ` loses charge, so injectivity of `τ` suffices.
  - Smallest fiber: `(*)` says `τ` gains charge, which is compatible with a strict `τ`. So the base must be assumed
    bijective.
- **Injectivity of `Φ`.** Used in Step 1' (`T_0`) and in Step 2 (`ψ`).
- **Group structure.** Used only through the two imports, both over every group.
- **`s = 1`.** `T_0` is the identity of a point, `R = Q0^V` is a single point, and the proof reduces to a count of
  data at non-star sites. This is the autonomous star design of
  `count-raising-reversible-automata-lower-biased-rokhlin-entropy`.
