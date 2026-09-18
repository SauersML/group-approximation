---
rg: 2
id: collapse-lift-bernoulli-window-count-proof
kind: route
title: The bijective rest map preserves the uniform measure, so a window count bounds the fiber charge and charge noncreation finishes
target: collapse-lifts-with-unique-largest-fiber-are-surjective
requires:
  - bijective-ca-preserve-uniform-bernoulli-measure
  - finite-injective-charge-noncreation-forces-surjectivity
---

Complete proof. Notation as in the target. Write `Q0 = Q_{a0}` and `q = |Q0| >= 2`. Automata act by
`Φ(y)(h) = φ((h^{-1} y)|_N)`, so `Φ(y)(h)` depends only on `y|_{hN}`. By Curtis–Hedlund–Lyndon, which holds over every
group, a continuous `G`-equivariant map between full shifts over finite alphabets is a cellular automaton, and a
bijective one has a cellular inverse. A configuration `u ∈ A^G` is *finite* if `E(u) = {g : u(g) != a0}` is finite.

## Step 0. `τ` has memory `N`

Let `x, x'` agree on `hN`. Choose lifts `y, y' ∈ B^G` with `r y = x`, `r y' = x'` and `y = y'` on `hN`. Then
`τ(x)(h) = r(Φ(y)(h)) = r(Φ(y')(h)) = τ(x')(h)`.

## Step 1. The rest map, and the first alternative

Let `τ(a0^G) = b^G` (a constant, by equivariance). `Φ` maps `r^{-1}(a0^G) = Q0^G` injectively and equivariantly into
`r^{-1}(b^G) = Q_b^G`; call this map `T_0`.

- If `b != a0`, then `|Q_b| < q`. Fix an injection `ι : Q_b -> Q0`. Then `ι ∘ T_0` is an injective automaton on
  `Q0^G` whose image avoids `Q0 \ ι(Q_b) != ∅` at every site, so it is not surjective and `q ∈ NS(G)`.
- If `b = a0` and `T_0` is not surjective, `T_0` itself shows `q ∈ NS(G)`.

From now on `τ(a0^G) = a0^G` and `T_0` is a bijective automaton on `Q0^G`. Let `S = T_0^{-1}`, an automaton with some
memory `N'`. `T_0` has memory `N`. By `bijective-ca-preserve-uniform-bernoulli-measure`, which states "Let `G` be any
group, `A` a finite alphabet, `mu` the uniform product measure on `A^G`, and `tau: A^G -> A^G` a bijective cellular
automaton. Then `tau_* mu = mu`.", we have `(T_0)_* μ = μ` for the uniform measure `μ` on `Q0^G`.

## Step 2. The fiber maps

Fix a finite `u`, and write `E = E(u)`, `E' = E(τ u)`, `F1 = E N^{-1}`. If `h ∉ F1` then `hN ∩ E = ∅`, so by Step 0
`τ(u)(h) = τ(a0^G)(h) = a0`. Hence `E' ⊆ F1` and `τ u` is finite. Identify `r^{-1}(u) = Π_g Q_{u(g)}`. Restricting `Φ`
gives an injective map `T_u : r^{-1}(u) -> r^{-1}(τ u)`.

Fix `p0 ∈ Q0`.
- For `z ∈ r^{-1}(u)` let `z̃ ∈ Q0^G` equal `z` off `E` and `p0` on `E`. For `h ∉ F1`, `z` and `z̃` agree on `hN`, so
  `T_u(z)(h) = T_0(z̃)(h)`.
- For `y ∈ r^{-1}(τ u)` let `ȳ ∈ Q0^G` equal `y` off `E'` and `p0` on `E'`.

Define `ψ(z) = ( S(ȳ), y|_{E'} )` with `y = T_u(z)`, a map into `Q0^G × Π_{g ∈ E'} Q_{τu(g)}`. It is injective:
`S` is a bijection, and `ȳ` together with `y|_{E'}` determines `y`, which determines `z`.

**Far from the defect `ψ` is the identity.** Put `F = F1 N'^{-1} ∪ E`. Let `g ∉ F`. Every `h ∈ gN'` lies outside
`F1 ⊇ E'`, so `ȳ(h) = y(h) = T_0(z̃)(h)`. Hence `S(ȳ)(g) = S(T_0 z̃)(g) = z̃(g) = z(g)`.

**The first component has a fixed pattern at `E'`.** `T_0(S(ȳ)) = ȳ`, which is `p0` on `E'`.

## Step 3. The window count

Choose a finite `V ⊇ F ∪ E' N`, and fix `c ∈ Q0^{G \ V}`. Note `E ⊆ V` and `G \ V ⊆ G \ E`.

- **Domain.** `D_c = {z ∈ r^{-1}(u) : z|_{G \ V} = c}` has `|D_c| = q^{|V| - |E|} · Π_{g ∈ E} |Q_{u(g)}|`.
- **Target.** For `z ∈ D_c`, Step 2 gives `ψ(z) = (w, e)` with `w|_{G \ V} = c`, `T_0(w)|_{E'} = p0^{E'}` and
  `e ∈ Π_{E'} Q_{τu(g)}`. Since `T_0(w)|_{E'}` depends only on `w|_{E'N} ⊆ V`, the set
  `R = {w_V ∈ Q0^V : T_0(w_V ∪ c)|_{E'} = p0^{E'}}` does not depend on `c`, and
  `|R| = q^{|V|} · μ(T_0^{-1}[p0^{E'}]) = q^{|V|} · μ([p0^{E'}]) = q^{|V| - |E'|}` by Step 1.
- **Injection.** `z ↦ (ψ(z)_1|_V, ψ(z)_2)` is injective on `D_c`, since `ψ(z)_1|_{G \ V} = c` is constant there. So

      q^{|V| - |E|} Π_{g ∈ E} |Q_{u(g)}|  <=  q^{|V| - |E'|} Π_{g ∈ E'} |Q_{τu(g)}|.

Taking logarithms, with `w(a) = log(q / |Q_a|)`, which is `0` at `a0` and strictly positive at every `a != a0`
(uniqueness of the largest fiber):

    W(τ u) = Σ_{g ∈ E'} w(τu(g))  <=  Σ_{g ∈ E} w(u(g)) = W(u).

## Step 4. Charge noncreation: `τ` is surjective

`τ` is a cellular automaton fixing `a0^G`, injective (so injective on finite configurations), and Step 3 gives
`W(τ x) <= W(x)` for every finite `x`, with `a0` the unique zero-charge symbol.
`finite-injective-charge-noncreation-forces-surjectivity` states: "Then equality holds for every finite x. Moreover,
tau is bijective on each finite-configuration charge sector, and is surjective on A^G." So `τ` is surjective and
`W(τ u) = W(u)` for all finite `u`.

## Step 5. `Φ` is surjective

With equality, the injection of Step 3 is between finite sets of the same size `q^{|V|-|E'|} Π_{E'} |Q_{τu(g)}|`,
hence onto `R × Π_{E'} Q_{τu(g)}`. Let `y' ∈ r^{-1}(τ u)`. Put `w = S(ȳ')` and `c = w|_{G \ V}`. Then
`T_0(w)|_{E'} = p0^{E'}`, so `(w|_V, y'|_{E'}) ∈ R × Π_{E'} Q_{τu(g)}`, and there is `z ∈ D_c` with
`ψ(z) = (w, y'|_{E'})`. Then `ȳ = ȳ'` and `y|_{E'} = y'|_{E'}` for `y = T_u(z)`, so `T_u(z) = y'`. Thus
`Φ(r^{-1}(u)) = r^{-1}(τ u)`.

By Step 4, `τ` is bijective on each finite charge sector, so every finite `v` is `τ u` for a finite `u`. Hence
`Φ(B^G)` contains `r^{-1}(v)` for every finite `v`. These configurations are dense in `B^G` (extend any finite
pattern by letters of `Q0` outside it). `Φ(B^G)` is compact, hence closed, so `Φ` is surjective. ∎

## Where each hypothesis is used

- *Unique largest fiber*: the charge `w` vanishes only at `a0` (Step 4), and a moved constant forces a smaller fiber
  (Step 1). With two largest fibers `a0, a1`, the sites of `a1` carry zero charge and the finite configurations
  relative to `a0` do not capture them; that case stays open.
- *Injectivity of `τ`*: only in Step 4. It is not implied by injectivity of `Φ`.
- *Group structure*: only through the two imports. The measure import uses local permutations of a free index set,
  and the charge import is proved over every group.
- *Calibration*: on the end-fixing tree the copying rule `τ(x)(v) = x(p(v))` lifts to `Q0 = B`, `A = {*}` trivially,
  and is strict. There `T_0` is not surjective, which is the first alternative, so the calibration is consistent.
