---
rg: 2
id: jacobson-el-sofic-bilateral-lift-proof
kind: route
title: Lift partial isomorphisms of the Haar relation class-bijectively into the subrelation, restrict the sofic approximations of the bilateral relation, and apply the Laurent sofic transfer
target: jacobson-el-sofic-if-haar-relation-lifts-into-bilateral
requires:
  - bilateral-laurent-haar-relation-is-sofic
  - cordeiro-sofic-relation-permanence
  - jacobson-haar-relation-is-laurent-affine-restriction
  - jacobson-haar-character-restricts-to-orbit-relation-summand
---

Assume `(BL_N)` holds with `S`, `r`. Write `(Y, ν) = (F_2^(Z x N), μ)`. Discard an `S`-invariant null set so that
class-bijectivity holds everywhere. This is possible because the saturation of a null set under a countable p.m.p.
relation is null.

## Step 1. The lifting homomorphism `[[R_n]] -> [[S]]`

Let `φ ∈ [[R_n]]` be a Borel partial bijection `dom φ -> ran φ` with graph in `R_n`. For
`y ∈ r^(-1)(dom φ)`, let `φ̃(y)` be the unique `y' ∈ [y]_S` with `r(y') = φ(r(y))`. It exists and is unique
because `r : [y]_S -> [r(y)]_(R_n)` is a bijection and `(r(y), φ(r(y))) ∈ R_n`.

* **Borel.** `S` is a countable Borel relation, so by Lusin–Novikov it is a countable union of graphs of Borel maps
  `h_i`. Then `φ̃(y) = h_i(y)` on the Borel set where `i` is the first index with `r(h_i(y)) = φ(r(y))`.
* **Partial bijection with graph in `S`.**
  * Suppose `φ̃(y_1) = φ̃(y_2) = y'`. Then `y_1, y_2 ∈ [y']_S` and `r(y_1) = φ^(-1)(r(y')) = r(y_2)`, so `y_1 = y_2`
    by injectivity on the class.
  * The range is `r^(-1)(ran φ)`, by surjectivity on classes.
  * A Borel partial bijection whose graph lies in a p.m.p. relation preserves the measure. So `φ̃ ∈ [[S]]`.
* **Well defined on the measured semigroup.** If `φ = ψ` off a `μ_+`-null set `Z`, then `φ̃ = ψ̃` off `r^(-1)(Z)`. That
  set is `ν`-null, since `r` is measure-preserving.
* **Homomorphism.** `(φψ)~ = φ̃ ψ̃` and `(φ^(-1))~ = (φ̃)^(-1)`. Both sides are characterized by the same point of the
  same `S`-class, by uniqueness.
* **Trace.** `φ̃(y) = y` iff `φ(r(y)) = r(y)`: the point of `[y]_S` over `r(y)` is `y` itself. So
  `Fix φ̃ = r^(-1)(Fix φ)`, and `tr φ̃ = ν(r^(-1) Fix φ) = μ_+(Fix φ) = tr φ`.

So `Φ : φ -> φ̃` is a trace-preserving homomorphism of measured full semigroups, and it is injective, since
`r ∘ φ̃ = φ ∘ r` and `r` pushes `ν` to `μ_+`.

## Step 2. `R_n` is sofic

By `bilateral-laurent-haar-relation-is-sofic` part 3, `S ⊆ R'_N` is sofic in Cordeiro's Definition 2.1. Given a finite
`K ⊆ [[R_n]]` and `ε > 0`, take `π : [[S]] -> [[M]]` that is `ε`-multiplicative and `ε`-trace-matching on the finite
set `Φ(K) ∪ Φ(K)Φ(K)`. Then `π ∘ Φ` is `ε`-multiplicative on `K`, because `Φ` is exactly multiplicative. It matches
traces on `K` up to `ε`, because `Φ` preserves traces. So `R_n` satisfies Definition 2.1.

## Step 3. Consequences

* **Group soficity.** `jacobson-haar-relation-is-laurent-affine-restriction` part 1 identifies `R_n = R_E` with
  `R_Γ|_D`, off a countable invariant set. Part 3 then gives: `R_Γ|_D` sofic implies `E` sofic. Sofic groups are
  hyperlinear.
* **The algebra.** Step 1 gives a trace-preserving `*`-embedding of the algebraic full-semigroup algebra, with
  `L^∞(X_+) -> L^∞(Y)`, `f -> f∘r`, and `u_φ -> u_(φ̃)`. It extends to a normal embedding `L(R_n) -> L(S)`.
  `L(S) ⊆ L(R'_N)` trace-preservingly. `L(R'_N) = L^∞(Y) ⋊ G` for the free action (Feldman–Moore), and it embeds in
  `Π_ω M_(N_m)` by the proof of `bilateral-laurent-haar-relation-is-sofic`, Step 4. So `L(R_n)` is CE.
* **The Haar character.** By `jacobson-haar-character-restricts-to-orbit-relation-summand` part 3, `u_g ∈ L(R_n)` has
  trace `φ_1(g)`. So `φ_1` is a CE character (its part 4 chain). ∎

## Remarks

* **Class-surjective is worthless.** Step 1 uses injectivity on classes. Without it the statement would be empty.
  Every countable p.m.p. relation is a class-surjective factor of a free action of a free group, and those are sofic
  (Păunescu, Corollary 3.7). To see this, generate the relation by an action of a quotient of `F_∞` (Feldman–Moore),
  then take the diagonal action with a free Bernoulli shift of `F_∞`. That is why `(BL_N)` demands
  class-bijectivity.
* **Why fusion does not block it.** `bilateral-envelope-fuses-the-mirror-kernel-with-the-head` (F3) kills characters of
  `EL_n(J)` of the form `χ ∘ pr` that extend to `⟨P, c⟩ ≤ H_bi`. The trace used here, `φ -> μ(Fix φ̃)`, lives on the
  full semigroup of `R'_N`. There, the lift of `g ∈ E` is a piecewise element whose pieces depend on the point. On
  `H_bi` itself, this trace is the Haar character `(g, f) -> μ_+(Fix g) μ_-(Fix f)` on `P`. It is `1/2` at the head
  `(w, 1)`, and it is not a pullback along `pr : P -> E_+`.
