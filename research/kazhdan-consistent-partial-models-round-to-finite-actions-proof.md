---
rg: 2
id: kazhdan-consistent-partial-models-round-to-finite-actions-proof
kind: route
title: A consistent set carries a partial action, globalize it to a G-set, project the indicator of the set onto finite orbits with property (T), and read off the finite action
target: kazhdan-consistent-partial-models-round-to-finite-actions
requires: []
---

# Proof

Notation of the target. Letters of words are `s` and `s^(-1)` for `s in S`, and the free group
`F(S)` is on the set `S`, so `s^(-1)` as an element of `S` and the formal inverse of the letter
`s` are different letters with the same value in `G`. An *`A`-path* is a path that starts and
stays in `A`. Write `[w]` for the value of `w` in `G`. Paths are determined by their start and
label.

## 0. Item 3

Let `iota : A -> Z` be as in item 3. If an edge of an `A`-path goes from `y` to `y'` with label
`s`, then `y' = sigma(s)y`, and both lie in `A`, so `iota(y') = s . iota(y)`. With label `s^(-1)`,
`y = sigma(s)y'` and `iota(y') = s^(-1) . iota(y)`. By induction, an `A`-path from `x` labelled `w`
ends at `y` with `iota(y) = [w] . iota(x)`. If `[w] = 1`, then `iota(y) = iota(x)`, and injectivity
gives `y = x`. So `A` is consistent.

## 1. The partial action

Assume `A` is consistent. For `g in G` put

```text
theta_g = {(x, y) in A x A : some A-path from x to y has a label w with [w] = g}.
```

* **Functions.** Suppose `(x,y), (x,y') in theta_g` via `A`-paths `p` labelled `w` and `p'`
  labelled `w'`. Traverse `p'` backwards from `y'` to `x`, which is an `A`-path labelled `w'^(-1)`,
  and then `p`. This is an `A`-path from `y'` to `y` labelled `w w'^(-1)`, with value `1`. By
  consistency `y = y'`. The same argument for `(x,y), (x',y) in theta_g` gives `x = x'`. So `theta_g`
  is a partial bijection of `A`.
* **Identity and inverse.** The empty path gives `theta_1 ⊇ id_A`, and consistency gives
  `theta_1 = id_A`. Reversing paths gives `theta_(g^(-1)) = theta_g^(-1)`.
* **Composition.** If `theta_h x = y` via `w_h` and `theta_g y = z` via `w_g`, the concatenated
  `A`-path from `x` to `z` has label `w_g w_h`, with value `gh`. So

  ```text
  theta_g theta_h ⊆ theta_(gh)                                          (PA1)
  ```

  as partial maps, with composition on the domain where the right-hand factor lands in the
  domain of the left.
* **Generators.** If `x in A` and `sigma(s)x in A`, the one-edge path gives

  ```text
  theta_s x = sigma(s) x         for x in A ∩ sigma(s)^(-1)A.            (PA2)
  ```

## 2. Globalization

On `G x A` put `(g,x) ~ (g',x')` iff `x in dom theta_(g'^(-1)g)` and `theta_(g'^(-1)g) x = x'`.

* Reflexive, since `theta_1 = id_A`.
* Symmetric, since `theta_(g^(-1)g') = theta_(g'^(-1)g)^(-1)`.
* Transitive. If `theta_(g'^(-1)g) x = x'` and `theta_(g''^(-1)g') x' = x''`, then by (PA1)
  `theta_(g''^(-1)g) x = x''`.

Let `Omega = (G x A)/~`, with `h . [(g,x)] = [(hg,x)]`. This is well defined because
`(hg')^(-1)(hg) = g'^(-1)g`, so `Omega` is a `G`-set. Put `iota(x) = [(1,x)]`.
* It is injective: `(1,x) ~ (1,x')` iff `theta_1 x = x'`.
* For `x in dom theta_s`, `(s,x) ~ (1, theta_s x)` by definition, so `s . iota(x) = iota(theta_s x)`.
* With (PA2):

  ```text
  s . iota(x) = iota(sigma(s)x)        for x in A ∩ sigma(s)^(-1)A.         (GL)
  ```

## 3. The Kazhdan projection

`G` acts unitarily on `l^2(Omega)`. Let `F = iota(A)` and `f = 1_F`. By (GL), if `x in A` and
`sigma(s)x in A`, then `s . iota(x) in F`. Hence `sF \ F ⊆ s . iota(A \ sigma(s)^(-1)A)`. Since
`sigma(s)` is a bijection, `|A \ sigma(s)^(-1)A| <= |[n] \ A| = eta n`, so

```text
||s f - f||^2 = |sF Δ F| = 2|sF \ F| <= 2 eta n.
```

By (KP), `dist(f, H^G)^2 <= 2 eta n / kappa^2`.

A `G`-invariant vector of `l^2(Omega)` is constant on orbits and square summable, so it vanishes
on infinite orbits. `H^G` is therefore the closed span of the orthogonal vectors `1_O` for the
finite orbits `O`. The orthogonal projection is `Pf = sum_(O finite) c_O 1_O` with
`c_O = |F ∩ O|/|O|`. Writing `a = |F ∩ O|`, a finite orbit contributes
`a(1-c_O)^2 + (|O|-a)c_O^2 = a - 2a c_O + |O| c_O^2 = a(1-c_O)` to `||f - Pf||^2`. So

```text
sum_(O infinite) |F ∩ O| + sum_(O finite) |F ∩ O| (1 - c_O) <= 2 eta n / kappa^2.     (KP2)
```

## 4. Item 1

If `G` has no nontrivial finite quotient, the action on a finite orbit `O` is a homomorphism
`G -> Sym(O)` with transitive image. The image is trivial, so `|O| = 1` and `c_O = 1` whenever
`F ∩ O != ∅`. By (KP2) the set `A_1 = {x in A : iota(x) is not a global fixed point}` has
`|A_1| <= 2 eta n/kappa^2`. If `x in A \ A_1` and `sigma(s)x in A`, then by (GL)
`iota(sigma(s)x) = s . iota(x) = iota(x)`, so `sigma(s)x = x`. So `sigma(s)x != x` only if
* `x notin A` (`eta n` points),
* `x in A_1` (`<= 2 eta n/kappa^2` points), or
* `x in A` with `sigma(s)x notin A` (`<= eta n` points).

This is (CP1).

## 5. Item 2

Let `W` be the union of the finite orbits `O` with `c_O > 1/2`. Then `W` is a finite `G`-set.

* **`|iota(A) \ W|`.** It is `sum_(O infinite) |F∩O| + sum_(O finite, c_O <= 1/2) |F∩O|`. On the
  second range `1 <= 2(1-c_O)`. So `|iota(A) \ W| <= 2 · 2 eta n/kappa^2` by (KP2).
* **`|W \ iota(A)|`.** It is `sum_(c_O > 1/2) (|O| - |F∩O|) = sum_(c_O > 1/2) |F∩O|(1-c_O)/c_O`.
  This is `<= 2 sum |F∩O|(1-c_O) <= 4 eta n/kappa^2`.

Let `A_W = iota^(-1)(W)` and `X'' = W ⊔ ([n] \ A_W)`, identifying `A_W` with `iota(A_W) ⊆ W`. So
`[n] ⊆ X''` and `|X''| = n + |W \ iota(A)| <= (1 + 4eta/kappa^2)n`. Let `rho` be the action of
`G` on `W`, extended trivially on `[n] \ A_W`. If `x in A_W` and `sigma(s)x in A`, then (GL) gives
`rho(s)x = s . iota(x) = iota(sigma(s)x)`, that is, `rho(s)x = sigma(s)x`. The exceptions in
`[n]` are
* `x notin A` (`eta n` points),
* `x in A \ A_W` (`<= 4 eta n/kappa^2` points), and
* `x in A` with `sigma(s)x notin A` (`<= eta n` points).

This is (CP2).

## 6. Consequences

(C1) and (C2) are rearrangements of (CP2) and (CP1), with the triangle inequality along the word
`w` for (C1). (C3) is item 3 followed by item 1. The Folner calibration is item 3 with `Z = G`.
