---
rg: 2
id: twin-mixture-caps-deficit-ratio-of-local-amplifiers
kind: claim
title: A black-box unique-games amplifier that is component-local with graph-determined mass, or a tensor power, cannot raise the deficit ratio -- R' <= (1-s_H)/(1-c) resp. R' <= R/(1-v0) -- so no such amplifier carries any source with c <= 1/2, in particular the 2-to-2 point, across the padding line
distinct_from:
  ug-hardness-deficit-ratio-padding-line: that caps padded proper splits of d-to-d games, dying at the one-branch count; this caps reductions whose input is already a unique game, dying at the twin mixture, and covers label re-encodings (long-code or Grassmann composition), walk powering and tensor powers, which that node lists as survivors.
  black-box-repetition-needs-sqrt-scale-soundness-gap: that kills repetition amplifiers certified by a universal soundness bound, near completeness 1, at the soundness step; this kills every reduction in its class at the completeness step, whatever soundness analysis is used, and it covers graph powering with alphabet reduction, which that node lists as a survivor.
  ugc-hardness-reductions-need-epsilon-dependent-size-exponent: that is an ETH size lower bound for any UGC reduction; this is a structural cap on the achievable (c, s) pair of black-box UG-to-UG amplifiers, with no complexity assumption.
  unique-games-np-hard-below-the-padding-line: that is the open milestone R > 2; this kills one class of proofs of it and leaves it open.
  unique-games-np-hard-above-the-two-c-minus-one-line: that pushes the proved point along the padding line by mixing; this shows that mixing is also the obstruction, since the same mixtures defeat every amplifier in the class.
artifacts:
  - experiments/ugc-amplifier-mixture-2026-09-17/check_twin_mixture.py
---

**ESTABLISHED (class kill).** Elementary. Proof:
`twin-mixture-caps-deficit-ratio-of-local-amplifiers-proof`.

## Setting

A *game* `U` is a finite bipartite unique game over `[K]`. It has positive
rational edge weights and a permutation `pi_e` on each edge. Its *mass*
`||U||` is the total weight, and `val(U)` is the largest satisfied mass
fraction. Its *weighted graph* `graph(U)` is `U` with the permutations
forgotten.

* `A + B` is the disjoint union with absolute weights. `mA` is `A` with all
  weights multiplied by the rational `m > 0`.
* `A x B` is the tensor product: the alphabet is `[K_A] x [K_B]`, and edges are
  pairs of edges, with multiplied weights and product permutations.
* A *satisfiable twin* of `H` is a game `S` with `graph(S) = graph(H)` and
  `val(S) = 1`. For linear games `T x_i + T' x_j = b_e` over `F_2^l`, keep
  `T, T'` and put `b_e := 0`.

A *source class* `C` is a set of games closed under `+` and under
satisfiable twins. Examples are all games over `[K]`, and all linear games
over `F_2^l`. `Gap_C[c, s]` has YES instances `val >= c` and NO instances
`val <= s`, both in `C`. A map `Red` from `C` to unique games *amplifies*
`(c, s)` to `(c', s')`, where `s' < c' <= 1`, if it sends YES instances to
games of value `>= c'` and NO instances to games of value `<= s'`. Its
complexity is irrelevant. `nX` means `n` disjoint copies of `X`. The ratio is
`R(c, s) = (1 - s)/(1 - c)`, as in `ug-hardness-deficit-ratio-padding-line`.

**Class TS (twin-splitting).** `Red` is twin-splitting on `C` if the following
holds for every `H` in `C`, every satisfiable twin `S` of `H` in `C`, and all
integers `a, b >= 0` with `a + b >= 1`. There are games `P_S`, `P_H` and `E`,
with `E` possibly empty and `||P_S|| = ||P_H||`, such that

```text
Red(aS + bH)   is isomorphic to   a P_S + b P_H + E,
Red((a+b) H)   is isomorphic to   (a+b) P_H + E.
```

**Class GL (graph-massed component-local), the main source of members.**
`Red` is in GL if there are maps `Phi_theta` and a parameter `theta(x)`
depending only on `graph(x)` (for example only on the size), with
`Red(x) = Phi_theta(x)(x)`, such that for all `A, B` and all `theta`:

* (L1) `Phi_theta(A + B)` is isomorphic to `Phi_theta(A) + Phi_theta(B)`;
* (L2) `||Phi_theta(A)||` depends only on `theta` and `graph(A)`.

Every member of GL is in TS, with `P_S = Phi(S)`, `P_H = Phi(H)` and `E`
empty. This holds because `graph(aS + bH) = graph((a+b)H)`, so both inputs get
the same `theta`.

**Members.**

* Edge gadgets that replace each edge of weight `w_e` by a gadget of total
  weight `kappa w_e`.
* Code compositions that replace each vertex by a table and each edge by a
  test distribution of mass `w_e` on the two tables, whenever the output is a
  unique game. Examples are long-code and noise tests with folding inside one
  vertex.
* Walk powering: the edges are length-`t` walks, which stay inside a
  component.
* 2-path and star games, and graph lifts chosen from `graph(x)`.

**Closure.** TS is closed under the following operations:

* padding after, with the padding fraction a function of `graph(x)`, and
  padding before a GL map; in both cases the identity edge goes into `E`;
* adding any component that depends only on `graph(x)`;
* post-composing with a GL map that is *mass-proportional*, i.e.
  `||Phi(A)|| = kappa_theta ||A||`, and whose parameter depends only on
  `graph(x)` of the original input.

So chains of such stages are covered as one map.

## Statement

**Theorem A (twin-splitting).** Let `Red` be twin-splitting on `C` and amplify
`(c, s)` on `C`. Let `H` in `C` have `val(H) = s_H <= s`, with
`s_H < c < 1` and `c` rational. Put `lambda = (c - s_H)/(1 - s_H)`. Then

```text
R(c', s')  <=  1/(1 - lambda)  =  (1 - s_H)/(1 - c).
```

If `E` is empty, then moreover `c' <= lambda + (1 - lambda) s'`.

Consequences:

* `R(c', s') <= 1/(1 - c)` whenever `C` has any NO instance.
* `R(c', s') <= R(c, s)` whenever `C` has an instance of value exactly `s`.
  This holds if `C` has a NO instance, `s` is rational, and `C` is closed
  under padding.
* *Bounded distortion.* Replace `||P_S|| = ||P_H||` by
  `||P_S|| <= D ||P_H||` and assume `E` is empty. An example is a GL map
  whose mass may depend on labels by a factor of up to `D`. Then `R' - 1 <= D (R_H - 1)`, where
  `R_H = (1 - s_H)/(1 - c)`.

**Theorem B (tensor powers).** Let `Red(U) = U^(x t)`, for any `t >= 1`, amplify
`(c, s)` on `C`. Let `H0` in `C` have `val(H0) = v0 <= s < c < 1`. Then

```text
R(c', s')  <=  R(c, s)/(1 - v0).
```

With `H0` a NO instance of value `s`, this gives `R' <= 1/(1 - c)`.

Padding `P_mu` keeps `R` (item 1 of `ug-hardness-deficit-ratio-padding-line`).
So both bounds survive a final padding step.

**Corollary (the 2-to-2 point cannot be amplified across the line in the
class).** Take `(c, s) = ((1-eps)/2, eps)` on linear games over `F_2^l`, the
source of `unique-games-hard-at-completeness-one-half`, or any source with
`c < 1/2`. Apply one member of TS, or one tensor power followed by an optional
padding. Then the result satisfies

```text
R(c', s') <= 1/(1 - c) = 2/(1 + eps) < 2,
```

so it lies strictly above the padding line `s' = 2c' - 1`. At `c = 1/2` the
bound is `R' <= 2`, i.e. on or above the line.

The same holds for any chain of gadget, powering, code-composition and
padding stages that is twin-splitting as one map (see Closure). An amplifier
across the line must therefore leave TS, and not only one stage of it.

## The invariant and where every member dies

The invariant is **mass faithfulness on twins**. Mix a satisfiable twin `S`
with a NO instance `H` at mass fraction `lambda = (c - s_H)/(1 - s_H)`. The
mixture `M = aS + bH` is a YES instance of value exactly `c`. A member of TS
must give the `H` part of `M` the same share `1 - lambda` of the non-`E`
output mass. On that share it does no better than on the NO instance
`(a+b)H`.

Every member dies at the **completeness case on `M`**. When `E` is empty:

```text
c' <= val Red(M) <= lambda + (1 - lambda) s'.
```

The ratio `1/(1 - lambda) = (1 - s_H)/(1 - c)` is the whole budget. `M` has
the value of the padding `P_lambda(H)` and is built the same way, with a
satisfiable block of mass fraction `lambda` next to `H`. So an amplifier in
the class treats the YES instance `M` like a padding of a NO instance. A
padding of `H` has ratio `(1 - s_H)/(1 - c)`.

For tensor powers the `S x ... x S` block gets mass `lambda^t`. Every other
block contains an `H0` factor and has value at most `v0`. The factor
`(1 - x^t)/(1 - y^t) <= (1 - x)/(1 - y)` for `x < y` then keeps the ratio.

## What survives

* **Non-black-box use of the source.** This covers reductions correct only on
  the image of a specific NP-hardness reduction, such as the KMS instances
  built from 3LIN. For those it matters whether the image is closed under
  twin mixtures. The KMS image is not visibly closed, because every k-tuple
  mixes the variables of both parts.
* **Cross-component maps.** Examples are expanderization, global
  sparsification and random re-pairing across components. Note that
  expanderization by equality edges is itself a padding-like mixture and
  lowers `R`.
* **Label-sensitive mass (large `D`).** The distortion bound then gives only
  `R' <= 1 + D(R_H - 1)`.
* **Randomized members.** This means maps whose coins are not shared across
  components, and whose guarantees hold only with high probability. The proof
  uses one deterministic output.
* **Products followed by a non-trivial gadget.** Here the gadget sees mixed
  blocks `S x H0`, whose value is not controlled by the reduction's
  guarantee. This mixed class `Phi(U^(x t))` is not covered.
* **Direct reductions from 3LIN or label cover**, such as the KMS proof itself.
  `ug-hardness-deficit-ratio-padding-line` item 5 covers only their
  padded-proper-split outputs.

This neither proves nor refutes `unique-games-np-hard-below-the-padding-line`
or `unique-games-conjecture`.

## Attempts

* **Artifact** `check_twin_mixture.py`, seed 20260918, exact rational brute
  force. It runs 25 random games over `Z_2` and `Z_3` with their twins and
  mixtures, under the 2-path map. It checks the union formula, the
  decomposition `val Phi(M) = lambda val Phi(S) + (1 - lambda) val Phi(H)`,
  the completeness inequality and the ratio bound. The maximum of `R'` divided
  by the bound is exactly `1`, so the bound is attained whenever `Phi(S)` is
  satisfiable. It also checks, on random pieces, that tensor values lie in
  `[product, min]`, and the block decomposition of `(S + H0)^(x 2)`. It
  checks the Theorem B bound for `t <= 6` and the scalar inequality on 2000
  rationals. The KMS caps come out as `1.818`, `1.980` and `1.998` for
  `eps = 1/10`, `1/100` and `1/1000`.
