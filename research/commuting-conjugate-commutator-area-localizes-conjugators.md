---
rg: 2
id: commuting-conjugate-commutator-area-localizes-conjugators
kind: claim
title: "Bounded area of a commutator of two conjugates of fixed words localizes the conjugators modulo the commuting pair, at word level, in any finitely presented group"
artifacts:
  - research/commuting-conjugate-commutator-localization-proof.md
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`commuting-conjugate-commutator-localization-proof`.  Group-independent; no
Property `(T)`, trace, or literature input.

## Statement

Let `Gamma = <S | R>` be finitely presented, `M = max_{r in R} |r|`, and Area
the Dehn area for this presentation.  Fix words `c, kappa` and let `delta,
epsilon` be arbitrary words, with elements `d, e`.  Put

```text
x = d c d^(-1),     y = e kappa e^(-1),     H = <x, y> <= Gamma.
```

Assume `[x, y] = 1`, that `x` and `y` have infinite order, and that `H` is
torsion-free (automatic when `Gamma` is torsion-free).  If

```text
Area( [ delta c delta^(-1), epsilon kappa epsilon^(-1) ] ) <= A        (L1)
```

then, with `R = (A M + 2|c| + 2|kappa|)/2`,

```text
d in H · e · B_R          (B_R = elements of word length <= R).    (L2)
```

**Special case (fixed conjugated element).**  If `epsilon` is empty and
`d in C(c) ∩ C(kappa)`, then `x = c`, `H = <c, kappa>`, and `(L2)` says
`d = h g` with `h in <c, kappa>`, `g in C(c) ∩ C(kappa)`, `|g| <= R`.  So the
stabilizer function

```text
f(d) = min { Area([delta c delta^(-1), kappa]) : delta a word for d }
```

on `D = C(c) ∩ C(kappa)` is proper on `D/<c,kappa>`: the set `{f <= A}` meets
at most `|B_R|` classes.  When `x, y` generate `Z^2` the constant improves to
`R = (A M + 2|c| + 2|kappa|)/4`.

**Corollary (star finiteness of conjugate templates).**  Fix words `c, h` and
let a template assign to each vertex `v` a word `u_v`, with element `t_v`.  Put
`C_v = u_v c u_v^(-1)` and `H_v = u_v h u_v^(-1)`.  Suppose every arc
`a -> b` has `[C_b, H_a] = 1` in `Gamma` and `Area([C_b, H_a]) <= A`, and that
`Gamma` is torsion-free with `c, h != 1`.  Then, for every vertex `a`,

```text
#{ element C_b : a -> b }   <=  |B_R|,
#{ element H_a : a -> b }   <=  |B_R|   (for each fixed b),
```

with `R = (A M + 2|c| + 2|h|)/2`.  More precisely,
`C_b in { t_a w c w^(-1) t_a^(-1) : |w| <= R }`.  So every conjugate template in
which one vertex sends arcs to infinitely many distinct elements `C_b`, or
receives arcs from infinitely many distinct elements `H_a`, has unbounded
area, for every choice of the words `u_v`.

## The mechanism in one line

The 1-chain of the boundary loop of `(L1)` is
`(1-x)(1-y)(P_delta - P_epsilon)` plus terms of norm at most `2|c|+2|kappa|`,
and it is the boundary of the diagram's 2-chain, of norm at most `A M`.  In the
free left `Z[H]`-module of edges, left multiplication by `(1-x)(1-y)` is
injective and never has fewer than two terms, so `P_delta - P_epsilon` lives on
at most `R` edge orbits.  Its image in the Schreier graph `H \ Cay(Gamma,S)` is
a chain of at most `R` edges whose boundary is `Hd - He`, which forces a path
of length at most `R` between them.

## What this changes

- It is a *word-level* strengthening of
  `bounded-area-commuting-conjugator-localization` (wave 18, element level:
  `Area([y,h]) <= A` forces `y in h^Z (C(h) ∩ B_K)`).  That lemma is empty when
  the conjugated element is fixed (`y = c` in the stabilizer-function
  setting).  This lemma is not empty there, because it constrains the
  conjugating word `delta` and not the conjugated element.
- It uses exactly the faithful regular permutation module `Z[Gamma]`.  The
  wave-22 class kill `thompson-template-area-sees-only-faithful-coefficients`
  shows that every linear area certificate whose coefficients are not faithful
  modulo the centre is constant on conjugate templates.  It names the
  permutation-module certificate (D1) as the remaining linear option.  This
  lemma is that certificate, and it is not constant.
- Main application:
  `lifted-thompson-t-shift-template-dies-for-all-words`.
