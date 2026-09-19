---
rg: 2
id: atlas-q14-simple-overgroup-index-is-at-least-32
kind: claim
title: The augmented finite-simple Atlas escape has A8 index at least thirty-two
distinct_from:
  atlas-q14-simple-overgroup-index-is-at-least-24: that establishes the local A4 amalgams, centralizer dichotomy, and the initial low-index sieve; this eliminates its two index-24 residues and all indices through 31.
  atlas-q14-finite-quotient-is-simple-overgroup-test: that removes finite radicals and extensions but gives no quantitative order bound; this raises the bound to 32 and identifies the first surviving permutation profiles.
---

In the notation of `(OSI1)`--`(OSI2)`, every finite-simple solution satisfies

```text
n=[S:A8] >= 32,
|S| >= 32 |A8| = 645120.                             (OSI32-1)
```

At the first remaining index `n=32`, the coset action has exactly one of the
following forms:

```text
primitive degree 32, with A8-subdegrees 1,8,8,15;    (OSI32-2)

or

imprimitive with sixteen blocks of size two,
S < A16 and [A16:S]=16216200.                        (OSI32-3)
```

In either case

```text
[A8:A intersect B] in {8,15,28}.                    (OSI32-4)
```

The three intersection types are respectively the natural point stabilizer
`A7`, an affine parabolic `2^3:GL_3(2)`, and the natural two-set stabilizer
`(S2 x S6) intersect A8 ~= S6`.

This is still a sieve, not nonexistence.  It shows that a finite escape cannot
hide in any small almost-classical completion: its first possible coset action
already has degree 32 and one of the two explicit profiles above.

The tempting global closure `S=(AB)^k` is fenced by
`atlas-augmented-relations-have-unbounded-chart-width`: the universal
completion has an infinite locally finite chart-coset graph.  Any upper bound
on `|S|` must therefore invoke a specifically finite-simple diameter theorem,
not merely rewrite the packet and collision relators.

The first natural overgroup family is completely removed by
`atlas-natural-a8-supports-collapse-before-collision`: in any
`A_n`, the packet forces two natural support `A8` copies to have the same
eight-point support, after which collision excludes their relative marking.

The entire degree-thirty-two residue, including the affine and `S6`
intersection profiles, is subsequently removed by
`atlas-q14-simple-overgroup-index-is-at-least-33` using the finite-simple
prime-power-index classification.
