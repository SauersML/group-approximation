---
rg: 2
id: atlas-q14-simple-overgroup-index-is-at-least-33
kind: claim
title: Every augmented finite-simple Atlas escape has A8 index at least thirty-three
distinct_from:
  atlas-q14-simple-overgroup-index-is-at-least-32: that leaves two degree-thirty-two coset profiles and three possible chart-intersection types; this excludes degree thirty-two outright by the prime-power-index classification.
  atlas-natural-a8-supports-collapse-before-collision: that excludes natural support embeddings in alternating groups by packet geometry; this excludes every finite simple ambient group of chart index thirty-two, independently of the packet labels beyond the preceding sieve.
---

Let `S` be a finite simple group and let

```text
A=i_1(A8),  B=i_2(A8),  S=<A,B>                     (OSI33-1)
```

solve the twelve packet relations, `q_19243`, and q14.  Then

```text
[S:A]=[S:B] >= 33,       |S| >= 33 |A8| = 665280.  (OSI33-2)
```

In particular, neither degree-thirty-two profile survives.  The prospective
intersection types

```text
A intersect B ~= 2^3:GL_3(2)   or   S6              (OSI33-3)
```

cannot occur in any finite simple completion, classical or otherwise.  The
same conclusion also removes the `A7` residue, though that natural-support
case already has a packet-specific exclusion.

This step uses the CFSG-dependent classification of prime-power-index
subgroups in finite nonabelian simple groups: R. M. Guralnick, *Subgroups of
prime power index in a simple group*, Journal of Algebra 81 (1983), 304--311,
Theorem 1.  It is an ambient finite-simple sieve, not a new consequence of
the Atlas packet or collision words.

The subsequent finite-simple order and maximal-subgroup classification in
`atlas-q14-simple-overgroup-index-is-at-least-91` removes the entire interval
through index ninety.
