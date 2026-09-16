---
rg: 2
id: prime-quotient-minimal-k1-trivial-unitaries-are-null
kind: claim
title: In a prime properly infinite algebra, a K1-trivial unitary that is null modulo every nonzero ideal is null
distinct_from:
  stw99-problem-lxi-properly-infinite-k1-injective: the root asks this for every unitary of every properly infinite algebra; this is the special case of prime algebras and unitaries that die in every proper quotient, which with the loop-detection claim is equivalent to the root.
artifacts:
  - research/artifacts/lxi-quotient-minimal-counterexamples-2026-09-16.md
---

Let `B` be a unital properly infinite C\*-algebra that is prime: any two nonzero closed two-sided ideals
of `B` have nonzero intersection. Let `v ∈ U(B)` satisfy `[v] = 0` in `K_1(B)`, and suppose
`q_J(v) ∈ U_0(B/J)` for every nonzero closed two-sided ideal `J`. Then `v ∈ U_0(B)`.

In other words, there is no prime quotient-minimal witness, in the terminology of
`nonprime-minimal-lxi-counterexample-yields-loop-witness`. By route
`stw99-lxi-from-prime-case-and-loop-detection`, this claim together with
`properly-infinite-unitary-loops-detected-by-k1-suspension` gives STW Problem LXI. For that purpose,
separable `B` would be enough. BRR Theorem 5.5, (i) <=> (vi), reduces LXI to the separable algebra
`O_∞ * O_∞`, and quotients of separable algebras are separable.

## Attempts

- **Simple case.** For simple `B` the hypothesis on quotients is vacuous, so this claim contains
  K1-injectivity of every simple unital properly infinite algebra. That is known for purely infinite simple
  `B` (Cuntz 1981; Rohde's thesis, Theorem 3.1.3) and for Z-stable `B`
  (`z-stable-unital-algebras-are-k1-bijective`). Simple unital properly infinite algebras need not be purely
  infinite. M. Rordam (Acta Math. 191 (2003), arXiv:math/0204339v2, Corollary 7.1, read 2026-09-16)
  gives a corner `A = p(D ⋊ Z)p` that is nuclear, unital, separable, simple and infinite, hence properly
  infinite, but not purely infinite because it contains a nonzero finite projection. No source settling the general simple properly
  infinite case was found.
- **Structure of a hypothetical counterexample** (artifact, Proposition 2). For every nonzero ideal `J`,
  `v` is homotopic in `U(B)` to some `v_J ∈ U(J~)` with `[v_J]_{K_1(J)} = 0`. Primeness keeps finite
  intersections of nonzero ideals nonzero, so `v` can be pushed into all of them. No nonzero ideal is
  stable, and no nonzero ideal has a stable rank one unitization. If `B` is separable, no nonzero ideal
  is purely infinite simple. A separable purely infinite simple algebra is unital or stable. This dichotomy
  is used without proof in Rohde's thesis, proof of Proposition 5.2.9, and is usually attributed to Zhang;
  it was not rechecked here. A unital ideal is cut out by a central projection, so it would force `B` itself
  to be purely infinite simple, and Cuntz's theorem excludes that.
- **Where the non-prime argument dies.** Theorem 3 of the artifact glues paths from `B/J_1` and `B/J_2`
  through the pullback `B ≅ B/J_1 ×_{B/(J_1+J_2)} B/J_2`. That needs `J_1 ∩ J_2 = 0`. In a prime algebra
  the same gluing only produces a path in `B/(J_1 ∩ J_2)`, which quotient-minimality already provides.
  Primeness constrains the ideal lattice but gives no handle on path components of `U(B)`.
- **Universal candidate.** If LXI fails, Blanchard's unitary in `T_2 *_C T_2` (arXiv:0804.4624v13,
  Remarks 4.7(i)) is a witness, and Proposition 1 of the artifact gives a quotient-minimal quotient `B`.
  Whether that `B` (or `O_∞ * O_∞`) is prime was not determined. Under the halving hypothesis
  (`trivial-unit-class-lxi-iff-universal-halving-homotopy`), the two Toeplitz defect ideals of `B` intersect
  nontrivially (artifact, Remark 5.2).
