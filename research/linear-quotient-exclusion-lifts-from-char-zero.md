---
rg: 2
id: linear-quotient-exclusion-lifts-from-char-zero
kind: claim
title: For fixed degree, a nontrivial projective representation of a finitely presented group exists in almost all characteristics or in finitely many, decided by one integral Nullstellensatz certificate
distinct_from:
  simple-vertex-groups-vtf-iff-some-finite-quotient: that says every nontrivial homomorphism of a simple-vertex triangle is vertex-injective; this turns one finite algebraic computation per degree into an exclusion theorem for infinitely many finite simple groups of Lie type at once
  convergent-quotient-count-decides-gromov-question: that shows no averaged count over all simple groups can be proved convergent without deciding Gromov's question; this is a positive tool that excludes, rigorously, every quotient of bounded projective degree
---

Let `Λ` be finitely presented, let `x in Λ`, and let `d >= 1`. For a field `k` put

```text
H_d(k) = { ρ : Λ -> PGL_d(k) homomorphism with ρ(x) != 1 }.
```

**THEOREM (established; unreviewed).**

```text
(L1) Exactly one of the following holds.
     (a) H_d(C) != ∅. Then H_d(F_p-bar) != ∅ for all but finitely many primes p.
     (b) H_d(C) = ∅. Then there is an integer N >= 1 with H_d(k) = ∅ for every field
         k whose characteristic does not divide N (characteristic 0 included).
(L2) Effectivity. H_d is the union of the solution sets of d^2 - 1 explicit polynomial
     systems S_1, ..., S_{d^2-1} with integer coefficients. In case (b) a Nullstellensatz
     certificate  N = Σ_j g_j h_j  (h_j the equations of S_i, g_j in Z[vars]) for each i
     gives N. For each of the finitely many primes p dividing N, emptiness of H_d(F_p-bar)
     is decided by a Groebner basis over F_p.
(L3) Simple-vertex triangles. Let Λ be the colimit of a triangle of finite simple groups
     with nontrivial edge groups, and x != 1 in a vertex group. Take a finite simple group
     S with a faithful projective representation of degree d over F_p-bar, or over C.
     Then S is a quotient of Λ only if H_d(F_p-bar) != ∅, respectively H_d(C) != ∅.
```

**Reading.** For each fixed degree, the primes carrying a nontrivial projective
representation form either a cofinite set or a finite, computable set. So one
characteristic-0 computation per degree `d`, plus finitely many prime computations,
settles every finite simple quotient of Λ with a projective module of dimension `<= d`,
in every characteristic. That covers all classical groups of natural dimension `<= d` and
every exceptional group whose minimal module has dimension `<= d`.

What stays out is exactly the unbounded part: alternating groups of large degree, and
classical groups of unbounded dimension. That part is what
`convergent-quotient-count-decides-gromov-question` shows to be the whole problem.

**Calibration.** Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276, Proposition 5.15 and
Remark 5.16 (read at source): `G_4^{14,14,18}` has an irreducible representation into
`U(6)` with infinite image, which is case (a) with `d = 6`. Their congruence images give
`PSp_6(p)` quotients for `p = 5, 7, 11, 13, 17, 19`. For the explicit `(A_7, A_7, A_8)`
candidates of `hyperbolic-simple-triangle-group-without-finite-quotients`, an exhaustive
`Hom(G, GL_7(C))` computation showing emptiness is case (b). With its integer `N`, it
excludes every degree-7 projective quotient outside the primes dividing `N`.

Proof: `linear-quotient-exclusion-lifts-from-char-zero-proof`. Standard Lefschetz-principle
and Nullstellensatz reasoning; no novelty is claimed.
