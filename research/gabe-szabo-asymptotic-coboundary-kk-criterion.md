---
rg: 2
id: gabe-szabo-asymptotic-coboundary-kk-criterion
kind: claim
title: On a unital Kirchberg algebra with an amenable isometrically shift-absorbing action of an exact group, a cocycle is an asymptotic coboundary iff its unit class equals the trivial one in KK^G(C, B)
distinct_from:
  gabe-szabo-unital-uniqueness-theorem: that imports Theorem 5.8, uniqueness of unital cocycle embeddings up to asymptotic unitary equivalence; this imports Theorem 5.14, its specialization to A = C, which decides when a single cocycle is an asymptotic coboundary.
---

**ESTABLISHED (literature).**  J. Gabe and G. Szabó, *The dynamical
Kirchberg–Phillips theorem*, arXiv:2205.04933v3, Section 5.3.

Let `β : G ↷ B` be an amenable, isometrically shift-absorbing action on a
Kirchberg algebra, and `u : G → U(1 + B)` a `β`-cocycle.

1. **Definition 5.9.**  `u` is an *asymptotic coboundary* if there is a
   continuous unitary path `v_t` with
   `lim_(t→∞) max_(g∈K) ‖u_g − v_t β_g(v_t)^*‖ = 0` for every compact `K ⊆ G`.
2. **Theorem 5.14(i).**  If `β` is strongly stable and `(u, 1) ∼_h (1, 1)`
   (Definition 1.9), then `u` is an asymptotic coboundary, witnessed by a path
   `y_t` with `y_0 = 1`.
3. **Theorem 5.14(ii).**  If `G` is exact and `B` is unital, put
   `u^♯ := KK^G(ι_B, u) ∈ KK^G(id_C, β)`, where `ι_B : C → B` is the unital
   inclusion (Notation 5.13).  Then `u` is an asymptotic coboundary iff
   `u^♯ = KK^G(ι_B, 1)`.
4. **Corollary 5.11.**  If `G` is compact, every asymptotic coboundary is a
   coboundary: `u_g = v β_g(v)^*` for one unitary `v`.

With Proposition 3.15 of `gabe-szabo-unital-uniqueness-theorem`, item 3
applies to every pointwise outer action of a finite group on a unital
Kirchberg algebra.  With item 4, such a cocycle is an honest coboundary iff
`u^♯ = KK^G(ι_B)`.

**Authors' comment (Remark 6.5).**  "In some very special cases, such as when
β has the Rokhlin property, it may happen that all cocycles are coboundaries,
but in general this provides plenty of examples demonstrating that conjugacy
between actions on unital Kirchberg algebras is indeed stronger than cocycle
conjugacy."

Proof: `gabe-szabo-asymptotic-coboundary-kk-criterion-citation`.
