---
rg: 2
id: large-odd-exponent-lef-burnside-groups-are-finite
kind: claim
title: For some large odd exponent, finitely generated LEF groups of that exponent are finite
distinct_from:
  large-odd-exponent-local-restricted-burnside: that is the local restricted Burnside principle, a statement about finite groups with the exponent law on short words; this is the equivalent statement about infinite LEF groups of bounded exponent
  hyperlinear-fg-bounded-exponent-groups-are-finite: that asserts finiteness for every finitely generated hyperlinear group of finite exponent, which covers the LEF ones; this asserts it only for LEF groups at one large odd exponent, the exact strength needed for a non-residually-finite hyperbolic group through the Coulon stages
  restricted-burnside-finiteness: that is Zelmanov's finiteness for residually finite groups of bounded exponent; this asks the same of the weaker LEF property
---

**OPEN.** For some `m >= 2` and some odd `N >= n_1(F_m)`, every `m`-generated LEF
group of exponent dividing `N` is finite.

By clause 1 of `local-restricted-burnside-iff-lef-burnside-groups-are-finite`
this is equivalent to `large-odd-exponent-local-restricted-burnside` at the same
`(m,N)`. Route `large-odd-exponent-lrb-via-lef-burnside-finiteness` feeds it into
`non-residually-finite-hyperbolic-group`.

## Attempts

1. **What refutes it.** By clause 4 of the equivalence, a residually finite Coulon
   stage `G_k` for infinitely many `k` makes `B(m,N)` an infinite LEF group of
   exponent `N`. So a positive answer to the residual finiteness question for
   hyperbolic groups refutes this claim at every large odd exponent.
2. **Easy kills.**
   - Residually finite groups: finite by Zelmanov
     (`restricted-burnside-finiteness`).
   - Finitely presented groups: an LEF finitely presented group is residually
     finite (the table model of a finite presentation's relators in a finite
     group is a quotient), so a finitely presented counterexample is impossible.
   - Linear, solvable or nilpotent limits: finite.
3. **Shape of a counterexample.** By
   `lef-burnside-approximants-are-nonlinear-and-nonsolvable`, its finite
   approximants are eventually non-nilpotent, of unbounded derived length, and of
   unbounded linear degree. By clause 3 of the equivalence, when the principle
   fails a counterexample can be taken to be a quotient of `B(m,N)`.
4. **Literature (2026-09-13).** TeX read on MSI; verbatim pins in
   `research/artifacts/hl-lef-burnside-literature-2026-09-13.md`.
   - Bradford (arXiv:2104.07111, l.1676): "it is not known whether infinite free
     Burnside groups are LEF". He records that either free Burnside groups of
     large odd exponent locally embed into nonabelian finite simple groups, or a
     non-residually-finite hyperbolic group exists, citing Caprace §5.4.
   - Caprace (arXiv:1709.05949, Problem `prob:limits`(ii), l.1299): "Can an
     infinite group of finite exponent be a limit of non-abelian finite simple
     groups?" His Corollary `cor:Olsh5` and the remark after it (l.1344–1348)
     say that residual finiteness of all hyperbolic groups would make Burnside
     groups such limits.
5. **Equivalence with Caprace's limit problem.** By
   `lef-burnside-groups-iff-finite-simple-limits`, infinite finitely generated
   LEF groups of exponent dividing `N` exist exactly when some infinite finitely
   generated group of exponent dividing `N` is a limit of nonabelian finite
   simple groups. Such a limit can be taken perfect, without nontrivial finite
   quotients, with simple approximants of unbounded linear degree. Route
   `large-odd-exponent-lef-burnside-via-no-simple-limits` derives this claim
   from `large-odd-exponent-no-finite-simple-limits`, the negative answer to
   Caprace's problem at one large odd exponent.
