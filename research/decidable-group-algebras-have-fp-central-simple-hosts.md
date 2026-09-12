---
rg: 2
id: decidable-group-algebras-have-fp-central-simple-hosts
kind: claim
title: Every decidable group algebra over F_2 embeds in a finitely presented central simple algebra with K-theoretically trivial Leavitt tensor
distinct_from:
  decidable-group-ring-has-fp-projective-simple-host: that asks for a ring host whose projective elementary group is finitely presented and simple, which still requires finitely normally generating an unstable Steinberg kernel; this asks only for a finitely presented central simple algebra B with K_1 and K_2 of B ⊗ L zero, because tensoring with L makes that kernel trivial.
  boone-higman-conjecture: that is the group embedding conjecture; this is an algebra embedding statement which implies it through the Leavitt tensor host theorem, with no known converse.
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem. Then
there is a finitely presented central simple unital `F_2`-algebra `B` with:
- a unital embedding `F_2[G] -> B`;
- `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`, where `L = L_(F_2)(1,2)`.

By Ara--Cortiñas Proposition 6.2, the `K`-theory condition holds whenever `B`
is regular supercoherent.

## Why it is a certificate

By `leavitt-tensor-hosts-acyclic-steinberg-and-fp` and
`central-simple-leavitt-tensor-unit-groups-are-simple`, `(B ⊗ L)^x` is
finitely presented and simple. It contains `G <= F_2[G]^x <= B^x`. This is the
route `boone-higman-via-central-simple-leavitt-tensor-host`.

## Attempts

1. **Evans--Mandelberg--Neff (1975).** Their Boone--Higman type theorems for
   algebras give the weak half: a simple algebra that embeds in a finitely
   presented algebra.
   *Does not reach*: finite presentation of the simple host is exactly the
   missing half, the algebra counterpart of the group wall.
2. **Fixed Leavitt-type hosts.** `B = L^(⊗d)` or a Leavitt path algebra.
   *Dies*: one finitely presented algebra has one word-problem bound. Its unit
   group is a finitely presented simple group, so
   `complexity-bounded-host-classes-are-not-universal` forbids universality.
   A universal family needs hosts with unbounded complexity.
3. **Maximal-ideal quotient.** Embed `F_2[G]` in a finitely presented algebra
   `P` missing every proper ideal, and pass to `P/M` for a maximal ideal `M`.
   *Dies* at the same point as `fp-quotient-iff-kernel-finitely-normally-generated`:
   `M` need not be finitely generated as an ideal. The requirement that `B`
   be central simple, not just simple, is inessential: a finite centre only
   changes `(B ⊗ L)^x` by a finite central quotient.
4. **Complexity test.** A proof must produce algebras `B` with arbitrarily hard
   decidable word problems. Nothing in the statement conflicts with that,
   unlike fixed hosts.
