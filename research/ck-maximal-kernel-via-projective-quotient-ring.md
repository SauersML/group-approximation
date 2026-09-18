---
rg: 2
id: ck-maximal-kernel-via-projective-quotient-ring
kind: route
title: Realise the maximal kernel as the congruence kernel of a finitely generated ideal of the sandwich ring with finitely presented simple projective quotient
target: ck-envelope-has-a-finitely-normally-generated-maximal-kernel
requires: [ck-maximal-kernel-four-regimes, ck-sandwich-ring-has-fp-projective-simple-quotient, ck-steinberg-marked-cover]
---

Let `Gamma ->> EL_4(U)` be the finitely presented marked cover from
[[ck-steinberg-marked-cover]]. By
[[ck-sandwich-ring-has-fp-projective-simple-quotient]], choose a finitely
generated ideal `I` of `U` such that `PE_4(U/I)` is simple and finitely
presented. Direction (2 ⇒ 1) of [[ck-maximal-kernel-four-regimes]] shows that
the kernel `M` of

    Gamma -> EL_4(U) -> E_4(U/I) -> PE_4(U/I)

is a maximal proper normal subgroup that is finitely normally generated.

## Why this route and why not only this route

The route uses only the congruence regime R4. By
[[ck-maximal-kernel-four-regimes]], R4 is the only regime in which every
finitely normally generated witness is of this form. It is also the only
regime available when the covering kernel has no nonabelian simple quotient,
the relative commutator formula holds for `U` at the level ideal, and
projective elementary groups over quotients of `U` detect roots. Under those
three standard normal-structure properties, the open prerequisite is
equivalent to the target.

A proof that avoids the prerequisite has to exhibit a maximal kernel in a
non-standard regime: a simple quotient of the covering kernel (R1), of the
congruence layer `C_I/E_4(U,I)` (R2), or a level-zero normal subgroup of
`PE_4(U/I)` (R3).
