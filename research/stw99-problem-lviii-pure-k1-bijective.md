---
rg: 2
id: stw99-problem-lviii-pure-k1-bijective
kind: claim
title: Pure C*-algebras are K1-bijective and K-stable (STW Problem LVIII, Thiel)
root: true
artifacts:
  - research/artifacts/stw99-k1-kk-cluster-2026-08-30.md
  - research/artifacts/stw58-simple-pure-k1-bijectivity-audit-2026-08-30.md
  - notes/stw58-coefficient-unitary-stabilization-2026-09-05.md
  - notes/stw58-soft-module-compression-attempt-2026-09-05.md
  - research/artifacts/stw58-local-factorization-and-overlap-cancellation-2026-09-05.md
---

**Problem LVIII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Thiel).  Is every pure C\*-algebra `K_1`-bijective, or even
`K`-stable?  Jiang: `Z`-stable algebras are `K`-stable; STW flag the
non-nuclear case as the interesting one, where pureness does not give
`Z`-stability.

## Established simple slice

Every unital simple pure C-star-algebra is already `K_1`-bijective
(`stw58-simple-pure-k1-bijective`).  Lin's published pure dichotomy puts it
in one of two branches:

- if it has stable rank one, Rieffel's Theorem 10.12 gives the full
  isomorphism `U(A)/U_0(A) -> K_1(A)`, not merely injectivity;
- if it is purely infinite, Cuntz's nonstable K-theory gives surjectivity for
  properly infinite algebras and injectivity in the simple purely infinite
  case.

Thus neither injectivity nor surjectivity remains in the unital simple slice.

## Remaining frontier

The `K_1`-bijectivity question remains for non-simple pure algebras and for
any nonunital formulation not covered by the stated convention.  The stronger
`K`-stability question remains even for simple pure algebras.

The 2025--26 selflessness examples—reduced group algebras of limit groups and
their relatives—remain useful tests for the higher `K`-stability maps:
pureness need not give `Z`-stability in the nonnuclear setting, even though
stable rank one has already settled their scalar-unitary `K_1` map.

## Attempts

The attached coefficient-stabilization notes record a full higher-degree
result under unbounded exact K0 divisibility of the unit and a nonempty
normalized quasitrace space. Strict comparison realizes the unit roots
by projections; stable-rank-one cancellation gives exact large matrix
decompositions, and Rieffel's published bounded-divisibility theorem
applies. This is a consequence of prior art, not a solution of LVIII.

Soft divisibility instead gives a concrete Hilbert-module sandwich
X^n -> B -> X^(n+1). It supplies a large compact corner over K(X),
but its first embedding need not be adjointable. The soft-module note
proves local coefficient-dependent contraction inside sufficiently
large hereditary matrix pieces and their dimension-drop overlap.
Localization of arbitrary sphere families into those pieces remains
unproved. A finite-matrix example rules out unrestricted hereditary
homotopy excision, so an argument must use an explicit stable range.

The local-factorization artifact now proves an exact continuous
factorization on a norm neighborhood of one, using a fullness identity,
a bounded linear commutator decomposition, and a corrected exponential
chart. Separately, a globally factored sphere family contracts whenever
its total stable class vanishes: the full overlap absorbs each factor's
K-class and cancels the sum in the stable matrix range. This also works
for a global factorization approximating the family within distance two.
The outstanding step is a continuous global factorization over the
parameter sphere; local factorization does not automatically supply it.
