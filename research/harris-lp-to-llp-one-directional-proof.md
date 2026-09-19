---
rg: 2
id: harris-lp-to-llp-one-directional-proof
kind: route
title: Separate the two quantifier scopes and check that hyperrigidity does not bridge them
target: harris-lp-to-llp-implication-is-one-directional
requires: []
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
---

Fix the definitions used throughout this graph (Enders--Shulman Definitions
2.1-2.2, source-verified in
`research/artifacts/enders-shulman-ffw-llp-sources-2026-08-21.md`):

```text
A has the LLP:  for every unital B, ideal J, and every ucp
    phi : A -> B/J, and every finite-dimensional operator system
    F subset A, the restriction phi|_F lifts to a ucp F -> B.   (Q1)

S has the LP:   for every unital B, ideal J, and every ucp
    psi : S -> B/J, psi lifts to a ucp S -> B.                  (Q2)
```

**`(H1D1)` stands.**  Harris Proposition 3.4(2) gives `LP(S_A) =>
LLP(M_(n+2)(A))`, and the LLP passes to matrix algebras and to hereditary
corners, so `LLP(A)` follows.  Nothing below touches this.

**`(H1D2)` does not follow from `(Q1)`.**  Take `S=S_A subset M_(n+2)(A)` and
suppose `A`, hence `M_(n+2)(A)`, has the LLP.  Let `psi:S->B/J` be an
arbitrary ucp map, as `(Q2)` demands.  To invoke `(Q1)` at
`F=S subset M_(n+2)(A)` one needs a ucp `phi:M_(n+2)(A)->B/J` with
`phi|_S = psi`.  No such `phi` is provided:

1. An operator system `S` inside a C-star algebra `C` carries many ucp maps
   that do not extend to `C`.  Arveson extension produces an extension into
   `B(H)`, not into the *prescribed* quotient `B/J`, and the obstruction to
   correcting an `B(H)`-valued extension back into `B/J` is exactly a lifting
   problem of the kind under discussion.  So the extension step is not a
   technicality one may assume away; it is the whole question.
2. Hyperrigidity of `S` in `C=C^*(S)` says: for every representation `pi` of
   `C`, `pi|_S` has the unique extension property, so any ucp map on `C`
   agreeing with `pi` on `S` equals `pi`.  Its hypothesis is a
   *representation* of `C` and its conclusion is uniqueness of an extension
   that is already assumed to exist.  It therefore does not manufacture an
   extension of a ucp `psi:S->B/J` to `M_(n+2)(A)`, and it says nothing at all
   when the codomain is a quotient rather than `B(H)`.  Uniqueness is not
   existence.

Hence the recorded derivation of `(H1D2)` -- "ambient LLP restricts to LP on
finite-dimensional subsystems" -- silently replaces the quantifier of `(Q2)`
(all ucp maps out of `S`) by the quantifier of `(Q1)` (restrictions of ucp maps
out of the ambient algebra).  Those are different classes of maps, and the
argument gives no reason for them to coincide.

**Consistency check on the sources.**  The direction that is available is
exactly the one Harris states, in both of its equivalent forms: Proposition
3.4(2) (`LP(S_A) => LLP` of the matrix algebra) and Corollary 3.5 (`A` fails
LLP `=>` `S_A` fails LP).  Neither is a converse of the other; they are
contrapositives.  A paper whose stated purpose is to manufacture
*counterexamples* to lifting among three-dimensional hyperrigid systems is
also not a plausible source for a theorem making LP of such systems automatic
over LLP algebras.

**What is not proved here.**  This route proves that `(H1D2)` is unsupported,
not that it is false.  Exhibiting a unital `A` with the LLP whose Harris
system fails LP would settle it; the natural candidate is the Scherer model
system `span{1,D,K} subset M_4(C^*_r(F_2))`, whose ambient algebra is widely
recorded as having the LLP, but neither the LP status of that system nor the
LLP of `C^*_r(F_2)` has been verified at source in this tree, so the candidate
is recorded and not used.
