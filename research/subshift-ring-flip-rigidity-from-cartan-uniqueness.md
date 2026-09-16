---
rg: 2
id: subshift-ring-flip-rigidity-from-cartan-uniqueness
kind: route
title: Cartan uniqueness at every infinite minimal subshift gives ring flip rigidity, by item 4 of the groupoid-model reduction
target: subshift-crossed-product-rings-determine-flip-conjugacy
requires: [subshift-crossed-product-algebraic-cartans-are-conjugate, subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity]
---

## Why sufficient

Let `X, Y` be infinite minimal subshifts with `R_Y ≅ R_X` as rings.

1. A yes to `subshift-crossed-product-algebraic-cartans-are-conjugate` is the statement, for every infinite minimal
   subshift, that every algebraic Cartan subalgebra of its crossed product is the image of the diagonal under a ring
   automorphism. In particular it holds at `X`. This is condition (a) of item 3 of
   `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`, at `X`.
2. Item 4 of `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`: if (a) holds at `X`, then every infinite
   minimal subshift `Y` with `R_Y ≅ R_X` is flip conjugate to `X`.
3. So `(X,T)` and `(Y,S)` are flip conjugate, which is `subshift-crossed-product-rings-determine-flip-conjugacy`.

Unwinding item 4, for the reader: let `ψ: R_Y → R_X` be the isomorphism. Algebraic Cartan subalgebras are defined by
ring-theoretic conditions relative to the ambient ring: commutative and spanned by idempotents, normalisers spanning,
a faithful conditional expectation, maximal commutative. So `ψ(D_Y)` is an algebraic Cartan subalgebra of `R_X`. By
(a), `ψ(D_Y) = β(D_X)` for a ring automorphism `β`. Then `β^(−1)∘ψ: R_Y → R_X` carries `D_Y` onto `D_X`, and
`subshift-elementary-group-diagonal-iso-gives-flip-conjugacy` (through
`diagonal-preserving-isomorphisms-reconstruct-effective-groupoids`) gives flip conjugacy. This paragraph only explains
the imported item. The route relies on item 4 as established.

Combined with `subshift-el3-flip-rigidity-from-ring-rigidity`, this gives `subshift-el3-group-isomorphism-forces-flip-conjugacy`
from Cartan uniqueness and standardness alone. The target's Attempts entry "Standard form plus Cartan uniqueness"
carries the proviso that `φ(LC(X,F_2))` be an algebraic Cartan subalgebra. That proviso is automatic, because the
defining conditions transport along ring isomorphisms. The genuinely open input is Cartan uniqueness itself.
