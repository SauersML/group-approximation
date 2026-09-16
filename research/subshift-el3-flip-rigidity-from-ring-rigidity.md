---
rg: 2
id: subshift-el3-flip-rigidity-from-ring-rigidity
kind: route
title: Standardness turns a group isomorphism G_X ≅ G_Y into a ring isomorphism R_X ≅ R_Y, so ring rigidity gives group rigidity
target: subshift-el3-group-isomorphism-forces-flip-conjugacy
requires: [subshift-crossed-product-rings-determine-flip-conjugacy, subshift-el3-isomorphisms-are-standard-over-f2]
---

## Why sufficient

Let `X, Y` be infinite minimal subshifts, `R_X = LC(X,F_2) ⋊ Z`, `G_X = EL_3(R_X)`, and suppose `α: G_X → G_Y` is a
group isomorphism.

1. By `subshift-el3-isomorphisms-are-standard-over-f2`, `α = inn(k)∘M_3(φ)|_{G_X}` for some `k ∈ GL_3(R_Y)` and a
   ring isomorphism `φ: R_X → R_Y`, possibly after composing `α` with the graph automorphism `γ_X`. That claim states
   the consequence explicitly: `G_X ≅ G_Y` implies `R_X ≅ R_Y`. Composing with `γ_X`, an automorphism of `G_X`, does
   not change the conclusion, since only the existence of `φ` is used.
2. By `subshift-crossed-product-rings-determine-flip-conjugacy`, applied to the ring isomorphism `φ`, the subshifts
   `(X,T)` and `(Y,S)` are flip conjugate.

So `G_X ≅ G_Y` implies flip conjugacy. The target's converse direction (flip conjugacy gives `G_X ≅ G_Y`) is not
needed for the answer "yes".

The converse implication is `subshift-ring-flip-rigidity-from-el3-flip-rigidity`, so the two claims are equivalent.
This route replaces the recognition hypothesis in item 5 of `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`
("every isomorphism carries `GL_3(D_X)` onto `GL_3(B)` for an algebraic Cartan `B`"). Standardness makes that
hypothesis unnecessary: the group question needs only the ring question.
