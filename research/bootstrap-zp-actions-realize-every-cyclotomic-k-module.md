---
rg: 2
id: bootstrap-zp-actions-realize-every-cyclotomic-k-module
kind: claim
title: Equivariant K-theory cannot certify a UCT witness among Z_p-actions on O_2 - every cyclotomic module is realized in the bootstrap class
distinct_from:
  bootstrap-class-zp-actions-on-o2-fix-a-cartan: that proves bootstrap-class actions fix a Cartan subalgebra; this proves that the complete equivariant K-theoretic invariant of any action on O_2 is already realized by a bootstrap-class object, so it cannot detect membership in that class.
  o2-zp-crossed-products-invert-p-in-kk: that is the UCT-free cyclotomic structure of KK-rings; this is its K-theoretic shadow made complete, together with the realization of every module.
---

**ESTABLISHED (derivation from Köhler's equivariant UCT as stated by
Meyer--Nadareishvili, arXiv:2604.12529v2).**  Let `p` be prime, `G = Z/p`,
`O = Z[ζ_p, 1/p]`, and write `U(A)` for Köhler's invariant
`U^G_C(A) = M_0 ⊕ M_1 ⊕ M_2`, a Z/2-graded module over Köhler's ring `K_p`.

1. **Normal form.**  If `A` is any separable `G`-C\*-algebra with
   `K_*(Res A) = 0`, then `U(A) ≅ Q(0, 0, M)`, where `M = K_*(A ⋊ G)` with the
   dual action.  `M` is a Z/2-graded `O`-module with `ζ_p` acting as the dual
   generator, and the third component is `ΣM`.  No UCT is used.
2. **Realization.**  Every countable Z/2-graded `O`-module `M` occurs:
   `M = K_*(A ⋊ G)` for some `A` in the equivariant bootstrap class `B^G` with
   `Res A ≃_KK 0`.
3. **Comparison map.**  For every action `α : G ↷ O_2` there are `A ∈ B^G` and
   `x ∈ KK^G(A, (O_2, α))` inducing an isomorphism `U(A) ≅ U(O_2, α)`.  The
   action lies in `B^G` if and only if `x` is invertible, if and only if the
   cone of `x` is KK^G-contractible.  That cone is a `G`-algebra with
   contractible restriction and zero Köhler invariant: an equivariant phantom.

**Consequence (the fence asked for in the ex-uct brief).**  No invariant that
factors through equivariant K-theory can show that an action on `O_2` lies
outside `B^G`.  That covers K-theory of the crossed product with its dual
action, divisibility, torsion and cyclotomic ideal classes, and all of Köhler's
invariant.  Every witness in the Barlak--Li picture
(`nuclear-algebra-without-uct-exists`) must lie outside `B^G`
(`bootstrap-class-zp-actions-on-o2-fix-a-cartan`).  So a certificate must
detect a nonzero equivariant phantom, which by construction is invisible to all
K-theoretic tests.  This answers the brief's question ("an explicit `Z/p` action
on `O_2` whose crossed product has a K-theoretic signature incompatible with the
UCT") in the negative: no such signature exists.

Items 1 and 2 recover the K-theoretic part of
`order-p-automorphism-kk-cyclotomic-structure`, because `1 − ζ_p` is a unit of
`O`.  They also show that range is exactly the class of all `O`-modules.  The
normal form is Meyer--Nadareishvili's Proposition 5.1.  The specialization to
contractible restriction and the application to Problem II are this lane's.
They are routine consequences, with no priority claimed.

Proof: `bootstrap-zp-actions-realize-every-cyclotomic-k-module-proof`.
