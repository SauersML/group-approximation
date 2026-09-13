---
rg: 2
id: order-p-automorphism-kk-cyclotomic-structure
kind: claim
title: An order-p automorphism whose Z_p crossed product is KK-contractible makes KK(C,C) an algebra over Z[zeta_p, 1/p]
---

**ESTABLISHED (derivation, no UCT input).**  Let `p` be a prime, `C` a separable
unital C\*-algebra and `β ∈ Aut(C)` with `β^p = id`.  Suppose the crossed product
`C ⋊_β Z_p` is KK-contractible.  Write `R = KK(C, C)` and `t = [β] ∈ R`.  Then:

1. `C ⋊_β Z` is isomorphic to the mapping torus of the dual automorphism of
   `C ⋊_β Z_p`, so it is KK-contractible.
2. `1 − t` is invertible in `R`.
3. `1 + t + ⋯ + t^(p−1) = 0` in `R`, so `x ↦ t` defines a unital ring
   homomorphism `Z[ζ_p] = Z[x]/(Φ_p) → R`.
4. `p · [id_C]` is invertible in `R`.  So the homomorphism extends to
   `Z[ζ_p, 1/p] → R`.
5. For every separable `D`, the groups `KK^*(D, C)` and `KK^*(C, D)` are uniquely
   `p`-divisible, and `1 − β` acts invertibly on them.  In particular
   `K_*(C)` and the K-homology `K^*(C)` are uniquely `p`-divisible, and
   `K_*(C)` has no nonzero `β`-invariant or `β`-coinvariant classes.

The hypothesis matters.  With `C = C*(Z_p) = C^p` and `β` the cyclic shift, the
crossed product is `M_p`, which is not contractible, and `1 − β_*` kills
`(1, …, 1) ∈ K_0(C) = Z^p`.

The main application is `o2-zp-crossed-products-invert-p-in-kk`: every
`Z_p`-action on `O_2`, not only the outer strongly approximately inner ones, has
a crossed product whose KK-ring is a `Z[ζ_p, 1/p]`-algebra.  The statement is
probably known to specialists in equivariant KK-theory in some form (it says
that `Res^G_1 = 0` forces the augmentation ideal to act invertibly).  The
sources this lane read do not state it, and no priority is claimed.  Proof:
`order-p-automorphism-kk-cyclotomic-structure-proof`.
