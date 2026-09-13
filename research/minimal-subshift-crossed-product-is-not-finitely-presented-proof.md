---
rg: 2
id: minimal-subshift-crossed-product-is-not-finitely-presented-proof
kind: route
title: The periodic-model embedding makes the crossed product a simple infinite LEF ring
target: minimal-subshift-crossed-product-is-not-finitely-presented
requires: [minimal-subshift-algebra-is-simple-lef-ring, lef-simple-rings-are-not-finitely-presented]
---

1. **LEF.** Item 3 of `minimal-subshift-algebra-is-simple-lef-ring` gives an injective unital
   ring homomorphism `Psi : R -> prod_omega M_(N_k)(F_q)`, `Psi(r) = [psi_k(r)]_omega`. Fix a
   finite `F ⊆ R`. The finitely many identities `a + b = c`, `ab = c`, `-a = c` holding in `F`, the
   values at `0` and `1`, and the finitely many inequalities `a != b` in `F` hold for `psi_k` in
   an omega-large set of coordinates. Pick one such `k`. Then `psi_k` restricted to `F` is an
   injective partial homomorphism into the finite ring `M_(N_k)(F_q)`. So `R` is LEF.
2. **Simple and infinite.** `R` is simple by item 2 of the same claim, and infinite because it
   contains `LC(X, F_q)` with `X` infinite.
3. **As a ring.** By `lef-simple-rings-are-not-finitely-presented`, a finite presentation would
   make `R` finite.
4. **As an algebra.** A finite presentation of `R` as an `F_q`-algebra gives one as a ring. Add a
   generator `y` for a primitive element of `F_q`, with the relations `p = 0`, `f(y) = 0` for its
   minimal polynomial `f` over `F_p`, and `[y, x_i] = 0` for the algebra generators `x_i`. Then
   rewrite every scalar in the algebra relators as a polynomial in `y`. So step 3 applies. QED
