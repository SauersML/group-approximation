---
rg: 2
id: connes-embeddable-tracial-root-extension-proof
kind: route
title: Lift the coefficients to unitary matrices, solve coordinatewise by Gerstenhaber--Rothaus, and reassemble in the ultraproduct
target: connes-embeddable-tracial-algebras-solve-nonsingular-equations
requires: [nonsingular-equations-preserve-matrix-certificates]
---

Notation.  `Q = prod_omega M_(d_n)` is the quotient of the bounded sequences
`(x_n)`, `x_n in M_(d_n)`, `sup_n ||x_n|| < infinity`, by those with
`lim_omega ||x_n||_2 = 0`, where `||x||_2 = tr_(d)(x^* x)^(1/2)` for the
normalized trace.  Its trace is `lim_omega tr_(d_n)`.  Products and adjoints
are computed coordinatewise.

1. **Unitary lifts.**  Let `u in U(Q)`.  Choose a bounded representative
   `(x_n)`.  Then `lim_omega || x_n^* x_n - 1 ||_2 = 0`.  Write
   `x_n = v_n |x_n|` with `v_n in U(d_n)`; in finite dimensions the polar
   part can be taken unitary.  For every real `lambda >= 0` one has
   `|lambda - 1| <= |lambda^2 - 1|`, because `lambda + 1 >= 1`.  By
   functional calculus on `|x_n|`,

       || x_n - v_n ||_2 = || v_n (|x_n| - 1) ||_2 = || |x_n| - 1 ||_2
                        <= || x_n^* x_n - 1 ||_2 .

   So `(v_n)` represents `u`, and every unitary of `Q` has a representative
   consisting of unitary matrices.
2. **Coordinatewise roots.**  Put `U_i = j(u_i)` and choose unitary
   representatives `(v_(i,n))_n` by step 1.  For each `n`,
   `nonsingular-equations-preserve-matrix-certificates` says the map
   `T -> w(v_(1,n), ..., v_(k,n), T)` from `U(d_n)` to itself has degree
   `m^(d_n) != 0` and is onto `U(d_n)`.  So there is `T_n in U(d_n)` with
   `w(v_(1,n), ..., v_(k,n), T_n) = I`.
3. **Reassembly.**  `T = (T_n)` is a bounded sequence of unitaries, hence a
   unitary of `Q`.  Word evaluation in `Q` is coordinatewise on
   representatives:

       w(U_1, ..., U_k, T) = ( w(v_(1,n), ..., v_(k,n), T_n) )_omega
                           = ( I )_omega = 1 .

   The embedding `j` is the given one, so `N = Q`, `iota = j`, and the root
   is `T`.

The index set, the ultrafilter and the dimensions `d_n` are whatever `j`
comes with; nothing is chosen.  In particular `N` is again
Connes-embeddable.
