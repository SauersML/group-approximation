---
rg: 2
id: centralizing-hnn-rf-iff-closed-proof
kind: route
title: Compute the closure through the quotients by powers of b, then separate pinches
target: centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed
requires: []
---

**(i), `A_{cl(J)}` is contained in the closure.**  Let `i in cl(J)` and let
`U <= F` have finite index with `A_J <= U`.  Some `n >= 1` has `b^n in U`
(the order of `b` modulo the core of `U`), and by closedness there is
`j in J` with `j = i + kn`.  Then `a_i = b^{-kn} a_j b^{kn} in U`.  So
`a_i` lies in every finite-index subgroup containing `A_J`, i.e. in the
closure; the closure is a subgroup, so it contains `A_{cl(J)}`.

**(i), the closure is contained in `A_{cl(J)}`.**  The normal closure `N`
of `a` is the kernel of `F -> Z`, `b |-> 1`, hence closed, so the closure
of `A_J` lies in `N`, the free group on `{a_j : j in Z}`.  Let `g in N` be a
reduced word in the `a_j` that is not in `A_{cl(J)}`; then `g` involves some
letter `a_i` with `i notin cl(J)`.  Choose `n` with `(i + nZ) n J` empty
and larger than every difference of two indices occurring in `g`.  In the
quotient `F / <<b^n>> = <a> * <b | b^n>`, the normal closure of `a` is free
on `a_0, ..., a_{n-1}` (Kurosh), with `a_j |-> a_{j mod n}`.  The image of
`A_J` is the free factor on `{a_r : r in J mod n}`, and the image of `g` is
a reduced word (the indices of `g` stay distinct modulo `n`) involving
`a_{i mod n}`, which is not in that factor.  So the image of `g` is not in
the image of `A_J`.  The group `<a> * <b | b^n>` is virtually free, hence
subgroup separable, and the image of `A_J` is finitely generated, so a
finite quotient of `F` separates `g` from `A_J`.  Hence `g` is not in the
closure.

**(ii), closed implies residually finite.**  `H_J` is an HNN extension of
`F` with both associated subgroups `A_J` and the identity isomorphism, so
Britton's lemma applies.  Let `g != 1` be Britton-reduced,
`g = f_0 s^{e_1} f_1 ... s^{e_m} f_m` with `f_i notin A_J` at every pinch
position.  Since `A_J` is closed there is a finite-index normal `N_0 <= F`
with `f_i notin A_J N_0` at those positions (and `f_0 notin N_0` if `m = 0`).
Let `psi : F -> Q = F/N_0`.  The relations `[s, A_J] = 1` map to relations
of `Q *_{psi(A_J)} (psi(A_J) x Z)`, so `psi` extends to `H_J`; the image of
`g` is Britton-reduced there, hence nontrivial, and the target is the
fundamental group of a finite graph of finite groups, hence virtually free
and residually finite.

**(ii), not closed implies not residually finite.**  If `cl(J) != J`, pick
`i in cl(J) \ J`.  By (i), `a_i` is in the closure of `A_J` but not in
`A_J`.  Then `g = [s, a_i] != 1` by Britton.  For any homomorphism `chi`
from `H_J` to a finite group, `U = {f in F : chi(f) in chi(A_J)}` has finite
index and contains `A_J`, so `a_i in U`, so `chi(a_i)` commutes with
`chi(s)`, so `chi(g) = 1`.
