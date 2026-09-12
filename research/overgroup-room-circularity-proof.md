---
rg: 2
id: overgroup-room-circularity-proof
kind: route
title: Both enlargements are equivalences, in one line each
target: overgroup-room-does-not-supply-a-root
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

**(a).**  Given faithful `rho : G -> U(H)` and `T in U(H)` with
`w(rho, T) = I`, the pair `(rho, T)` defines a homomorphism `G * <t> -> U(H)`
killing `w`, hence a homomorphism `G_w -> U(H)`; its restriction to the image
of `G` is `rho`, which is faithful, so `G -> G_w` is injective.  Conversely,
if `G -> G_w` is injective, let `lambda` be the left regular representation
of `G_w` on `l^2(G_w)`: it is faithful, so `rho = lambda|_G` is faithful, and
`T = lambda(t)` satisfies `w(rho, T) = lambda(w) = I`.

So "there is a big enough Hilbert space carrying a faithful copy of `G` and a
root" is not a sufficient condition for injectivity — it *is* injectivity.

**(b).**  Let `H` be existentially closed over `G`.  By definition `H`
realizes a finite system of equations and inequations with parameters in `G`
if and only if that system is satisfiable in some group extending `G`.  The
system `{ w(t) = 1 } ∪ { g != 1 : g in F }`, `F <= G` finite, is satisfiable
in some extension precisely when the images of the elements of `F` survive in
`G_w`.  Quantifying over all finite `F` gives injectivity of `G -> G_w`.  So
existential closure returns the hypothesis it was asked to supply.

`requires: []` is a proof commitment.  Full write-up in
`research/artifacts/kervaire-laudenbach-audit-2026-08-17.md` §H.3.
