---
rg: 2
id: exact-x1-via-uct-free-trace-extending-af-embedding
kind: route
title: Pass to the faithful GNS trace, embed in an AF algebra extending it, and restrict its quasidiagonal trace
target: amenable-traces-on-exact-cstar-algebras-are-quasidiagonal
requires: [exact-faithful-amenable-trace-extends-to-af-embedding]
artifacts:
  - research/artifacts/stw10-x1-exact-residual-2026-09-05.md
---

Let `A` be exact and `tau` amenable.  Quasidiagonality of a trace is tested
on finite sets, so by `directed-unions-preserve-trace-approximations` we may
take `A` separable and unital.  Put `B = pi_tau(A)` and let `q : A -> B` be
the GNS quotient with induced faithful trace `tau_B`, so `tau = tau_B o q`.
Since `A` is exact, `q` is locally liftable (Effros--Haagerup), so `tau_B` is
amenable by `amenable-trace-descends-through-locally-liftable-quotient`, and
`B` is exact as a quotient of an exact algebra.

By the prerequisite there are a unital simple AF algebra `D`, an embedding
`iota : B -> D` and a trace `tau_D` on `D` with `tau_D o iota = tau_B`.

Every trace on an AF algebra is quasidiagonal: write `D` as the closure of an
increasing union of finite-dimensional unital subalgebras `D_n`, extend the
identity of `D_n` to a u.c.p. map `E_n : D -> D_n` by Arveson (`D_n` is
injective), and approximate the finite-dimensional trace `tau_D|_(D_n)` by
normalized traces of finite-dimensional representations `sigma_n` of `D_n`.
The maps `sigma_n o E_n` are u.c.p. into matrices, exactly multiplicative on
`D_m` for `m <= n`, and their traces converge to `tau_D`.

Quasidiagonality of traces passes to subalgebras (restrict the models) and
pulls back along surjections (compose the models with the surjection).  So
`tau_B = tau_D o iota` is quasidiagonal on `B`, and `tau = tau_B o q` is
quasidiagonal on `A`.  This is the argument of STW footnote 26.
