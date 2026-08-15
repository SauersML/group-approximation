---
rg: 2
id: fournier-facio-group-finite-dimensional-shadow-proof
kind: route
title: Simplicity plus Malcev kills the simple factor in finite dimensions
target: fournier-facio-group-finite-dimensional-shadow
requires: [fournier-facio-torsion-free-skeleton]
---

## Why sufficient

By `fournier-facio-torsion-free-skeleton`, `pi|_S` is injective, so `G`
contains a copy of `S`: infinite, finitely presented, simple, torsion-free.

**Clause 1.**  Let `rho : G -> U(n)` be a finite-dimensional unitary
representation and consider `rho|_{pi(S)}`.  Its kernel is a normal subgroup
of the simple group `pi(S)`, hence trivial or everything.  If it were
trivial, `pi(S)` would embed in `U(n) <= GL_n(C)`, making it a finitely
generated linear group in characteristic zero, hence residually finite by
Malcev.  But an infinite simple group is not residually finite: its only
proper normal subgroup is trivial, so a residually finite simple group has a
trivial finite-index normal subgroup and is therefore finite.  So the kernel
is everything: `rho` kills `pi(S)`, and being a homomorphism it kills the
normal closure.

**Clause 2.**  Residual finiteness passes to subgroups, and `pi(S)` is an
infinite simple group, hence not residually finite by the same argument.  So
`G` is not residually finite.

**Clause 3.**  If `<<pi(S)>> = G` then clause 1 says every finite-dimensional
unitary representation of `G` is trivial, which is minimal almost
periodicity.

Note what is *not* claimed: nothing here says `G` has no infinite-dimensional
representations, nor that `G` fails to be MF.  Minimal almost periodicity
concerns exact finite-dimensional representations only, and the whole point
of the non-MF program is that asymptotic finite-dimensional models are not
controlled by exact ones.
