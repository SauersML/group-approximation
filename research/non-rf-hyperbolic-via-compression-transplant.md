---
rg: 2
id: non-rf-hyperbolic-via-compression-transplant
kind: route
title: Transplant the finite-residual compression witness into a hyperbolic ambient group
target: non-residually-finite-hyperbolic-group
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

The obvious first attack, and the one this repository is best equipped to
run.  This program already owns a machine that manufactures elements of the
finite residual: a subgroup `Γ`, a strict compression `tΓt^(-1) ⊊ Γ`, a
centralizing element `c`, and a commutator word in `d = tct^(-1)` and elements
of `Γ`.  Every finite quotient turns the compression into an equality, so the
image of `d` centralizes the image of `Γ` and the word dies; a Clifford model
proves it does not die in the group.  That is precisely a nontrivial element
of the finite residual (`commuting-lamp-quotient-finite-residual`,
`literal-mark-quotient-finite-residual`).

So: run the same construction with a hyperbolic ambient group.

Dead: by `hyperbolic-compression-centralizer-rigidity`, in a hyperbolic `G`
with `Γ` non-elementary the compressor already normalizes `C_G(Γ)`, so
`d ∈ C_G(Γ)` and the witness word is trivial **in `G`**.  The mechanism does
not merely fail to certify a hyperbolic example; it degenerates, because what
the finite quotients were supposed to add is already true upstairs.  And
non-elementarity is not a restriction one can negotiate away: the architecture
needs `Γ` infinite with property (T), which forces it.

**What survives the demolition.**  Everything the machine does outside the
hyperbolic category, which is where this program uses it — the wreath-type
ambient groups contain `ℤ^2` and were never hyperbolic.  What dies is the hope
that the finite-residual witness is portable, and with it the idea that this
repository has a head start on the hyperbolic question.
