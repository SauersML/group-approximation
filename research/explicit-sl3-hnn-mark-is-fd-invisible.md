---
rg: 2
id: explicit-sl3-hnn-mark-is-fd-invisible
kind: claim
title: A displayed finitely presented SL_3(Z) HNN group has a concrete nontrivial word killed by every finite-dimensional unitary representation
distinct_from:
  affine-leavitt-steinberg-mark-is-fd-invisible: that uses a properly infinite coefficient idempotent and Steinberg root groups; this is a two-relator arithmetic HNN extension whose exact collapse follows from profinite co-density.
  explicit-sl3-thin-codense-tau-pair: that establishes the subgroup data; this records the unconditional group-theoretic consequence for the HNN extension.
---

Let `a,b,r in SL_3(Z)` be the displayed matrices of
`explicit-sl3-thin-codense-tau-pair` and put

```text
G_exp = < SL_3(Z), t | [t,a]=1, [t,b]=1 >,
w_exp = [t,r].                                          (EFI1)
```

Then:

1. `G_exp` is finitely presented;
2. `w_exp != 1` in `G_exp`;
3. every finite-dimensional unitary representation `sigma` of `G_exp`
   satisfies `sigma(w_exp)=1`;
4. in particular every finite quotient kills `w_exp`, so `G_exp` is neither
   maximally almost periodic nor residually finite.

Finite presentability follows from a standard finite presentation of
`SL_3(Z)` plus the two HNN relators.  Since `C=<a,b>` is free and `r` has
order three, `r notin C`; Britton's lemma gives item 2.

For item 3, restrict `sigma` to `rho:SL_3(Z)->U(d)`.  Every such `rho` has
finite image and factors through a congruence quotient.  Profinite density of
`C` gives `rho(C)=rho(SL_3(Z))`.  The HNN relators say that `sigma(t)`
commutes with `rho(C)`, hence it commutes with `rho(r)`, and therefore
`sigma([t,r])=1`.

This exact theorem is unconditional.  The remaining hyperlinearity problem
for `G_exp` is precisely whether the same collapse is robust under
normalized-Hilbert--Schmidt approximate representations.

