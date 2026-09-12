---
rg: 2
id: o2-zp-cartan-fixing-all-primes-or-at-most-one-proof
kind: route
title: Pass each prime half through Barlak--Li II Theorem 4.16 and glue two primes with the coprime UHF splitting
target: o2-zp-cartan-fixing-all-primes-or-at-most-one
requires: [barlak-li-p-half-iff-zp-actions-fix-cartan, coprime-uhf-stabilizations-detect-uct, torsion-kk-identity-dies-after-uhf-absorption]
artifacts:
  - research/artifacts/stw-uct-per-prime-cartan-2026-09-12.md
---

Write `H_p` for statement 1 of part (b) of
`barlak-li-p-half-iff-zp-actions-fix-cartan`: every separable nuclear `A` that is
KK-equivalent to `A ⊗ M_(p^∞)` satisfies the UCT.  That node gives `H_p ⟺ D_p` for
every prime `p`.

**Item 1, forward.**  Assume `D_p` and `D_q` with `p ≠ q`, so `H_p` and `H_q` hold.
Let `A` be separable and nuclear.  Since `M_(p^∞) ⊗ M_(p^∞) ≅ M_(p^∞)`, the algebra
`B = A ⊗ M_(p^∞)` is separable, nuclear and isomorphic to `B ⊗ M_(p^∞)`, so `H_p`
gives the UCT for `B`.  Likewise `A ⊗ M_(q^∞)` satisfies the UCT.  The supernatural
numbers `p^∞` and `q^∞` are coprime and different from `1`, so (CU1) of
`coprime-uhf-stabilizations-detect-uct` gives the UCT for `A`.

**Item 1, backward.**  If every separable nuclear algebra satisfies the UCT, then
`H_r` holds at every prime `r`, hence `D_r` does.

**Item 2.**  If `D_p` holds at two distinct primes, item 1 gives the UCT for all
separable nuclear algebras, and the backward direction gives `D_r` at every prime.

**Item 3.**  By `torsion-kk-identity-dies-after-uhf-absorption`, `A ⊗ M_(r^∞)` fails
the UCT at every prime `r ≠ p`.  It is separable, nuclear and isomorphic to its own
`M_(r^∞)`-stabilization, so `H_r` fails, hence `D_r` fails.
