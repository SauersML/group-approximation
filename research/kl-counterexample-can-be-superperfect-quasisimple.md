---
rg: 2
id: kl-counterexample-can-be-superperfect-quasisimple
kind: claim
title: Any Kervaire--Laudenbach counterexample can be taken two-generator superperfect and quasisimple
distinct_from:
  kl-counterexample-can-be-two-generator-simple: that reduces a failure to a simple coefficient group, whose Schur multiplier can be nonzero; this asks for a failure over a group with trivial first and second homology, which is not simple when that multiplier is nonzero.
  kl-simple-failure-universal-cover-collapses-when-centralized: that is the established statement that the universal central extension of a simple counterexample collapses in the centralized adjunction; this asks for a failure in the plain adjunction.
  universal-schur-injectivity-for-nonsingular-adjunctions: that is the universal degree-two injectivity statement; a witness for this would kill coefficients over a group whose every Schur kernel is zero for trivial reasons.
---

**ESTABLISHED (2026-09-14)** via
`kl-superperfect-quasisimple-via-simple-acyclic-proof`. If
`kervaire-laudenbach-nonsingular-conjecture` fails, then it fails
over a two-generator group `G` with `H_1(G; Z) = H_2(G; Z) = 0` and
`G/Z(G)` nonabelian simple.

A witness would kill coefficients while its Schur kernel is zero, since the
coefficient group has `H_2 = 0`.

**Correction (2026-09-13).** 667dfcf9d first landed this node as ESTABLISHED,
via the universal central extension `S^` of a simple counterexample `S`. That
derivation is wrong at its collapse step:

* The kernel of `S^ * <t> -> S * <t>` is the normal closure of `A = Z(S^)`.
* So the image of `S^` in `(S^ * <t>)/<<w^>>` lies in the normal closure of the
  image of `A`, not in that image itself, because `t` need not commute with
  `A` there.
* Only the centralized quotient `(S^ * <t>)/<<w^, [A, t]>>` is forced to
  collapse. That is recorded in
  `kl-simple-failure-universal-cover-collapses-when-centralized`, and the
  route now targets that claim.

## Attempts

1. **Universal central extension.** Dies at the gap between the plain and the
   centralized adjunction. This is the same gap as Attempt 1 of
   `kl-implies-universal-schur-injectivity`: the extra relators `[a, t]` have
   exponent sum zero, so the conjecture predicts nothing about the system.
   Only one direction transfers: if all of `S^` dies in the plain adjunction,
   all of `S` dies at `w`.
2. **Acyclic overgroups.** Works (2026-09-14).
   * A failure passes to every overgroup of the coefficient group with the same
     equation. If `a` lies in `<<w>>_(G * <t>)` and `G <= H`, then `a` lies in
     `<<w>>_(H * <t>)`, and `a != 1` in `H`.
   * So an embedding of every countable group in an acyclic group would give a
     counterexample with `H_1 = H_2 = 0`. It would not be two-generated or
     quasisimple.
   * No such embedding theorem was pinned at source here at the time. It is now
     pinned: Palmer--Wu, arXiv:2510.16879v1, Corollary 0.10 embeds every finitely
     generated group in a 2-generated simple acyclic group. So the counterexample
     is two-generated and quasisimple after all, with trivial centre; see
     `kl-counterexample-can-be-two-generator-simple-acyclic`.

## Resolution (2026-09-14)

The simple acyclic counterexample of
`kl-counterexample-can-be-two-generator-simple-acyclic` has `H_1 = H_2 = 0`,
`Z = 1` and is nonabelian simple, so it is a witness. Attempt 1's gap is not
crossed; it is avoided, since that witness is its own universal central
extension.

DERIVATION
kl-superperfect-quasisimple-via-simple-acyclic-proof
