---
rg: 2
id: mdls-obstruction-is-affine-mechanism-plus-level-matching
kind: claim
title: The Magee-de la Salle SL_2-invariant vector exists in every representation of the affine group (Z/p^r)^3 x| SL_3(Z/p^r) that sees Z^3 primitively
distinct_from:
  sl4z-representations-have-sl2-invariant-vectors: that is the published theorem for all representations of SL_4(Z); this isolates which part of its proof holds for the affine subgroup and which input only SL_4 supplies.
  sl3z-has-no-invariant-vector-witnesses: that shows no finite family of subgroups of SL_3(Z) is a witness; this explains, inside Z^3 x| SL_3(Z), where the SL_4 witness comes from and why it fails at d = 3.
---

ESTABLISHED (unreviewed).  Let `p` be a prime, `r >= 1` and
`P_r = (Z/p^r)^3 x| SL_3(Z/p^r)`.  Suppose a representation `tau` of `P_r`
restricted to `(Z/p^r)^3` contains a character `xi` with `xi != 0 mod p`.  Then
`tau` has a nonzero vector fixed by `G_2 = SL_2(Z/p^r)` acting on coordinates
`2,3`.

**Level matching.**  An irreducible representation of a finite quotient
`(Z/M)^3 x| SL_3(Z/M)` of `Z^3 x| SL_3(Z)` is `(x)_p tau_p` over the primes
dividing `M`.  It has a `G_2`-invariant vector iff every `tau_p` does.  The
claim supplies one at every prime where `Z^3` is seen at the full level with a
primitive character.  For a representation of `SL_4(Z/M)` that is new at every
prime, Magee--de la Salle's Step 1 (normal generation of the congruence kernel
by elementary matrices) forces this at all primes.  Inside the affine group
nothing forces it.  A factor where `Z^3` is invisible, or visible below the
`SL_3` level, is an arbitrary representation of `SL_3(Z/p^b)`, and it can have
no `G_2`-invariants: Deligne's representations, and the representations used by
`sl3z-has-no-invariant-vector-witnesses`.

So the `SL_4(Z)` obstruction is this affine mechanism plus level matching.  By
`sl3z-pmf-iff-affine-kazhdan-group-pmf` the `SL_3(Z)` question lives in the
affine Kazhdan group, where level matching is absent.

Proof: `mdls-obstruction-is-affine-mechanism-plus-level-matching-proof`.
