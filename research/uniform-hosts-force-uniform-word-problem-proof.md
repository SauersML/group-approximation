---
rg: 2
id: uniform-hosts-force-uniform-word-problem-proof
kind: route
title: Relator consequences enumerate triviality; a homomorphism search into the host or a normal-generation search in the envelope enumerates nontriviality
target: uniform-hosts-force-uniform-word-problem
requires: []
---

Throughout, `Z = {e : w_e = 1 in Gamma_e}` is recursively enumerable: enumerate,
uniformly in `e`, all products of conjugates of relators of `P_e` and their
inverses, freely reduce, and compare with `w_e`.  So it suffices in each case to
show that the complement of `Z` is recursively enumerable.  A set that is
r.e. and co-r.e. is decidable.

## (H)

Fix a finite generating set `Y` of `U` and a total algorithm `A` for the word
problem of `U`.  This data is fixed once and does not depend on `e`.

Semi-algorithm for `e notin Z`: enumerate all assignments `f` of a word
`f(x)` over `Y u Y^-1` to each generator `x` of `P_e`.  For each `f`, use `A` to
check that every relator of `P_e`, with `x` replaced by `f(x)`, is trivial in
`U`, and that `f(w_e)` is nontrivial in `U`.  Halt when an `f` passes both
checks.

- *Soundness.*  If `f` passes the relator check, it induces a homomorphism
  `Gamma_e -> U`.  If `w_e = 1` in `Gamma_e`, its image is `1`, so the second
  check fails.  Thus halting implies `e notin Z`.
- *Completeness.*  If `e notin Z`, choose an injective homomorphism
  `iota: Gamma_e -> U`.  It exists by hypothesis and need not be computable.
  Choose words `f(x)` representing `iota(x)`.  Both checks pass because `iota`
  is a homomorphism and `iota(w_e) != 1`.  The enumeration reaches `f`.

Each check is a finite number of calls to `A`, so the search is a
semi-algorithm uniform in `e`.

## (S)

Semi-algorithm for `e notin Z`: run the partial algorithm on `e` to obtain `Q_e`
and the words `phi_e(x)`.  This halts for every `e` by hypothesis.  Write `w'_e`
and `v'_e` for the words obtained by substituting `phi_e` into `w_e` and `v_e`.
Enumerate the consequences of the relators of `Q_e` together with `w'_e`, and
halt when `v'_e` appears.

- *Completeness.*  If `e notin Z`, then `w'_e != 1` in `S_e` by injectivity.
  The normal closure of `w'_e` is therefore a nontrivial normal subgroup of the
  simple group `S_e`, so it is all of `S_e`.  Then `v'_e` is a product of
  conjugates of `w'_e^(+-1)`, which is detected modulo the relators of `Q_e`.
- *Soundness.*  If `e in Z`, then `w'_e = 1` in `S_e`.  Adding `w'_e` to `Q_e`
  does not change the group, so `v'_e` is detected only if `v'_e = 1` in `S_e`.
  That would force `v_e = 1` in `Gamma_e` by injectivity, which is excluded.

The role of `v_e` is to rule out the trivial group `S_e = 1`, where every word
is a consequence.  In Kuznetsov's single-group argument this is the
non-triviality of the fixed simple group.  In the uniform version it must be
supplied uniformly, and a computable nontrivial word does this.
