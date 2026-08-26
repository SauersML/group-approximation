---
rg: 2
id: leavitt-regular-character-is-not-mf
kind: claim
title: The regular character of the binary Leavitt elementary group is not an MF character
distinct_from:
  binary-leavitt-steinberg-mf-characters-are-trivial: that asks that EVERY MF character of the Steinberg group be trivial; this asks only that the single character `delta_e` of the simple elementary group not be MF, and the two are equivalent for the elementary group by Diracization, simplicity, and the torsion-normal-generator criterion.
  binary-leavitt-haar-row-profile-is-not-mf-character-restriction: that excludes the Haar profile on one root module; this is the global statement that the regular character of the whole group is not a trace limit of operator-norm asymptotic representations, which is what Diracization of the simple group reduces everything to.
  degree-zero-leavitt-core-characters-are-dirac-haar-mixtures: that is the established classification showing every character is `w+(1-w)delta_e` on the core; this is the open assertion that the `w=0` endpoint of that family is not operator-norm approximable.
artifacts:
  - research/artifacts/property-t-free-provenance-delta-2026-08-26.md
---

**OPEN.**  Let `R=L_(F_2)(1,2)` and `H=EL_n(R)`, `n>=3` (equivalently
`n=12` or `n=20`; all are isomorphic).  There is no sequence of maps
`V_k:H->U(d_k)` with

```text
||V_k(gh)-V_k(g)V_k(h)||_op -> 0     and     tr_(d_k) V_k(g) -> 0   (g!=1).   (RNM1)
```

Equivalently, `delta_e` is not a pointwise limit of normalized traces of
operator-norm asymptotic unitary representations of `H`.

By `property-t-free-el20-collapse-via-regular-character` this single
statement is equivalent to the Property-`(T)`-free full MF radical of `H`,
hence to every retained manuscript endpoint.  Every character-level,
finite-subgroup-level and `K`-theoretic invariant of a corona
representation is consistent with `(RNM1)`, because `delta_e` is a genuine
character of `H` and the regular representations of the finite subgroups
realize all such invariants exactly; a proof must find an operator-norm
invariant of finite-dimensional approximants that `delta_e` violates.

## Attempts

* **Trace and character data cannot decide it.**  By
  `degree-zero-leavitt-core-characters-are-dirac-haar-mixtures` every MF
  character is `w+(1-w)delta_e` on the degree-zero core, and by
  `monomial-root-elements-are-conjugate-in-the-leavitt-group` on every
  monomial-type root of every degree; `delta_e` is the `w=0` member and is a
  character of `H`.  Spectral measures on root-module duals are then exactly
  Haar, which is invariant under every parabolic action.
* **Finite-subgroup and partial-conjugation data cannot decide it.**
  `corona-representations-are-exact-on-locally-finite-subgroups` shows
  the coordinate representations are genuine on `SL_(n*2^m)(F_2)` with exact
  compressor intertwiners, and that regular representations of the finite
  groups satisfy all such constraints.
* **Amenable sub-configurations cannot decide it.**
  `leavitt-one-compressor-defect-lies-in-amenable-subgroups`: the full
  degree-zero core, and separately the unipotent parabolic, with one
  compressor and the centralizer, are amenable and carry `delta_e`-profile
  corona representations in which the defect survives.
* **`K`-theory of the corona cannot decide it.**  `K_1` of a matrix corona
  is `0`; `K_0` is the rank-germ group, and every `K_0`-relation among group
  algebra projections is trace-consistent, hence satisfied by `delta_e`.
  Bott elements of almost-commuting pairs vanish for involutions and, when
  they vanish, only help exactification (Friis--Rordam), so they cannot
  obstruct.
* **Rank counting of commutants without a gap cannot decide it.**  In the
  `delta_e` regime the commutant dimensions `dim sigma(G_m)'` decrease by
  `(1-w)^2 d^2/|G_m|` at every level and never stabilize; the one-sided
  inclusion `U^* E_(m+1) U <= E_m` has a genuine rank deficit at every
  finite level, and the trace-ultraproduct limit exists but does not act on
  the vector-level ultraproduct.  Only a uniform gap (Property `(T)`)
  collapses the deficits.
* **What the Kazhdan proof secretly uses.**  In the `(RNM1)` regime the
  element `sigma(x_01(q)x_34(1))` is `Ad`-invariant under the compressed copy
  `tau L tau^-1` but not under `L`, so it is an almost-invariant vector of
  `Ad(V(L))` far from every invariant vector; Property `(T)` of `L` forbids
  that.  A Property-`(T)`-free proof must forbid it by a different
  mechanism: either a proper isometry in the corona built from finite data
  (no candidate survives: fixed and isotypic projections of finite subgroups
  are never properly compressed, and Pauli carriers `E`, `E_p`, `E_q` satisfy
  only `E=E_p Delta E_q`), or a finite-dimensional extension obstruction: a
  nontrivial representation `pi` of `SL_(n*2^M)(F_2)` cannot be extended by a
  unitary `A` for `x_01(s_0)` satisfying the exact Heisenberg, `S_3`, and
  Weyl relations up to `epsilon`, for `M` large.  The latter is the live
  attack; its difficulty is that `pi` may be a single irreducible, in which
  case `sigma(C[H])` is all of `M_d` and every group-algebra identity holds
  approximately.
