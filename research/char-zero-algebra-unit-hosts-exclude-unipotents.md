---
rg: 2
id: char-zero-algebra-unit-hosts-exclude-unipotents
kind: claim
title: Finitely generated simple groups of units modulo central units over characteristic-zero rings with bounded divisibility contain no unipotents
distinct_from:
  char-zero-leavitt-unit-groups-have-congruence-kernels: that shows the full unit group of L_A(1,2) over a finitely generated characteristic-zero domain is not simple; this shows that no finitely generated simple subgroup of units modulo central units, over any ring with bounded divisibility, contains a non-central scalar multiple of a unipotent, so it also excludes subgroups, scalar quotients and Q-algebra coefficients.
  positive-char-surface-linear-groups-satisfy-boone-higman: that embeds linear groups as matrices over Leavitt tensor algebras over F_p, where unipotents have order p; this shows the same matrix mechanism cannot give a simple host in characteristic zero for any input containing a non-trivial unipotent matrix.
  affine-self-similar-coordinate-rings-are-one-dimensional: that obstructs affine self-similar hosts at positive transcendence degree; this obstructs algebraic unit-group hosts in characteristic zero at every transcendence degree, including zero.
artifacts:
  - research/artifacts/bh-char-zero-transcendental-2026-09-12.md
---

**ESTABLISHED.** Let `A` be a `Q`-algebra, `C <= Z(A)^x` a group of central
units, and `G <= A^x / C` a finitely generated group. Choose lifts
`g_1, ..., g_r in A^x` of a generating set, and let `G~ <= A^x` be the group they
generate, so `G = G~ C / C`. Suppose:

- **(U)** some `u in G~` has the form `u = c (1 + nu)` with `c in Z(A)^x` and
  `nu` nilpotent and not central;
- **(D)** `A` has a subring `B` containing every `g_i^(+-1)` and `c^(+-1)`, in
  which each non-zero element lies in `pB` for only finitely many primes `p`.

Then `G` is not simple.

**Where (D) holds.**
- `B` is additively a subgroup of a free `Z[1/m]`-module. This covers every
  finitely generated subring of `A_Z ⊗ Q` when the ring `A_Z` is a free abelian
  group. Examples: `M_n(Z[t_1, ..., t_d])`, integral group rings, and tensor
  products of such rings.
- `B <= M_n(B_0)` for a finitely generated commutative domain `B_0` of
  characteristic zero. This covers `M_n(K)` for every field `K` finitely
  generated over `Q`.

**Consequence for Boone--Higman.** The positive-characteristic host places
`GL_n` of a coordinate ring inside the units of an algebra through matrix units,
and there elementary matrices are unipotent. In characteristic zero the same
mechanism fails for every input that contains a non-trivial elementary matrix,
already for `SL_3(Z)`. For example, `SL_3(Z[t])` is not a subgroup of any finitely
generated simple subgroup of `M_3(A)^x / C` when `A` has an integral form that is
free over `Z` and `SL_3(Z[t])` sits inside by matrices. So a characteristic-zero
host cannot be a unit group of this kind modulo central units.

**Scope. Not excluded:**
- embeddings that send every unipotent of the input to a unit that is not a
  scalar times a unipotent;
- `Q`-algebras in which some finitely generated subring violates (D), such as a
  finitely generated ring containing `Q`;
- groups of homeomorphisms, such as Zaremsky's Rover--Nekrashevych host for
  `GL_n(Q)`.

The argument is the classical congruence argument; no novelty is claimed. It is
recorded because it closes the whole algebraic-host family at once for
`char-zero-linear-groups-satisfy-boone-higman`.
