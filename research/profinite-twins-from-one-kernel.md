---
rg: 2
id: profinite-twins-from-one-kernel
kind: route
title: Perfect lamps collapse the visible quotient onto the skeleton
target: profinite-twins-opposite-mf
requires: [compression-wreath-five-radicals-coincide]
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

## Why sufficient

For perfect `K` the abelianization `K_ab` is trivial, so the universal visible
quotient degenerates: `P_K = G*` and the common kernel is the whole lamp base
`R_K = K^(G*/Gamma*)`, which is nontrivial.  Every clause is then a reading of
the prerequisite at `P_K = G*`.

**Finite-index lattice.**  Since `R_K = Res_fin(W_K)` is contained in every
finite-index subgroup, the quotient correspondence applies to *all*
finite-index subgroups, not only the normal ones, giving mutually inverse
inclusion-preserving bijections `L |-> L/R_K` and `M |-> q^-1(M)`.  Index is
preserved because the induced map of coset sets `W_K/L -> G*/q(L)` is a
bijection, and normality transfers both ways.  Counting at each index gives
identical subgroup growth.

**Profinite and Bohr.**  The finite-index normal subgroups correspond, with
matching quotients and transition maps, so the two inverse systems are
canonically isomorphic; the compact-target bijection identifies the Bohr
compactifications by the universal property.

**Finite actions.**  A finite action is a homomorphism to a finite symmetric
group, so `R_K` acts trivially and the action descends uniquely; a map between
two descended actions is equivariant for one group iff for the other, since
`q` is onto.  The same surjectivity argument makes the intertwiner spaces of
descended linear representations literally equal, so the representation
categories agree, not merely their object sets.

**Section.**  `q s = id`, so `s* q* = id`; as `q*` is bijective on Hom-sets by
the prerequisite, `s*` is its inverse.

**Opposite MF.**  `G*` is residually finite hence MF; `W_K` has nontrivial
`Rad_MF = R_K`, hence is not MF; soficity of `W_K` is the finite-index
telescope action plus the generalized wreath theorem.

## Priority

Groups with isomorphic profinite completions are classical and that phenomenon
is not claimed here.  What is specific is the combination: matching
finite/profinite/compact/linear data together with *opposite MF behaviour* and
an explicitly computed MF radical realizing the whole difference.
