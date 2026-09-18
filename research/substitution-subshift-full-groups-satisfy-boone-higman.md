---
rg: 2
id: substitution-subshift-full-groups-satisfy-boone-higman
kind: claim
title: The topological full group of every primitive aperiodic substitution subshift embeds in a finitely presented simple group
distinct_from:
  boone-higman-via-v-times-aperiodic-sft-full-groups: that route puts an arbitrary input into the acting group of a subshift over the input's overgroup and needs two OPEN premises; this is an unconditional result for one explicit family, the full groups of substitution Z-subshifts.
  stationary-vershik-maps-generate-contracting-rsgs: that is the RSG verification for the Vershik map; this is the resulting embedding statement for the topological full group of the subshift.
  amenable-full-group-forces-invariant-measure: that constrains amenable full groups; nothing here is about amenability of the host, which is a twisted Brin--Thompson group.
artifacts:
  - research/artifacts/gq-bh-bh-free-03-substitution-full-groups.md
---

**ESTABLISHED** by `substitution-subshift-full-groups-satisfy-boone-higman-proof`
(lane proof, not independently reviewed). No priority is claimed; see the artifact,
§4.

**Statement.** Let `tau` be a primitive aperiodic substitution and `(X_tau, S)` its
two-sided subshift. The topological full group
`[[S]] = {h ∈ Homeo(X_tau) : h(x) = S^{n(x)} x, n : X_tau -> Z continuous}` embeds
in a finitely presented simple group, namely a twisted Brin--Thompson group `SV_G`
over a full contracting rational similarity group `G`.

**Consequences.**
- Every subgroup of `[[S]]` satisfies Boone--Higman. That includes the commutator
  subgroup `[[S]]'`, which for minimal subshifts is a finitely generated, infinite
  simple, amenable group (Matui; Juschenko--Monod). This context is cited but not read
  at source, and the proof does not use it.
- Examples: the Fibonacci subshift (`a -> ab, b -> a`), the Thue--Morse subshift
  (`a -> ab, b -> ba`). Sturmian subshifts with quadratic-irrational slope are substitutive by a standard theorem (cited, not read at source).
- The same argument covers stationary odometers. For those it recovers the known
  case of the Röver--Nekrashevych group of the adding machine.

**Scope.** Only substitution subshifts, i.e. stationary Bratteli--Vershik models by
DHS Theorem 1. For a general minimal subshift the Vershik map is not rational: its
local actions at the all-maximal cones of level `k` depend on the tail of the
diagram from level `k`. So BH for the full groups of all minimal subshifts (for
example all linearly recurrent ones, or all with decidable language) stays OPEN.
