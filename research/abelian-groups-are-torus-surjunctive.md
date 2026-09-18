---
rg: 2
id: abelian-groups-are-torus-surjunctive
kind: claim
title: Over every abelian group, every injective continuous equivariant self-map of every torus full shift is a homeomorphism with invertible degree matrix
distinct_from:
  every-group-is-torus-surjunctive: that is the statement for every group; this is the abelian case, including the non-residually-finite torsion hosts Q/Z and Z(2^inf) x Z(3^inf) that the graph recorded as the smallest open hosts.
  torus-degree-regular-on-prime-power-residual-support: that covers abelian groups only when the torsion subgroup is a p-group for a single p, and shows its augmentation-only method dies on every mixed-prime torsion subgroup; this covers all abelian groups.
artifacts:
  - research/artifacts/torus-normal-p-lifting-2026-09-17.md
  - experiments/torus-normal-p-lifting-2026-09-17/check_normal_p_lifting.py
---

Let `G` be a countable abelian group and `d >= 1`. Every injective continuous
`G`-equivariant `tau : (T^d)^G -> (T^d)^G` is surjective, hence a homeomorphism, and
`D(tau) in GL_d(Z[G])`.

In particular, over `Q/Z` or `Z(2^inf) x Z(3^inf)`, with `s` of order 3 and `t` of order 2,
no injective torus automaton has degree `s + s^2 - t`. Its image modulo the 2-primary
part is `s + s^2 - 1`, which takes the value `-2` at `s -> omega` and so is not a unit of
`Z[Z/3]`. This answers negatively the "Next test" recorded on
`injective-torus-automata-have-regular-degree` and the "Concrete test (need)" of the
artifact of `torus-degree-regular-on-prime-power-residual-support`.

**Belief change.** The graph recorded that torus surjunctivity "is open even on countable
abelian locally finite groups, where Gottschalk's conjecture is trivial", with smallest open
host `Z(2^inf) x Z(3^inf)` or `Q/Z`. That is false. The open hosts move to groups with no
nontrivial locally normal `p`-subgroups, e.g. the simple, locally finite, amenable,
non-residually-finite `Alt_fin(N)`.

**ESTABLISHED 2026-09-17** by [[abelian-groups-are-torus-surjunctive-proof]].
