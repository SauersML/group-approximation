---
rg: 2
id: folner-torus-truncations-have-exact-or-linearly-deficient-rank
kind: claim
title: Over an amenable group the Følner truncations of an injective torus automaton have exactly full first-cohomology rank or lose a fixed proportion of it, and full rank is equivalent to C2, so Følner instances test only C2 and never the constants of the rectangular small-fibre lemma
distinct_from:
  local-rectangular-small-fibre-maps-lose-proportional-rank: that is the group-free lemma LRSF (OPEN); this shows that the LRSF instances an amenable group produces from its own Følner sets obey a 0/1 law and are equivalent to C2 for that group, so they cannot test LRSF's constants.
  sofic-torus-c2-reduces-to-rectangular-small-fibres: that proves LRSF implies C2 on sofic groups through frozen sofic models; this proves the converse on Følner instances for amenable groups, where no freezing occurs and the rank is decided by an exact finite annihilator.
  injective-torus-automata-have-regular-degree: that is C2 for every group (OPEN); this proves that over amenable groups C2 is equivalent to right regularity of the degree, and to exact full rank of every truncation.
  exact-relation-models-give-torus-degree-regularity: that uses exact finite models of local presentations and reaches LEF; this uses truncations of the group itself, which are exact but rectangular, with no LEF hypothesis.
artifacts:
  - research/artifacts/folner-torus-truncation-rank-dichotomy-2026-09-20.md
---

**Setting.** `tau: (T^d)^G -> (T^d)^G` is injective, continuous and equivariant, with degree
`D in M_d(Z[G])` (`tau^* xi = xi D`). For finite `E <= G`, the truncation
`g_E: (T^d)^E -> (T^d)^(J(E))` extends inputs by `0` off `E` and reads a finite-memory
approximation of `tau` on `J(E) = E F^-1 ∪ E W` (artifact Section 1). It is a `(K, eta/3)`-local
rectangular map in the sense of LRSF.

**Claim.**
1. *Every group.* `rank g_E^* = d|E| - dim{ v in Q[G]^d : supp v <= E, v D^* = 0 }`. Here
   `D^*(m) = D(m^-1)^T`, so the kernel is the right annihilator of `D` inside `E`. In particular,
   if `D` is right-regular, every truncation has exactly full rank `d|E|`.
2. *Amenable groups.* Let `(E_n)` be right-Følner, so the surplus of `g_(E_n)` is `o(|E_n|)`. The
   following are equivalent:
   - C2 (`D` left-regular);
   - `D` right-regular;
   - `rank g_E^* = d|E|` for every finite `E`;
   - `rank g_(E_n)^* / (d|E_n|) -> 1`.

   If they fail, there is `c = c(tau) > 0` with `rank g_(E_n)^* <= d|E_n| - c|E_n| + o(|E_n|)`.

**Consequences for LRSF.**
- Følner instances obey a 0/1 law: exact full rank, or a fixed proportional loss at surplus
  `o(|E|)`. So they cannot test `beta(K, d, eta, delta)` or the constant of the linear form.
- The test case the LRSF node proposes, Følner maps of amenable non-LEF groups, is C2 for those
  groups. That is open when the group has torsion.
- A counterexample to amenable C2 is a counterexample to LRSF.
- LRSF's quantitative content is needed only for sofic models of non-amenable groups.
- Invariant: `dim A(E)`, the exact finite right-annihilator space of `D` in `E`. The approach
  "check LRSF on Følner instances" dies at the step where checking a host is already C2 on that
  host.

**ESTABLISHED 2026-09-20** by [[folner-torus-truncation-dichotomy-proof]]. Agent-verified only.
