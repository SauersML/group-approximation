---
rg: 2
id: padded-abstract-rn-perfect-decidable-witness-via-structure
kind: route
title: Pad the repaired hard recursion, compute finite abelianization, and apply the explicit abstract RN structural theorem
target: padded-abstract-rn-perfect-decidable-nonrecursive-kernel
requires:
  - bartholdi-mitrofanov-proposition-2-4-gap-and-repair
  - abstract-rover-nekrashevych-groups-are-finitely-presented
  - padded-abstract-rn-local-derived-normal-subgroup-theorem
artifacts:
  - research/artifacts/padded-abstract-rn-manuscript-integration-2026-09-20.md
---

This is a **conditional implication**, not a claim that the newly supplied
manuscript has already been proved or refereed. The third prerequisite is
unresolved. Sections 4–10 of the artifact supply the detailed argument for
the implication; the structural prerequisite is used at Sections 7 and 9.

The repaired Bartholdi–Mitrofanov input provides a finite free recursion
with nonrecursive, co-c.e. tree kernel `N`. Add `k` fixed state-preserving
letters with `D=d+k` even and `k−1>||A||₁`. The padded recursion is injective
and has the same tree kernel. The abstract presentation gives a finitely
presented `P` with decidable word problem, and abelianizing it gives
`P_ab=ℤ^r/((k−1)I+A)ℤ^r`. The strict norm inequality makes this quotient
finite, so `E=P′` is finite-index, finitely presented and decidable.

The structural prerequisite now gives direct relative simplicity for
`M=E∩ker(boundary action)`, perfectness, and the type `[A₂]` clopen action.
It also identifies the unique simple quotient and its faithful prefix core.

For disjoint first-letter cones, the computable word map
`f↦[ι₁(f),v]∈E` belongs to `M` exactly when `f∈N`; finite-index rewriting
makes it an effective map to a fixed finite generating set of `E`. The
converse oracle reduction is the finite table-label test. Therefore
`M≡_T N` and `M` is co-c.e. but not c.e. A recursive presentation of `E/M`
would enumerate `M`, which is impossible. Relative simplicity shows that
every nontrivial simple quotient is this quotient. Finite normal generation
of `M` would give a finite presentation of `E/M`, also impossible.

Finally an exact pair embedding into `(H,L)` with `H` finitely presented
and `L` finitely normally generated injects `E/M` into the finitely
presented `H/L`. Enumerating ambient identity words for its finite generating
tuple again enumerates `M`, a contradiction. This proves the full target
once the listed prerequisites hold, without invoking an abstract twisted
Brin–Thompson finite-presentation result.
