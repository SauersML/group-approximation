---
rg: 2
id: strict-automata-live-on-canonical-table-groups
kind: claim
title: A rule pair has a strict realization exactly when one canonical table group of a minimal forward partition is strict
distinct_from:
  forward-memory-lifts-exclude-strict-cellular-sections: that attaches one presentation to the product table of a given pair in a given group and proves a cover obstruction; this attaches a presentation to each minimal forward-sufficient partition of the rule pair alone and proves strictness anywhere is equivalent to strictness over one of them.
  sofic-radical-localizes-garden-of-eden-windows: that places one sofic-invisible difference inside a Garden-of-Eden window; this names the only groups a rule pair needs and shows every sofic quotient of them kills all words of some reverse hinge.
  gottschalk-surjunctivity-fixed-two-generator-tester: that reduces every group to one fixed host through marked limits; this fixes the rule pair and reduces every group to finitely many explicit table presentations.
  strict-pairs-transfer-to-table-realizations: that pushes one strict pair with its Garden-of-Eden pattern forward to every group admitting a partial homomorphism on the window tables; this pulls strictness back to the canonical table group of a minimal forward-sufficient partition, the initial realization of the rule pair, and decides it there through the reverse hinge words.
artifacts:
  - research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

A **design** is a finite alphabet `A`, finite address sets `S` and `M` with
identity addresses, and rules `nu : A^S -> A` and `mu : A^M -> A`. A realization
in a group sends addresses to elements, and identity addresses to `1`, giving an
encoder `tau` and a decoder `sigma`.

For a marked partition `E` of `S x M` (one class marked as "equals 1"), the
forward composite `nu(mu(...))` is either the identity on `E`'s classes or not.
The **forward-sufficient** partitions form an up-set `𝓕_D`, and similarly the
reverse-sufficient partitions of `M x S` form an up-set `𝓡_D`. Both are computed
from `(nu, mu)` alone.

The **table group** of `E` is

    U_E = < x_a (a in S ⊔ M, non-identity) |
            x_s x_m = x_s' x_m' for (s,m) ~_E (s',m'),  x_s x_m = 1 on the marked class >,

with at most `|S||M|` relators of length at most four.

**Theorem.** For a design `D` these are equivalent:

1. some realization in some group has `sigma tau = id` and `tau` not surjective;
2. for some minimal `E` in `𝓕_D`, the reverse table of `U_E` is not in `𝓡_D`,
   so the realization over `U_E` itself is injective and not surjective.

Hence Gottschalk's conjecture holds iff every design and every minimal
forward-sufficient partition give a table group whose reverse table is reverse
sufficient.

Every realization satisfying `E` receives a homomorphism from `U_E`, which only
coarsens the reverse table, and coarsening preserves reverse sufficiency. So no
choice of group can beat `U_E`: amalgams, extra relations, adjoined Kazhdan
subgroups and unread addresses add nothing. Any group structure a counterexample
uses must be forced by the rule pair's minimal forward sufficiency.

**Hinge form.** The realization over `U_E` is strict iff every minimal
reverse-sufficient partition has a hinge word `x_s'^-1 x_m'^-1 x_m x_s` (or `x_m x_s`)
that is nontrivial in `U_E`. Every sofic quotient of `U_E` kills all hinge words of
some minimal reverse partition.

Proof: Sections 1 to 3 of the artifact.
