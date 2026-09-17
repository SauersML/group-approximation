---
rg: 2
id: gottschalk-via-torus-alphabet-degree-transfer
kind: route
title: Replace finite-model counting by topological degree on torus alphabets, then transfer surjunctivity down to finite alphabets
target: gottschalk-surjunctivity-conjecture
requires:
  - every-group-is-torus-surjunctive
  - torus-surjunctivity-implies-finite-alphabet-surjunctivity
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

A decomposition into three prerequisites, each of which can fail on its own.

1. **C1, ESTABLISHED** (`torus-automata-with-regular-degree-are-surjective`). Over every
   group, a torus automaton with a regular degree matrix is onto.
2. **C2, OPEN** (`injective-torus-automata-have-regular-degree`). Injective torus automata
   have regular degree matrices.
   - *Established cases.* Residually finite groups; the circle alphabet over groups whose
     rational group ring is a domain.
   - *How it can fail.* An invariance-of-domain failure for `G`-shifts of tori. This is
     independent of finite alphabets.
3. **C3, OPEN** (`torus-surjunctivity-implies-finite-alphabet-surjunctivity`). Transfer
   from torus alphabets down to finite alphabets.
   - *How it can fail.* A torus-surjunctive group with a strict finite-alphabet automaton.
   - *Known obstructions.* Every equivariant-map mechanism dies at connectedness (no
     factor maps) or at subsystem invisibility.

C1 and C2 give `every-group-is-torus-surjunctive`, and C3 then gives the target.

**Weak link.** C3. The route's first step is fully proved and uses no sofic approximation.
The open cost is concentrated in C2 and C3.
