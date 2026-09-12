---
rg: 2
id: finite-group-formalizability-equals-equivariant-automorphism
kind: claim
title: On a finite group a binary left-inverse pair is formalizable exactly when it is the shadow of an equivariant polynomial automorphism
distinct_from:
  formalizable-pairs-induce-polynomial-automorphisms-on-constants: that specializes every site variable diagonally and sees only the constant-configuration map; this characterizes formalizability over a whole finite group as equivariant automorphism extension of all of affine space.
  structurally-reversible-automata-are-formalizable: that proves words of track shears are formalizable on every group; this characterizes all formalizable pairs on finite groups, whether or not they are words of shears.
artifacts:
  - research/artifacts/formalizability-finite-levels-and-z3-rigidity-2026-09-12.md
---

Let `G` be finite and `(tau, sigma)` a pair on `(F_2^n)^G` with `sigma o tau = id`. The pair is
formalizable iff `tau` is the Boolean shadow of a `G`-equivariant polynomial automorphism of
`A^(n|G|)` over `F_2`. The inverse automorphism then has shadow `sigma = tau^-1`.

**Stable form.** The same holds for `tau x id` on `n + m` tracks. So on finite groups, stable
formalizability is equivariant automorphism extension of `tau x id`.

*Why.*
- **Forward.** A formal identity `S o T = id` on finitely many variables makes `T` injective over
  `F̄_2`. Ax–Grothendieck makes it bijective, so `T o S = id` on an infinite field and hence formally.
- **Backward.** An equivariant automorphism is the automaton with memory `G` whose rule is its
  coordinate at `1`.

Artifact, Section 1, Theorem 1.
