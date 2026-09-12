---
rg: 2
id: asymptotic-quantum-birkhoff-false
kind: claim
title: The asymptotic quantum Birkhoff conjecture is refuted
invalidates: [sofic-model-via-quantum-birkhoff-channel-rounding]
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

Haagerup–Musat, *Factorization and dilation problems for completely positive
maps on von Neumann algebras* (arXiv:1009.0778, CMP 2011), solve in the
negative the asymptotic quantum Birkhoff conjecture: there are unital
trace-preserving (bistochastic) channels `T` on a matrix algebra such that
`T^{⊗n}` stays a fixed positive distance — uniformly in `n`, in the relevant
normalized distance — from the convex hull of channels of the form
`X ↦ U X U^*` (mixed-unitary channels).  Tensoring does not classicalize a
bistochastic channel.

**Why this graph carries it.**  It is the boundary condition on every
"replicate and classicalize" attack on Q3.4.  The naive route is: send each
`U_g` to a bistochastic channel, take many copies, and use an asymptotic
Birkhoff theorem to approximate the result by a convex combination of
classical (permutation) channels, then read off a sofic model.  That route is
dead at its second step for arbitrary channels, and is recorded as such
(`sofic-model-via-quantum-birkhoff-channel-rounding`).

**What it does not kill.**  It says nothing about a *symmetric-extension face
cut out by a group table at the regular trace*, which is what
`definetti-group-table-rounding` proposes to classicalize.  The lesson the
source dossier draws is exactly this: a de Finetti-style argument for Q3.4 has
to live on that special face, and any argument that would also apply to
arbitrary bistochastic channels is refuted before it starts.  It is the
cheapest available sanity check on a proposed rounding theorem.
