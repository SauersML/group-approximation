---
rg: 2
id: infinite-simple-kazhdan-limit-of-alternating-groups
kind: claim
title: Some infinite simple Kazhdan group is a marked limit of alternating groups
distinct_from:
  torsion-free-kazhdan-alternating-mother-limit-gate: that asks for a TORSION-FREE simple Kazhdan limit of alternating quotients of one mother; this allows torsion and asks for any infinite simple Kazhdan marked limit of alternating groups.
  finite-simple-groups-converge-to-simple-kazhdan-group: that gives simple Kazhdan limits of projective special linear groups; this asks for alternating approximants.
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part3.md
---

**OPEN.** Is there an infinite finitely generated simple group with property (T) that is a limit, in the space of
marked groups, of alternating groups `A_(n_k)`, `n_k → ∞`?

By `simple-lef-groups-are-limits-of-finite-simple-groups`, the finite simple approximants of an infinite simple group
are eventually alternating of unbounded degree or of unbounded Lie rank. The known Kazhdan examples (`G_X`, the
lamplighter hosts) are limits of `SL_N(F_2)`.

## Attempts

- **(T) forces asymptotic freeness (sk-free-4, artifact part 3 §2).**
  - By `kazhdan-marked-limits-eventually-uniform-expanders`, large approximants are quotients of one Kazhdan group.
  - A transitive action on `Ω_k` then has a uniform gap on `ℓ^2_0(Ω_k)`, so the limit fixed-point character `χ`
    satisfies `Σ_w p_m(w)χ(w) ≤ (1−δ)^m`.
  - For a character-rigid limit (`subshift-elementary-groups-are-character-rigid`), `χ = δ_e`: every transitive
    permutation approximation, including the natural action of `A_(n_k)`, is asymptotically free.
  - This does not exclude alternating limits. It only says they are sofic approximations whose images generate the
    full alternating group.
- **Mother groups with alternating quotients exist** (finite-index subgroups of `Out(F_5)`, via Kaluba–Nowak–Ozawa and
  Gilman; see the gate node). Every limit is Kazhdan and LEF, but simplicity of a limit is not known. Simplicity needs
  bounded-length normal generation of the generators by each nontrivial ball element, uniformly in `k`.
- **Quotients do not help.** A simple quotient of a limit `K` is not a limit of the same alternating groups: imposing
  its extra relators kills the simple approximants.
