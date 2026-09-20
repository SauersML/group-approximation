---
rg: 2
id: fpbs-mal-seed-density-towers-over-orbit-gapped-bases
kind: claim
title: Over any finite transitive F(a,b)-set whose L_j-orbits are all spectrally gapped below a fixed lambda_0 > sqrt(3)/2, random lifts give an essentially free profinite tower with transitive levels whose phi^j-twisted seed density stays at least (1 - lambda_0)/6; in particular over the Cayley level of Sym(j+2), with density 1/60
distinct_from:
  fpbs-mal-twisted-level-seed-density-uniform-witness: that builds the tower over a point and uses a global gap of M_j on each level; this builds it over an arbitrary base B, allowing B and every level to be L_j-intransitive, and uses the gap orbit by orbit. That node is the case B = point.
  fpbs-mal-overfold-merges-never-help: that is the open exchange statement; this is a density statement, and it is what lets the exchange be asked only on covers of a chosen base.
  fpbs-mal-sym-levels-embed-orbits-at-every-depth: that computes the L_j-orbits of the Sym(d) levels; this uses only that on B_j they have size 2, so that their top non-trivial eigenvalue is -1.
artifacts:
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/spectral_sym.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/spectral_sym_m3_m8.txt
---

**ESTABLISHED** through
`fpbs-mal-seed-density-towers-over-orbit-gapped-bases-proof`.

Notation is as in
[[fpbs-mal-twisted-level-seed-density-uniform-witness]]. For a finite
`L`-set `Q` and `j ≥ 0`:
- `M_j = (U_a + U_a^* + U_{t_j} + U_{t_j}^*)/4` on `ℓ²(Q)`;
- `I_j(Q)` is the space of `L_j`-invariant functions, equivalently the
  functions constant on each `L_j`-orbit;
- `μ_j(Q)` is the largest eigenvalue of `M_j` on `I_j(Q)^⊥`, or `−1` if that
  space is `0`. Equivalently, it is the largest eigenvalue of `M_j` on
  `ℓ²_0(O)`, maximised over the `L_j`-orbits `O` with `|O| ≥ 2`.

Note that `μ_j` is a top eigenvalue, not a norm. A two-point orbit on which
`a` and `t_j` act by the same swap has `μ_j = −1`.

**Claim.** Let `ρ = √3/2`, `λ_0 ∈ (ρ, 1)` and `j ≥ 0`. Let `B` be a finite
transitive `L`-set with `μ_j(B) ≤ λ_0`. Then there is an essentially free
profinite action `X = lim Q_m` of `L` such that:
- `Q_0 = B`, and each `Q_{m+1} → Q_m` is an `L`-equivariant surjection, so
  every level is a finite cover of `B`;
- every level `Q_m` is transitive;
- `r(Q_m^{(j)}) ≥ (1 − λ_0)|Q_m|/6` for every `m`.

**Instance.** Let `B_j` be the Cayley level of `Sym(j+2)`, with `a ↦ (0 1)`
and `b ↦ (0 1 ⋯ j+1)`. By item 4 of
[[fpbs-mal-sym-levels-embed-orbits-at-every-depth]], every `L_j`-orbit of
`B_j` is `{g, gα}`, with `a` and `t_j` both acting by `g ↦ gα`. So `M_j` acts
as `−1` on `ℓ²_0` of each orbit, and `μ_j(B_j) = −1`. With `λ_0 = 0.9`, the
claim gives, for every `j`, a tower over `B_j` with density at least `1/60`.
This is the same constant as the tower over a point.

**Why a base is needed.** A single tower that passes through every `B_j`
inherits, as old eigenvalues, the spectra of the `L_j`-orbit graphs of
`Sym(m)` for `m = d − j`. These are the Cayley graphs of `Sym(m)` for an
adjacent transposition and an `m`-cycle. `spectral_sym.py` gives their gaps
`1 − λ_2 = 0.75, 0.19, 0.094, 0.054, 0.034, 0.023` for `m = 3, …, 8`, which
tend to `0`. So a spectral bound cannot use one tower for all `j`. The claim
instead uses one tower per depth, over `B_j` itself, where the orbits are
as small as possible. By Theorem M of
[[fpbs-mal-promotion-cost-monotone-under-weak-containment]], per-depth
witnesses suffice.
