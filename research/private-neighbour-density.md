---
rg: 2
id: private-neighbour-density
kind: claim
title: A random high-degree root parameter is a private neighbour with probability tending to one
distinct_from:
  minimal-marked-graph-private-neighbour: that asserts existence of one separating vertex per finite set, by a coset-avoidance argument that names no distribution; this measures the density of the good parameters inside an explicit finite box and is what an ensemble-of-blocks construction consumes — existence of a single witness would not supply it.
  marked-double-coset-infinite-degree: that says the neighbour set is infinite; this counts, inside a degree-bounded box of the root parameter, how large the separating fraction is.
artifacts:
  - research/artifacts/kun-thom-private-neighbour-2026-08-18.md
---

Notation as in `minimal-marked-graph-private-neighbour`.  For `L ≥ 0` let
`P_L ⊆ R₊` be the `F_q`-span of the monomials `x^α` with `0 ≤ α_j ≤ L`, so
`dim P_L = (L+1)^d`.  For `f ∈ R \ R₊` write the denominator ideal as
`I_f = x^u R₊` with `u ≠ 0`, and put

```text
κ_u(L) = (L+1)^d − ∏_{j=1}^d max(L − u_j + 1, 0)   ~   (Σ_j u_j)(L+1)^{d−1}.
```

1. For every `c ∈ R`, the set `{a ∈ P_L : af + c ∈ R₊}` is empty or a coset
   of `I_f ∩ P_L` in `P_L`, hence of relative size exactly `q^{−κ_u(L)}`.
2. Consequently, for a fixed finite competitor family with denominators
   aligned into a common row, a parameter `a` drawn uniformly from `P_L`
   fails to give a private neighbour with probability at most
   `Σ_i q^{−κ_{u_i}(L)} → 0` as `L → ∞`; and independent uniform shear
   parameters from `P_L` fail to align the same family with probability at
   most the same bound.

So the two nonconstructive choices in `minimal-marked-graph-private-neighbour`
are generic: high-degree random polynomials work, and the failure probability
decays like `q^{−c L^{d−1}}`.

**Why this is wanted.**  `finite-clifford-symplectic-section-obstruction`
rules out an exact global symplectic-to-Clifford section, so any surviving
construction must dilute a defect across many blocks rather than remove it
from one.  Diluting by tensoring is known not to work
(`wall-energy-amplification`, `additive-index-instability`); direct-sum
dilution needs a large supply of independent legal completions, and this
claim is what says the supply exists and is easy to sample.

## Scope

The density is measured in the root parameter of one fixed direction `(p,q)`
and in the shear parameters of one fixed row, against one fixed finite
competitor family.  It gives no joint statement over all finite families at
once, and no statement whatever about Clifford cocycle values of the
resulting completions — whether those are equidistributed is the open
computation recorded in `minimal-marked-graph-crossed-product-ce`.
