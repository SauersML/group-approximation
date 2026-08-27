---
rg: 2
id: atlas-stabilizer-coset-witness
kind: route
title: Deform the tensor flip inside the index-15 stabilizer commutant until the atlas relators die
target: leavitt-steinberg-hs-unstable
requires: []
artifacts:
  - research/artifacts/atlas-true-criterion-probe-2026-08-15.md
  - research/artifacts/hyperlinear-q34-audit-2026-08-16.md
  - experiments/atlas_stabilizer_coset_search.py
  - experiments/atlas_true_criterion_stage1.py
---

# The index-15 stabilizer-coset lane

The cheapest attack on the explicit one-unitary criterion, and the first stage
of the campaign designed in `atlas-true-criterion-baseline` §(d).  Under
`A₈ ≅ GL₄(𝔽₂)` let `M < A₈` be the stabilizer of a nonzero vector
(`|M| = 1344`, index 15), so that `ℓ²(A₈) ≅ ℓ²(M) ⊗ ℂ¹⁵` and the first chart
restricted to `M` is `λ_M ⊗ I₁₅`.  Start at the tensor flip `J` — the best
classical warm start, exactly zero on 4,564 of 4,636 relators — and search

```
U = D J ,        D ∈ I_{ℓ²(M)} ⊗ U(15k) ,
```

i.e. deform inside 1,344 identical `15 × 15` blocks.  The attraction is
arithmetic: the objective decomposes into 15-dimensional blocks, three orders
of magnitude cheaper per evaluation than unrestricted `U ∈ U(20160k)`, so the
whole `V`-landscape is sweepable before any stage-2 spend.  Drive the 72
cartesian escapees to zero without breaking the 4,564 already-satisfied
control relators and the criterion is met.

**Dead: `atlas-stabilizer-commutant-no-go`.**  Every `D` in this family
commutes exactly with the first chart's copy of `M`, and right translations
commute with left ones, so the family silently imposes the extra exact
relation `[π₁(m), π₂(b)] = 1` for all `m ∈ M`, `b ∈ A₈`.  The commutator
`c = [p¹₀₁, p²₁₀]` — legal because the transvection `p₀₁` fixes the stabilized
vector — is therefore killed *exactly* in every member of the family, while its
image in `Q` is nontrivial.  Quasisimplicity of `P̄/⟨⟨T_St⟩⟩` then forbids the
defects from ever tending to zero, at every multiplicity `k` and for arbitrary
`U(15k)` blocks.  The MSI Stage-1 pilot's flat landscape was the first-order
shadow of this (`atlas-stabilizer-slice-stationary`): the gradient at `J` is
exactly zero in every `U(15)` direction, so the flatness was structural rather
than an under-optimized run.

**What survives.**  Only the unrestricted lane: `U_n ∈ U(20160 k_n)` with no
asymptotically preserved exact commutant of a first-chart subgroup.  The
cost wall recorded in the probe artifact (180,716 `U`-applications per full
evaluation) is unrelieved, and the cheap warm start is now known to be a trap
rather than a head start.  The no-go's reusable screen — evaluate whichever
relations an ansatz forces in the binary-Leavitt normal form *before*
optimizing — is the practical residue of this route.
