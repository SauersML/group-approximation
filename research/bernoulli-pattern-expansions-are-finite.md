---
rg: 2
id: bernoulli-pattern-expansions-are-finite
kind: claim
title: Over every torsion-free host the ranks of each Bernoulli K-class have vanishing mixed differences at far sites, so pattern expansions are finite and shape (a) never occurs
distinct_from:
  bernoulli-assembly-injective-beyond-the-host: that defines ranks, pattern coefficients and the three shapes, and shows coefficients vanish on B-separated patterns; this shows they vanish on every pattern of large diameter, so shape (a) is empty.
  bernoulli-defects-vanish-along-bcc-subgroup-tubes: that restricts defects along tubes of subgroups satisfying Baum--Connes with coefficients; this proves bounded diameter of pattern coefficients for every host with no hypothesis, which removes shape (a) along tubes and off them.
---

**ESTABLISHED** by `bernoulli-pattern-expansions-are-finite-proof` (unreviewed). Full proofs:
`research/artifacts/bc-bernoulli-rank-locality-2026-09-13.md`.

**Setting.** `G` is countable and torsion-free with a proper length function, `Z = G`, `X = Λ^G` and
`I_1 = C_0(X \ {0})`. Ranks `r_x`, the pattern expansion `n(y)` and the shapes (a), (b), (c) are those of
`bernoulli-assembly-injective-beyond-the-host`.

**Theorem.**
1. **Far-site mixed differences vanish.** For each projection `p` over `I_1 ⋊_r G` there is `d_0` such that
   `r_(x^(uv))(p) - r_(x^u)(p) - r_(x^v)(p) + r_x(p) = 0`. This holds for every finite-support `x`, all sites `u, v`
   with `d(u, v) >= d_0`, and any symbol changes at `u` and `v`.
2. **Finite expansions.** For each `y ∈ K_0(I_1 ⋊_r G)`, `n(y)` vanishes on patterns of diameter at least `d_0(y)`. So
   it is supported on finitely many orbits, and `r_x(y) = r_x(T_r(n(y)))` for every `x`.
3. **No shape (a).** Over every countable torsion-free host, the **graded** cylinder comparison fails to be surjective iff there is a nonzero
   rank-invisible tail class (shape (b)) or `K_1(I_1 ⋊_r G) ≠ 0` (shape (c)).
4. **Gapped local operators.** A self-adjoint configuration-local operator with a spectral gap uniform over all
   finite-support configurations has, above the gap, ranks that form a finite combination of pattern counts.

**Why it holds.**
- Every projection is uniformly gapped at every configuration. A single-site change is a bounded block of the
  orbit representation.
- The rank difference it causes is a contour integral of a trace.
- The mixed difference at two sites is a trace through a resolvent between the two blocks. Combes--Thomas
  conjugation bounds that resolvent by `C e^(-α d)`, with no volume or growth factor.
- An integer of absolute value below `1/2` is `0`.

**What it decides.** No spectral gap over the full shift, on any host (monsters included), produces a non-local rank.
The embedded expanders of a monster cannot give a shape-(a) witness for
`bernoulli-cylinder-comparison-fails-for-some-group`. A witness must be invisible to all finite-support orbit
representations.

**Model tests.**
- For `G = Z`, `T_r` is an isomorphism, which is consistent.
- On `Z^2` the induced-subgraph component count has mixed difference `1` at two far sites, via the boundary of a large
  square. It is not a rank of any projection, because long induced paths close every gap. So the theorem excludes
  exactly this kind of rank.
- For a cylinder `1_(C_s)`, mixed differences vanish beyond `diam F_s`.

**Scope.**
- Torsion-free hosts, with `Z = G`.
- The estimates are the standard Combes--Thomas bound and integrality of relative traces of projections, proved inline.
- Bounded novelty check: not in the predecessor artifacts or CEKN Sections 1--2. No web search was done.

**Downstream deductions, 2026-09-20.** The finite coefficients define an
integer retraction N of T, with kernel exactly the rank-invisible K_0
subgroup. See `bernoulli-assembly-defects-split-into-host-and-tail` for
the ordinary wreath kernels and cokernels. Every independent product
trace of that subgroup vanishes, and all product traces are finite
cylinder formulas (`bernoulli-product-traces-have-finite-cylinder-form`).
Neither conclusion proves that the virtual subgroup or K_1 vanishes.
