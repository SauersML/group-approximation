---
rg: 2
id: thompson-t-euler-splitting-witnesses-are-asymptotically-free
kind: claim
title: "Every witness for the measurable Euler splitting of Thompson's T is asymptotically essentially free along its almost invariant densities, so witnesses with local stabilizers must have supports that become dense"
distinct_from:
  thompson-t-euler-class-splits-over-almost-invariant-space: that is the open existence statement (MT); this is a forced shape of every witness, established, which decides nothing about existence
  thompson-t-co-amenable-subgroup-kills-real-euler-class: that is the discrete special case X = T/H; this covers every nonsingular witness, and in the discrete case gives only that the invariant mean on T/H is mean-free
  almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial: that takes IRS limits of finite permutation almost actions; this takes IRS limits of total-variation almost invariant densities of a genuine nonsingular action, and removes the global fixed set using the Euler normalization
  thompson-v-amenable-actions-are-free-off-fixed-points: that is the analogue for invariant means on V-sets; this is for Thompson's T and for measures, and the fixed set is null here rather than a free parameter
  mean-free-amenable-actions-residually-amenable-and-sofic: that defines mean-free actions and proves soficity from them; no soficity is claimed here, since a free probability-measure-preserving action already satisfies the conclusion
artifacts: []
---

**ESTABLISHED** by `thompson-t-euler-splitting-witnesses-asymptotically-free-proof`.

**Setting.** A witness for (MT) is a pair `(X, μ, β)` as in
`thompson-t-euler-class-splits-over-almost-invariant-space`:
- a Borel nonsingular action of `T` on a standard σ-finite measure space `(X, μ)`;
- unit vectors `ξ_n` in `L²(X, μ)` that are almost invariant for the Koopman representation `κ`;
- a measurable cocycle `β : T̄ × X → R`, with `T̄` acting through `T`, and `β(z, ·) = 1` almost everywhere.

Write `ν_n = |ξ_n|² μ`, which are probability measures, and `Fix(g) = {x : gx = x}`.

**Statement.**
1. **(F3) Asymptotic freeness.** For every sequence of almost invariant unit vectors `ξ_n`,
   `ν_n(Fix g) → 0` for every `g ∈ T \ {e}`. Equivalently, the stabilizer
   laws `Stab_* ν_n` converge weak* to `δ_{e}` in `Sub(T)`. In particular, for every finite
   `P ⊆ T \ {e}`, `ν_n{x : Stab(x) ∩ P ≠ ∅} → 0`.
2. **Probability-measure-preserving witnesses.** If `μ` is a `T`-invariant probability measure, then the
   action is essentially free.
3. **Local witnesses need dense supports.** Suppose `x ↦ K(x)` is a Borel map to the closed subsets of `S^1`
   such that every `g ∈ T` equal to the identity on a neighbourhood of `K(x)` fixes `x`. Then:
   - for every nonempty open arc `I`, `ν_n{x : K(x) ∩ I = ∅} → 0`;
   - for every `N`, `ν_n{x : |K(x)| ≤ N} → 0`;
   - for every `ε > 0`, `ν_n{x : K(x) is not ε-dense in S^1} → 0`.

**What it excludes.** A witness cannot have a set of `ν_n`-mass bounded below on which the stabilizers
contain a fixed nontrivial element. Item 3 excludes, among others, the following as witnesses along
any almost invariant sequence:
- configuration spaces of at most `N` marked points of `S^1`, for every `N` and every marking that
  `T` transports locally;
- spaces of functions or measures on `S^1` whose supports stay inside a proper closed arc with
  probability bounded below.

These are not excluded by (F2), since they need not map equivariantly to `S^1`. In the discrete case
item 1 says that the invariant mean on `T/H` given by co-amenability is mean-free.

**Scope.** Item 1 is IRS rigidity of `T`, obtained from its character rigidity, applied to limits of
almost invariant densities. The only extra input is that the global fixed set is null, which follows from
the Euler normalization because `T̄` is perfect. No novelty is claimed for the rigidity step. The
statement (MT) stays OPEN: a free probability-measure-preserving action, such as a Bernoulli shift,
satisfies items 1–3 and fails, if at all, only in the cocycle.
