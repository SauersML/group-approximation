---
rg: 2
id: thompson-v-rank-models-through-displacing-sym-reps-are-trivial
kind: claim
title: Rank models of Thompson's V built from symmetric-group representations with positive 3-cycle displacement are trivial
distinct_from:
  transvection-displacement-forces-exact-local-embedding: that forces exactness for stage maps into GL_m(F_2) through transvection commutators; this is the symmetric-group analogue through 3-cycle commutators, applied to V, where exactness kills the model because V is finitely presented and infinite simple.
  monomial-rank-models-are-hamming-models: that turns monomial models into Hamming models; this excludes every model whose stages are symmetric-group representations with 3-cycle displacement bounded below, monomial or not, and leaves the natural permutation modules, whose displacement tends to zero.
---

**ESTABLISHED** (route `thompson-v-sym-rep-rank-models-local-embedding-proof`). The argument was found by
`w3-gate-construct` and landed by `w3-gate-v`.

Let `F` be any field and `sigma = lim_omega sigma_k : V -> M^x` a homomorphism into a rank ultraproduct
of the `M_(n_k)(F)`. Suppose `sigma_k = pi_k o phi_k`, where:
- `phi_k : V -> S_(m_k)` are arbitrary set maps;
- `pi_k : S_(m_k) -> GL_(n_k)(F)` are linear representations;
- the normalized 3-cycle displacement `d_k = rk(pi_k(t) - 1)/n_k` satisfies `lim_omega d_k > 0`.
  All 3-cycles are conjugate, so `d_k` does not depend on `t`.

Then `sigma` is trivial.

**Scope.**
- **Killed:** the regular module of `S_(m_k)` (`d_k = 2/3`), and the `j`-subset modules with `j/m_k`
  bounded away from `0` and `1`. Applied to leaf permutations of finite dyadic trees, this kills every
  Cantor-truncation model that passes through such modules.
- **Survives:** the natural permutation module `F^(m_k)` (`d_k = 2/m_k`), and fixed tensor powers of
  it (`d_k = O(1/m_k)`). A symmetric-group-built rank model of `V`, if one exists, lives in the
  vanishing-displacement regime, where the question is again of sofic type (`thompson-v-is-sofic`).
- **For the gate:** a counterexample to `thompson-v-has-no-nontrivial-f2-rank-model` built from finite
  symmetric groups must have 3-cycle displacement tending to zero.
