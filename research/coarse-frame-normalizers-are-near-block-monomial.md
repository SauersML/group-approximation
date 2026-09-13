---
rg: 2
id: coarse-frame-normalizers-are-near-block-monomial
kind: claim
title: Approximate normalizers of an equal-rank coarse frame are near block-monomial, uniformly in the rank
distinct_from:
  diagonal-normalizer-rigidity: that rounds approximate normalizers of the full diagonal masa to monomials; this rounds approximate normalizers of any equal-rank abelian subalgebra to U(k) wr S_n, where no monomial approximation exists (the Fourier-block example).
  block-monomial-coordinate-collapse: that starts from matrices already exactly block-monomial over a coarse index set; this proves that uniformly approximate normalization of the coarse diagonal forces nearness to such matrices at an explicit, rank-free cost.
artifacts:
  - research/artifacts/ex-q34-imprimitivity-witness-2026-09-12.md
---

**ESTABLISHED.**  Let `p_1..p_n` be orthogonal rank-`k` projections with sum
`1` on `C^(nk)`, `B = span{p_i}`, and for a unitary `u`

```text
def_B(u) = sup{ ||u f u^* - E_B(u f u^*)||_2 : f = f^* in B, ||f|| <= 1 }
```

in normalized Hilbert--Schmidt norm.  If `def_B(u) <= delta`, there are a
permutation `sigma` of the blocks and unitaries
`w_i : ran p_i -> ran p_(sigma(i))` with

```text
|| u - sum_i w_i ||_2 <= 2 sqrt(3) delta ,
```

with no dependence on `k` or `n`.  Moreover `def_B(uv) <= def_B(u) + def_B(v)`
and `def_B(u') <= def_B(u) + 2 ||u - u'||_2`.  So frame control on generators
propagates to words with linear loss.

For `k = 1` this is `diagonal-normalizer-rigidity` clause 1 with a linear
rather than square-root constant.  For `k > 1` it is the finitary form of an
approximate *system of imprimitivity*: a unitary microstate that
approximately preserves an equal-rank orthogonal decomposition is close to an
induced-type block-monomial matrix.  The soft-kernel theory of
`block-monomial-hs-models-sofic-mod-amenable-soft-kernel` then applies.

Model tests: the Fourier-block unitary `⊕_j F_m` exactly normalizes
`ℓ^∞_n ⊗ 1_m`, and the lemma returns it with trivial permutation.  A Haar
unitary has `def_B` close to `1` when `k << n`.

## Attempts

Established; see `coarse-frame-normalizers-are-near-block-monomial-proof`.
