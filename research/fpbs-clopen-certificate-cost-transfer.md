---
rg: 2
id: fpbs-clopen-certificate-cost-transfer
kind: claim
title: Cost of a shift measure is an infimum of clopen certificate values, each moving by at most a window total-variation multiple under a change of measure
distinct_from:
  fpbs-kazhdan-local-cost-formula: that writes the Bernoulli cost of a Kazhdan group as an infimum of window statistics of finite-range iid subgraphs; this holds for every invariant measure on a finite-alphabet shift over any finitely generated group, and its certificates are clopen partial maps whose value transfers between two measures with an explicit total-variation error.
artifacts:
  - research/artifacts/fpbs-clopen-certificate-cost-transfer-proof-attempt-2026-09-17.md
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts). It is not established because the
referee vote of lens 1 was lost; lenses 2 and 3 returned *survives*.

**Setting.** `G` is a finitely generated group with finite symmetric generating set `S`, word
length `|.|`, and balls `B_n`. `L` is a finite set, and `G` acts on `L^G` by
`(g.x)(h) = x(g^{-1}h)`. `C(nu)` is the cost of the orbit relation of `G ↷ (L^G, nu)` for
an invariant Borel probability measure `nu`.

A **clopen certificate** `(Phi, l)` is a finite list `Phi = ((gamma_1, A_1), ..., (gamma_M, A_M))`
of group elements `gamma_i` and clopen sets `A_i ⊂ L^G`, together with a length `l >= 1`.
A `Phi`-path of length `k` from `x` is a sequence `x_0 = x, x_1, ..., x_k` where each step is
`x_{t+1} = gamma_i x_t` with `x_t ∈ A_i`, or `x_{t+1} = gamma_i^{-1} x_t` with
`x_{t+1} ∈ A_i`. Its product is the resulting group element, so the path ends at
(product)`.x`. For `s ∈ S` let `N_s(Phi, l)` be the set of `x` from which no `Phi`-path of
length at most `l` has product `s`. This is a clopen set. Put

`c_l(Phi, nu) = sum_i nu(A_i) + sum_{s ∈ S} nu(N_s(Phi, l))`.

Let `W(Phi, l)` be a finite window such that every `A_i` and every `N_s(Phi, l)` is a
cylinder over `W`. `TV_W(nu, nu')` is the total-variation distance of the marginals on `L^W`.

1. **Upper bound.** For every invariant `nu`, `C(nu) <= c_l(Phi, nu)`.
2. **Exactness on free measures.** If `nu` is essentially free, then
   `C(nu) = inf_{(Phi, l)} c_l(Phi, nu)`.
3. **Transfer.** For invariant `nu, nu'`,
   `|c_l(Phi, nu) - c_l(Phi, nu')| <= (M + |S|) TV_W(nu, nu')`. Hence
   `C(nu') <= c_l(Phi, nu) + (M + |S|) TV_W(nu, nu')`.

Item 3 is the quantitative form of the upper semicontinuity of cost at free measures along
weak* limits. All lower-bound content of fixed price sits in the failure of the reverse
inequality; see `fpbs-fixed-price-iff-cost-lsc-at-bernoulli`.

## Attempts

1. **Generator repair edges on the no-path sets, Borel pieces by group element, clopen regularity and cylinder
   total variation (2026-09-17).** Formerly the route `fpbs-clopen-certificate-cost-transfer-proof` (requires
   []); see `research/artifacts/fpbs-clopen-certificate-cost-transfer-proof-attempt-2026-09-17.md`. Demoted on
   2026-09-17 after the referee audit of `fpbs-fixed-price-iff-cost-lsc-at-bernoulli`: the vote of lens 1 was
   lost, so the full referee pass required for ESTABLISHED did not complete. Lenses 2 and 3 returned
   *survives*; lens 3 checked that item 1 generates with no freeness assumption, item 2 uses clopen
   approximation with invariance error at most `|B_{lr}| N theta`, and item 3 is a sum of `M+|S|` cylinder
   events over `W`. No mathematical error has been reported. Restore the route once a full referee pass
   survives.
