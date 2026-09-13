---
rg: 2
id: standard-identity-witnesses-force-block-displacement
kind: claim
title: Standard-identity witnesses force block displacement, so bounded-rank frame-coherent microstates round to sofic approximations at explicit cost
distinct_from:
  block-monomial-hs-models-sofic-mod-amenable-soft-kernel: that is the qualitative ultraproduct theorem (the soft kernel is amenable, abelian for monomials); this is its finitary, dimension-free quantitative form with explicit constants and an explicit rounding rate.
  amenable-hyperlinear-rounds-to-sofic: that rounds arbitrary microstates of amenable groups in the same dimension; this rounds microstates of arbitrary groups, provided they preserve a bounded-rank coarse frame and the window has witnesses.
  uniformly-discrete-block-monomial-images-are-sofic: that needs finite label groups with a uniform character gap; this needs no gap on the labels and pays with a group-theoretic witness instead.
artifacts:
  - research/artifacts/ex-q34-imprimitivity-witness-2026-09-12.md
---

**ESTABLISHED.**  Let `U : F -> U(k) wr S_n` be block-monomial with block size
`k`, permutation parts `sigma_x`, multiplicative defect `<= delta` on `F`, and
regular trace `|tr U_w| <= delta` for `w in F \ {e}`.

**Witness lemma.**  Let `g in F` and `h_1..h_(2k) in F`, put
`g_i = h_i g h_i^(-1)`, and suppose the `(2k)!` ordered products
`w_pi = g_(pi 1)...g_(pi 2k)` are pairwise distinct.  Suppose `F` holds the
needed products, prefixes, inverses and quotients `w_pi^(-1) w_pi'`.  Then

```text
d_H(sigma_g, id) >= 1/(8 k^2 (2k)!) - C_k delta .
```

Proof idea: small displacement of `g` means small displacement of its
conjugates, so all `U_(g_i)` are near block-diagonal.  Block-diagonal matrices
satisfy the Amitsur--Levitzki identity `S_(2k)`, but regular traces force
`||sum_pi sgn(pi) U_(w_pi)||_2^2` to be about `(2k)!`.  For `k = 1` the witness is a
single non-commuting conjugate of `g` (normal closure nonabelian), with
constant `1/16`.

**Quantitative rounding.**  If every `g in E \ {e}` has a witness in `F` and
`delta <= delta_k`, the `m`-fold tensor powers of the permutation parts, with
`m = ceil(2 log(1/eps)/c_k)` and `c_k = 1/(8 k^2 (2k)!)`, are `(E, eps)`-sofic
approximations.  Their Hamming defect is `<= m delta^2/2` and their separation
is `>= 1 - eps`, with no dependence on `n`.  With
`coarse-frame-normalizers-are-near-block-monomial` the same holds for
microstates that approximately preserve an equal-rank decomposition of rank
`k` on generators (defect `def_B`), at cost `O(def_B)` propagated along words.

Model tests: in abelian groups no witness exists, and diagonal random-character
models are indeed regular with zero displacement.  In `F_2`, `a` and `bab^(-1)`
witness `a`: a diagonal `U_a` would commute with its conjugate, and the trace of
the commutator would be `1`.  `c_k -> 0` is forced, because `n` diagonal copies
of any microstate are block-monomial with zero displacement once `k` is
unbounded.

## Attempts

Established; see `standard-identity-witnesses-force-block-displacement-proof`.
