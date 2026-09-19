---
rg: 2
id: fpbs-mal-simple-chain-count-uniform
kind: claim
title: Vertex-simple chains of prescribed relative positions between adjacent K-classes number at most rho^n, uniformly in the double cosets
distinct_from:
  fpbs-mal-stage-block-sprinkling-threshold: that counts simple paths for the single relative position K b K, getting at most 2^{25 m}; this asks for the same exponential count uniformly over all sequences of double cosets, with unbounded word length.
  fpbs-mal-two-step-relative-position-rigidity: that is the established length-two case, bound 12; this is the all-length statement.
  fpbs-malnormal-coset-cycles-linear-perimeter: that bounds the perimeter of coset cycles of packing certificates; this counts chains whose steps are arbitrary relative positions.
artifacts:
  - research/artifacts/fpbs-iid-chord-union-bound-2026-09-19.md
  - experiments/fpbs-iid-chord-union-bound-2026-09-17/simple.py
  - experiments/fpbs-iid-chord-union-bound-2026-09-17/s3_long.py
  - experiments/fpbs-iid-chord-union-bound-2026-09-17/s3_long_out.txt
  - experiments/fpbs-iid-chord-union-bound-2026-09-17/s3_mid.py
  - experiments/fpbs-iid-chord-union-bound-2026-09-17/s3_mid_out.txt
---

**OPEN.** Let `F = F(a, b)` and `K = <a, b a b^{-2}>`, and let
`D(A, B) = K z y^{-1} K` be the relative position of the right cosets
`A = Ky`, `B = Kz`. For double cosets `D_1, ..., D_n ≠ K`, let
`N_n(D_1..D_n)` be the number of sequences of **pairwise distinct** right
cosets

```text
K = C_0, C_1, ..., C_n = K b      with  D(C_{i-1}, C_i) = D_i .
```

**Claim.** There is `rho < infinity` with `N_n(D_1..D_n) <= rho^n` for all
`n` and all `D_1, ..., D_n`.

**Why it matters.** By Lemma 1 of the artifact, the claim implies
`fpbs-mal-iid-chord-graphings-floor`: independent chord graphings of mass
`< 1/(6 rho)` never generate `E_F` over `E_K`, whatever the label law.

**Known.**
- `n = 1`: `N_1 <= 1`, by malnormality.
- `n = 2`: `N_2 <= 12` for arbitrary endpoints
  (`fpbs-mal-two-step-relative-position-rigidity`).
- Single position `D_i = K b^{±1} K`: the claim holds with an explicit `rho`
  by the hull-nerve count of `fpbs-mal-stage-block-sprinkling-threshold`,
  subject to that claim's open freeness import. Only its combinatorial count
  is needed here.
- Data (artifact §3): `N_3 <= 3` and `N_4 <= 5` in every scan so far. This
  covers short labels, random long labels up to length 16, folding labels,
  periodic labels, and labels with a buried `K`-syllable of length 1 or 2
(longer syllables did not finish).

**Where it could fail.** Use the chain's hulls `X_0, ..., X_n` in the Cayley
tree. A long label whose reduced word contains a long path of the core can
run along another hull `X_j` of the chain. Then the path segment `sigma_j`
inside `X_j` is cancelled by a bridge, and not only by the at most 2-edge
overlaps of (F1). The attachment offset along that bridge has about `|h|`
possible values. A crude count therefore gives only
`N_n <= C^n prod (1 + |h_i|)^{O(1)}`, and this polynomial count was not
proved either. A family where `N_3` grows with the label length would refute
the uniform claim. It would also kill the uniform union-bound route, but not
the floor itself.
