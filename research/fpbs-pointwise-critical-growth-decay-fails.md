---
rg: 2
id: fpbs-pointwise-critical-growth-decay-fails
kind: claim
title: The critical two-point function does not decay pointwise at rate gr, already on Z x F_3 and on a product of two trees
distinct_from:
  fpbs-worst-pair-connectivity-rate-kernel: that node uses Hutchcroft's bound on the worst pair kappa_(p_c)(n) <= gr^(-n); this node shows the bound cannot be upgraded to all pairs, not even with a slightly smaller exponent
  fpbs-sphere-two-point-rate-right-continuous-universal: that node's EG0 bullet cites a pointwise bound tau_(p_c)(o,x) <= gr^(-|x|); this node refutes that bound, so EG0 needs another route
artifacts:
  - experiments/pointwise-critical-decay-2026-09-17/check_block_certificate.py
  - experiments/pointwise-critical-decay-2026-09-17/output.txt
---

**ESTABLISHED.** Proof in `fpbs-pointwise-critical-growth-decay-fails-proof`.

**Claim.** Let `T_d` be the `d`-regular tree, with `T_2 = Z`. Let
`G = T_a □ T_b` be the Cartesian product. It is the Cayley graph of the
direct product of the two free products of copies of `Z/2`, or of `Z` and `F_n`
when the degree is even, with the union of the two standard generating sets.
Put `D = a+b`, `p0 = 1/(D-1)` and `gr = lim |B_n|^(1/n)`. If `2 <= a < b`, then
`gr = b-1`. Let `z_k = (x_k, y_k)` with `|x_k| = |y_k| = k`, so `|z_k| = 2k`.
Then

```text
tau_(p_c)(o, z_k) >= (2 p0^2 - p0^4)^k      for all k >= 0.
```

So `sup_z tau_(p_c)(o,z) gr^(|z|) = infinity` whenever
`R := (b-1)^2 (2 p0^2 - p0^4) > 1`. Exact values of `R`:

| group (standard generators) | trees | `gr` | `R` |
|---|---|---|---|
| `(Z/2)^{*3} x (Z/2)^{*10}` | `T_3 □ T_10` | 9 | `287/256 ≈ 1.1211` |
| `F_2 x F_6` | `T_4 □ T_12` | 11 | `54329/50625 ≈ 1.0732` |
| `Z x F_3` | `T_2 □ T_6` | 5 | `2425/2401 ≈ 1.0100` |

Even the weaker bound `tau_(p_c)(o,x) <= C gr^(-(1-eps)|x|)` fails. On
`T_3 □ T_10` it fails for `eps < log R / (2 log 9) ≈ 0.026`. The smallest
violating `b` for each `a` is listed in the experiment output: for example
`b = 6` when `a = 2`, and `b = 9` when `a = 3`.

**Consequences.**

1. Hutchcroft's critical bound (arXiv:1605.05301, quoted verbatim as [H16] in
   `research/artifacts/fpbs/docs/lq-two-point-walk-rate-2026-09-17.md`)
   bounds the infimum `kappa_(p_c)(n) = min_(B_n) tau_(p_c)(o,.)`. The claim
   shows that it has no pointwise form. So the EG0 justification in
   `fpbs-sphere-two-point-rate-right-continuous-universal` and in Section 4 of
   `research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md`
   cannot be repaired by a better citation.
2. This kills a class of approaches: every route that bounds a critical sphere
   sum or `l^q` norm by `|S_r| · sup_(x in S_r) tau_(p_c)(o,x)` together with
   a gr-rate pointwise decay. Each of them fails at the diagonal blocks above.
3. The failure is about the pointwise bound, not about EG0 itself. On these same
   graphs `g(p_c) = 0` holds, by `fpbs-critical-sphere-rate-vanishes-on-tree-products`.
