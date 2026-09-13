---
rg: 2
id: sl2-subfield-root-links-codistance-q8-q16
kind: claim
title: For q = 8 and q = 16 every subfield root link u(F_q), v(sF_q) of SL_2(q^2) is connected with second singular value below 1 - 2/q (computer-certified)
---

Let `q ∈ {8, 16}`, `k = F_q ⊂ F = F_{q^2}` and `s ∈ F \ k`. Let `Γ_s` be the coset graph
`Γ_{SL_2(F)}(u(k), v(sk))` of `sl2-subfield-root-pair-girth-eight`. It is `q`-regular with
`n = q(q^4 - 1)` vertices on each side: `32,760` for `q = 8` and `1,048,560` for `q = 16`.

**ESTABLISHED (computer-assisted, exact integer arithmetic; unreviewed).** For every such `s`,

```text
σ_2(Γ_s) < 1 - 2/q,     that is  < 3/4 for q = 8  and  < 7/8 for q = 16.
```

Consequences:
- `Γ_s` is connected, so `<u(k), v(sk)> = SL_2(F)`.
- By `coset-graph-singular-values-bound-fixed-space-angles`,
  `cos ∢(V^{u(k)}, V^{v(sk)}) <= σ_2(Γ_s) < 1 - 2/q` in every unitary representation.

**Certified runs and numerical values.** The Lanczos values below are not certified. The girth comes
from BFS at one vertex, which is exact by vertex-transitivity.

| `q` | `s` | girth | top singular values (Lanczos) | certified `σ_2 <` | first certifying `2m` |
|---|---|---|---|---|---|
| 8 | `g` | 10 | 0.683135 (x2), 0.676646 (x2) | 3/4 | 56 |
| 8 | `g^3` | 10 | 0.684017 (x2), 0.630406 | 3/4 | 48 |
| 16 | `g` | 10 | 0.496284 (x2), 0.495010 (x2) | 7/8 | 18 |
| 16 | `g^3` | 10 | 0.494194, 0.494144, 0.492993 | 7/8 | 18 |

Here `g` is a primitive element of `F`. The exact walk counts also give weaker but explicit rigorous bounds:
- `σ_2 <= 0.6915` for `q = 8`, `s = g`, at `2m = 400`;
- `σ_2 <= 0.566` for `q = 16`, `s = g`, at `2m = 60`.

For comparison, the Ramanujan value `2√(q-1)/q` is `0.661` for `q = 8` and `0.484` for `q = 16`; these
links sit slightly above it.

**Two classes of `s` suffice.**
- `Γ_s` depends only on the line `sk`, so `s` matters only up to `k^*`.
- The Frobenius automorphism of `SL_2(F)` maps `(u(k), v(sk))` to `(u(k), v(s^2 k))`, which is a graph
  isomorphism.
- Writing `s = g^j`, the class is `j mod q+1` with `j ≢ 0`, and Frobenius acts by `j ↦ 2j`.
- On `Z/9 \ 0` the orbits are `{1,2,4,8,7,5}` and `{3,6}`. On `Z/17 \ 0` they are
  `{1,2,4,8,16,15,13,9}` and `{3,6,12,7,14,11,5,10}`.
- So `s = g` and `s = g^3` cover everything. The run with `s = g^2` reproduces `s = g` digit for digit,
  which calibrates this symmetry.

Proof: `sl2-subfield-root-links-codistance-q8-q16-proof`.
