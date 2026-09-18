---
rg: 2
id: fpbs-product-amenable-factor-mean-field-deficit
kind: claim
title: Percolation on a nonamenable factor times a spread-out amenable factor is mean-field at second order in the critical reciprocal
distinct_from:
  fpbs-nb-spectral-deficit-obstruction: that proves the deficit criterion and the H-only lower bound it imposes on any counterexample; this is the open p_c asymptotic that would feed that criterion on products.
  fpbs-percolation-kesten-normal-gap: that asks for a relative threshold gap for every normal subgroup on every generating set; this is only the high-degree product regime and is a statement about p_c(G) alone.
---

**OPEN.** Let `H` be finitely generated with finite symmetric `S_H`, `d_H = |S_H|`
and `||A_H|| < d_H`. Let `B_k` be Cayley graphs of amenable groups with degrees
`d_k -> infinity`, for example `Z^k` or spread-out balls in `Z^2`. Put
`G_k = Cay(H,S_H) □ B_k` and `d = d_H + d_k`. The claim is

```text
D(G_k) = d - 1 - 1/p_c(G_k)  ->  0     (k -> infinity),
```

or at least `limsup D(G_k) < d_H - ||A_H||`.

**Consequence.** By `fpbs-nb-spectral-deficit-obstruction` Corollary 3,
`p_c(G_k) < p_u(G_k)` for all large `k`, for every nonamenable `H`. This
includes Kazhdan `H` and torsion `H`, where the nonunimodular, hyperbolic,
acylindrically hyperbolic and cost theorems do not apply. It would kill the
class "nonamenable times an amenable factor with a large generating set" as a
source of counterexamples.

**Evidence and calibration.** For `B_k = Z^k` with trivial `H`,
`1/p_c(Z^k) = 2k - 1 - 5/(4k) + O(k^-2)` by the lace-expansion asymptotics of
Hara–Slade and van der Hofstad–Slade. This is quoted from memory and not
imported. So the deficit of the amenable factor alone tends to `0`.

The mean-field heuristic predicts `1/p_c(G_k) = d - 1 - O(cycle density/d)`, and
`G_k` has `O(d^2)` squares per vertex. That also gives `D -> 0`.

## Attempts

**Why the easy bounds fail.** Each loses exactly the needed amount:

* `p_c(G_k) <= p_c(B_k)` gives only `D(G_k) <= D(B_k) + d_H`;
* covering by `T_{d_H} □ B_k` goes the wrong way;
* Kesten-type second-moment arguments give `1/p_c >= d(1 - o(1))`, a deficit of
  `o(d)` rather than `o(1)`.

**Where it can fail on its own.** The claim can fail independently of
Benjamini–Schramm: short cycles of `H` could raise `D` by order one. For
example, if `S_H` contains many triangles, the `H`-directions contribute fewer
than `d_H` effective offspring. The claim is then false for that `S_H`, while the
obstruction still demands `D >= d_H - ||A_H||`, and the two margins compete. A
lace expansion on `G_k` needs a triangle-type bound. On nonamenable `G_k` there
is no Fourier transform, so the Hara–Slade bootstrap must be redone with
operator norms.
