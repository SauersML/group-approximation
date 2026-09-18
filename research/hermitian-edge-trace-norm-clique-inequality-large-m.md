---
rg: 2
id: hermitian-edge-trace-norm-clique-inequality-large-m
kind: claim
title: The uniform clique inequality ||C||_1 >= sqrt3 (m-1) holds for every m >= 6, so the Hermitian edge inequality holds on large cliques
artifacts:
  - research/hermitian-edge-trace-norm-clique-inequality-large-m-proof.md
  - experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/verify.py
  - experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/verify_F_m6_D4.log
distinct_from:
  hermitian-edge-trace-norm-clique-inequality: that is the conjecture (UCI) for every m; this proves it for all m >= 6 (m <= 3 was already known), which leaves exactly m = 4 and m = 5 open there.
  hermitian-edge-trace-norm-vs-independence: that is (**) for every graph and weight; this is the case G = K_m, w = 1, m >= 6.
---

**ESTABLISHED (ordinary proof plus one interval-arithmetic verification of a two-variable polynomial
inequality; unreviewed, not Lean-verified; route
`hermitian-edge-trace-norm-clique-inequality-large-m-proof`).**

**Theorem.** Let `m >= 6` and let `C` be a Hermitian `m x m` matrix with `C_ii = 0` and
`|C_ij| >= 1` for all `i != j`. Then

```text
|| C ||_1  >=  sqrt3 (m - 1) .
```

Equivalently, the Hermitian edge inequality (**) of `hermitian-edge-trace-norm-vs-independence`
holds for `G = K_m` with unit weights. With the known cases, (UCI) holds for all `m` except
`m = 4` and `m = 5`.

**Proof in four lines.**
1. *Rank-one reduction.* Put `A = C_+` and `B = C_-`. Both have the diagonal `d`, and
   `sum d = ||C||_1/2`. Einollahzadeh's lemma (arXiv:2309.14958) says that `|a|, |b| <= delta`
   implies `|a - b| <= |delta - conj(a) b/delta|`. The Schur product `conj(A) o B` is PSD. Together
   they give a Gram matrix `G` of unit vectors with `d_i d_j |1 - G_ij|^2 >= 1` for all `i != j`.
2. *Averaging.* Write `sum d = (1/(m-1)) sum_{i<j} (d_i + d_j)`. By AM-GM this is at least
   `(1/(m-1)) E(G)`, where `E(G) = sum_{i != j} 1/|1 - G_ij|` is an energy.
3. *Linear programming bound (Yudin-type).* Let `F(z) = sum c_pq z^p zbar^q` with `c_pq >= 0` for
   `(p,q) != (0,0)` and `F <= 1/|1-z|` on the unit disc. Then `E(G) >= c_00 m^2 - m F(1)`, because
   `[F(G_ij)]` is PSD.
4. *Certificate.* An explicit degree-5 polynomial `F` has rational coefficients and `c_00 = 0.90244`.
   Interval arithmetic verifies `F <= 1/|1-z|` on the disc. For every `m >= 6`,
   `c_00 m^2 - m F(1) >= (sqrt3/2)(m-1)^2`.

**Sharpness of the method, and what is left.** The energy LP is sharp. Its values at `m = 4, 5`,
namely `2 + 4 sqrt2 = 7.657` and `13.764`, are attained by the 4th and 5th roots of unity in `C^1`.
Both are below the needed values `(sqrt3/2)(m-1)^2 = 7.794` and `13.856`. So no uniform-averaging
energy bound can prove `m = 4, 5`. The exact form of the rank-one bound is a fractional matching:
`sum d >= 2 nu_f(r)` with `r_ij = 1/|1 - G_ij|`. Numerically it is sharp at `m = 4, 5`, with values
`1 + sqrt3` and `(5 + sqrt5)/2`. What remains is a statement about maximum matchings of 4 or 5 unit
vectors; see `hermitian-edge-trace-norm-clique-inequality`.
