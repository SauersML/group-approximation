---
rg: 2
id: hermitian-edge-trace-norm-odd-antihole-c11-clique-cover
kind: route
title: Cover the complement of the 11-cycle by its 11 five-cliques and apply the certified K5 bound c_5 >= 7.0857 > 45 sqrt3/11
target: hermitian-edge-trace-norm-odd-antihole-c11
requires:
  - hermitian-edge-trace-norm-clique-k5-margin
artifacts:
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/k5hi_runs.log
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/README.md
---

An ordinary proof on top of one computer-assisted input. Lane w7-078, 2026-09-18.

**Theorem.** Every admissible `C` on `C̄_11` has `||C||_1 >= 9 sqrt3`.

## Step 1. Clique covering

The sets `U_t = {t, t+2, t+4, t+6, t+8}` (mod 11) are cliques of `C̄_11`. Two of their elements
differ by an element of `{±2, ±4, ±6, ±8}` mod 11, so never by `0` or `±1`. Each vertex lies in
exactly 5 of them. Write `C = P - N` with `P, N >= 0` and `PN = 0`, so `|C| = P + N`. For every
vertex set `U`,

```text
|| C_U ||_1  <=  || P_U ||_1 + || N_U ||_1  =  tr P_U + tr N_U  =  sum_{i in U} |C|_ii .
```

Summing over `t`:

```text
sum_t || C_{U_t} ||_1  <=  5 sum_i |C|_ii  =  5 || C ||_1 .
```

## Step 2. The K5 bound

Each `C_{U_t}` is Hermitian with zero diagonal and off-diagonal moduli `>= 1`, since `U_t` is a
clique. By `hermitian-edge-trace-norm-clique-k5-margin`, `||C_{U_t}||_1 >= 7.0857`. Hence

```text
|| C ||_1  >=  (11/5) 7.0857  =  15.58854  >  9 sqrt3  =  15.58846 ,
```

since `15.58854^2 = 243.0026 > 243`. ∎

This also fills the one gap in `hermitian-edge-trace-norm-odd-antihole-facets-by-size`, which
requires this claim for `n = 11`.
