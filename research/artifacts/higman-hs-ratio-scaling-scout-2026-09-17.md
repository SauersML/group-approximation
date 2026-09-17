# Higman HS word-ratio scaling scout (2026-09-17)

Lane: `non-hyperlinear-group`, compute-scout. This is a directed search, not
a census, of the marked HS word-stability ratio

```text
ratio(U) = e(g_0) / sum_j e(r_j),  r_j = g_j g_(j+1) g_j^-1 g_(j+1)^-2,  e(v)=||v-1||_2^2 (normalized)
```

over `U(d)^k`, for Higman's four-cycle `H4` (`k=4`, open) and the trivial
three-cycle `H3` (`k=3`, calibration). By
`hyperlinear-radical-has-linear-word-certificate`, `C(4)=sup_d C_d(4)<infinity`
iff `g_0` lies in the hyperlinear radical, which gives a nonhyperlinear
witness. Before this, main had `C(4)>16` (U(3)) and a U(2) upper bound of 2.
No large-dimension or calibrated data existed.

Scripts: `experiments/higman-hs-microstate-scaling-2026-09-17/`. All runs
were single-threaded and at most 20 minutes each.

## 1. Rigorous outputs

| statement | tier | where |
|---|---|---|
| `C(4) > 38` (U(6), exact Q(i)) | exact finite computation | `higman-hs-word-coefficient-exceeds-thirty-eight` |
| `C(3) > 10` for the trivial 3-cycle (U(6), exact Q(i)) | exact finite computation | same |
| On `T3={g_1^3=g_3^3=1}`: `e(g_0) <= 17973 sum e(r_j)`; robustly `e(g_0) <= 25397(sum e(r_j)+e(g_1^3)+e(g_3^3))`, all dimensions, any tracial algebra | complete proof | `higman-order-three-torsion-ratio-bound` |
| For every `m>=1` and generator `g_i`: `e(g_0) <= K_(m,i)(sum e(r_j)+e(g_i^m))`, finite tower-type `K`, any tracial algebra | complete proof | `higman-approximate-torsion-collapses-hs-word-ratio` |

## 2. Data: best ratio found per dimension

Full-unitary Riemannian nonlinear CG (`ratio_search.py`) from Haar starts.
There were 60 restarts per d (`ratio_sweep.jsonl`) and 1000 restarts for
d=4..9 (`many_restarts.jsonl`). The table also includes basin hopping and
direct sums (`run_hop.py`, `hop_a.jsonl`), tensor seeds (`run_tensor.py`),
and the order-q ansatz (`run_orderq.py`: odd generators isospectral to
q-th roots, even generators free).

| d | H4 best | in T3? | H3 best |
|---|---|---|---|
| 2 | 1.819 | – | – |
| 3 | 16.372 | yes (e(g^3)<3e-5) | 4.359 |
| 4 | 36.127 | yes, exact | 4.498 |
| 5 | 36.127 (padded d4) | yes | 5.625 |
| 6 | **38.740** | yes, spectrum 2x{1,w,w-bar} | **10.3217** |
| 7, 8 | 38.739 (order-3 ansatz, mult 2) | yes | 10.3217 (padded) |
| 9 | 27.03 (mult 3) | yes | – |
| 10, 12 | 16.6, 15.5 (60 restarts) | no | 8.65, 9.69 |
| 16 | 23.91 (tensor 4x4 + CG) | yes | ~6 |

Non-T3 local maximizers do exist: 21.93 (d=7), 24.30 (d=8), 19.71 (d=9, best of
1000 Haar restarts), and 21.16
(hop from a padded non-T3 d6 tuple). None exceeds the T3 value 38.74. Basin
hopping from the padded and direct-summed d4 T3 witness (perturbations off
T3 with eps in {0.2, 0.5, 1, 2}) never improved on it. The order-q ansatz for q=5 and q=7 gives
only 9.6 to 13.9.

Growing torsion exponent (`offT3_roots.jsonl`: odd generators isospectral
to all d-th roots of unity, q=d, 12 restarts). This is the one regime the
torsion-collapse theorem leaves open. The ratios are 10.30 (d=9), 10.16 (d=11),
10.41 (d=13) and 7.17 (d=16): flat, at the level of the trivial three-cycle,
with no growth in d.

## 3. Anomalies

1. **Spontaneous torsion.** Unconstrained full-U(d) optimization lands on
   exact order-three odd generators (`e(g_1^3)=e(g_3^3)=0` to machine
   precision at d=4 and d=6). The even generators have conjugation-symmetric
   spectra, not order 7, so the tuple is not a Frobenius F21 packet. The
   inversion relators `r_0,r_2` carry about half the defect of `r_1,r_3`.
   Adding `g_1^3=g_3^3=1` to Hig gives the trivial group (Higman's
   smallest-prime argument), and the torsion theorem makes this quantitative.
   So the best microstate-like tuples are near-representations of a trivial
   group.
2. **Plateau and separation.** Both ratios plateau in d (H4 ≈ 38.7, H3
   ≈ 10.3 for d ≤ 16). The factor ≈ 3.75 between them has the same order as
   the differences in relator count and area, so it is not a hyperlinearity
   signal.
3. **Large-d BS packets are dominated.** Discrete-log Baumslag-Solitar
   packet starts (`init_models.py`, `run_cg.py`, isospectral CG at mark
   ≈ 2) give minimal defects:

   | p | H4 | H3 |
   |---|---|---|
   | 29 | 0.653 | – |
   | 53 | 0.422 | – |
   | 101 | 0.298 | 0.391 |
   | 149 | 0.257 | 0.369 |
   | 197 | 0.233 | 0.358 |

   These are still slowly decreasing at 2500 iterations. The H4 local
   exponent is about 0.37, and H3 is flattening (0.15, then 0.10). At p=197
   the implied ratio is about 8.5, below the d=6 witness. This does rule out
   using p ≤ 197 packet CG as a discriminator: it is dominated by d ≤ 6 T3
   tuples, and its H4/H3 difference is a decay rate, not a separation.
4. **Permutation annealing is blind.** Helfgott-Juschenko exponential
   permutations (`expperm_sa.c`) were annealed at n=1019 with 30000 sweeps.
   The minimal bad fractions were (k,m)=(4,2) 0.409, (3,2) 0.425, (2,2)
   0.492 and (4,3) 0.411. The (4,3) case, which is known to decay eventually,
   does not separate from the trivial cases at this n.

## 4. What is ruled out, precisely

- Coefficients ≤ 38 (Hig) and ≤ 10 (trivial three-cycle).
- Scaling out of `T3`: every family built from the numerical maximizers by
  direct sums, tensor products, padding or ultraproducts stays in `T3`,
  whose ratio is ≤ 17973. So no such family shows `C(4)=infinity`. This
  covers the coefficient-16 and coefficient-38 witnesses and the whole
  order-3 ansatz in every dimension.
- Any sequence with ratio → ∞ must satisfy
  `(e(g_1^3)+e(g_3^3)) / sum_j e(r_j) → ∞`: the odd generators must stay far
  from order three, relative to the defect.

## 5. Conjecture suggested

**Torsion-maximizer conjecture.** For every d, `C_d(4)` is approached by
tuples in `T3`, or more weakly within `e(g_1^3)+e(g_3^3) = O(sum e(r_j))`.
Then `C(4) <= 25397` and Hig is not hyperlinear. The weak form is a single
dimension-free inequality between `e(g_1^3)+e(g_3^3)` and `e(g_0)` on
near-Higman tuples. Evidence: every global best for d ≤ 16 lies in T3, and
non-T3 local maxima are strictly lower. Counter-pressure: non-T3 local maxima
exist (24.3 at d=8), and the search is not exhaustive for d ≥ 7.

Extension, now proved (`higman-approximate-torsion-collapses-hs-word-ratio`):
approximate torsion of any fixed exponent on any single generator already
gives a finite constant. So the weak conjecture can be restated
exponent-free: `C_d(4)` is approached, uniformly in d, by tuples in which some
generator is within `O(sum e(r_j))` of a fixed finite order. What remains
open is exactly the regime of torsion exponents growing with d. The q=d
root-spectrum runs above (ratio ≈ 10, flat) show no growth there.
