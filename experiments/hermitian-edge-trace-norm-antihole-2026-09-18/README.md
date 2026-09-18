# Odd antiholes: ||C||_1 >= sqrt3 (n-2) on the complement of C_n (lane w7-078, 2026-09-18)

Supports `research/hermitian-edge-trace-norm-odd-antihole-facets-by-size.md` (route) and
`research/hermitian-edge-trace-norm-odd-antihole-c11.md` (the open case n = 11).
Every run is single-threaded (`OMP_NUM_THREADS=1`), in python3 with numpy, scipy, cvxpy (Clarabel) and mpmath.

| file | what | proof status |
|---|---|---|
| `graphbb.py` | exact SDP branch-and-bound lower bound for `min ||C||_1` on any graph (generalises `../hermitian-edge-trace-norm-clique-small-m-2026-09-18/cliquebb.py`) | rigorous |
| `house_c7bar.log` | `python3 graphbb.py AH7:0,1,2,3,4 6.1859 3.1 3`: house `>= 6.1859` (n = 7) | certificate |
| `k4_c9bar.log` | `python3 graphbb.py K4 5.3887 2.7 3`: `c_4 >= 5.3887` (n = 9) | certificate |
| `cert_ah.py` | float LP that finds a kernel certificate on `Z_n x disc` | search only |
| `K_n13_D4.json` | output of `python3 cert_ah.py 13 4 0.003 0.002 K_n13_D4.json` (LP value 19.20962) | data |
| `verify_ah.py` | rigorous check of a kernel certificate (rational rounding, interval DFT, interval branch-and-bound on the disc) | rigorous |
| `verify_K_n13_D4.log`, `K_n13_D4_exact.json` | `python3 verify_ah.py K_n13_D4.json`: `c(C̄_13) >= 19.2096 > 11 sqrt3` | certificate |
| `cert_circ.py` | the same LP on any circulant graph (webs): `python3 cert_circ.py n D eta eps EDGES alpha out.json` | search only |
| `tail_check.py`, `tail_check.log` | exact check that clique covering + the energy LP give every n >= 15 | exact |
| `k5hilane.sh` | driver for `c_5 >= 7.0857` (n = 11): `./k5hilane.sh 16 <slice> ...`, resumable | running |
| `k5hi_n16_s<i>.log` | per-slice logs of `k5hilane.sh`; so far slice 7 prints `ALL CLOSED` (59042 boxes, 2765 s) | partial certificate |

Running times on one core, under load: house 2 s, `K_4` 39 s, `verify_ah.py` 82 s (it reproduces the log exactly), and
the `c_5 >= 7.0857` computation about 45 min per slice (twice the boxes of the `6.928` run).

## graphbb.py

`python3 graphbb.py GRAPH TARGET T n0 [a_lo a_hi [checkpoint.pkl]]`. `GRAPH` is `K<m>`, or
`AH<n>:<v1>,...` for the subgraph of `C̄_n` induced on the listed vertices. The scheme:
- a BFS spanning tree is gauged real;
- moduli above `T` are closed by 2x2 compression (`2T >= TARGET` is asserted);
- otherwise the SDP dual at the box centre, rounded to Gaussian rationals and checked exactly to
  satisfy `-I < Z < I`, gives the edge-separable bound `tr(ZC)`, which is minimised over the box with
  outward rounding.

For `K5` the edge order matches `cliquebb.py` (star at vertex 0 first), so the symmetry reduction of
`research/hermitian-edge-trace-norm-clique-inequality-k5.md` (first free phase in `[0, pi/2]`) applies
to the slices of `k5hilane.sh`.

## verify_ah.py

The kernel is `K(s,z) = sum_{p<=q<=D} w_pq f_pq(s) Re(z^p conj(z)^q)`. The script checks:
- (K1) every circulant `[f_pq(s(i,j))]`, `(p,q) != (0,0)`, is PSD (interval DFT; `f_pq(0)` is
  raised if needed);
- (K2) `K(1,z) < 0` on the closed unit disc;
- (K3) `K(s,z) < 2 y_s/|1-z|` for `s = 2..k`.

(K2) and (K3) are checked by interval branch-and-bound in polar boxes, widened outward by `1e-12`
relative plus `1e-14` absolute. The bound `n beta` is computed exactly and compared with
`sqrt3 (n-2)` by squaring. The proof that (K1)–(K3) imply `||C||_1 >= n beta` is Step 3 of the route.
