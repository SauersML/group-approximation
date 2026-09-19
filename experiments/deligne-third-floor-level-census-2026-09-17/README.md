# mu_(1/3) census on small Sp_4(Z)-sets (2026-09-17 wave, run 2026-09-19)

Target: `research/deligne-schreier-complexes-have-a-uniform-third-cellular-floor.md`.

- `presentation.py`: Sp_4(Z) = Mod(S_2)/<<(t1 t2)^6>> (Birman-Hilden), t_i = symplectic transvections along the
  chain classes. Every relator is checked to be the identity in Sp_4(Z); its Deligne lift exponent `k_r` is the
  winding number of `det u` along the relator path (polar part of the real-symplectic matrix path).
  Output: braid/commutator relators 0, `chain6 = (t1..t5)^6` -3, `iota2` -2, `[iota, t1]` 0, `sep = (t1 t2)^6` -1.
- `gsets.py`: permutation actions on P^3(F_p), Lagrangians of F_p^4, F_p^4 - 0; relators checked to act trivially.
- `defect.py`: exact MILP for mu_theta(X) (HiGHS) plus an independent re-evaluation `defect_of`.
- `heur.py`, `run_heur.py`: smooth local search + LP polishing (integers frozen), re-evaluated by `defect_of`.

Results (theta = 1/3; all upper bounds certified by `defect_of`):

| X | abs X | best upper bound | lower bound |
|---|---|---|---|
| pt | 1 | 1/291 | 1/291 (MILP closed) |
| P^3(F_2) | 15 | 1/291 (Kahler pullback) | 0 (MILP dual, 120 s) |
| Lag(F_2) | 15 | 1/291 (Kahler pullback) | 0 |
| P^3(F_3) | 40 | 1/291 (Kahler pullback) | none |

- The pulled-back point model is a fixed point of LP polishing on every set tried; 10-20 random starts per set
  land at 0.08-0.16, far above 1/291. No non-Kahler improvement was found.
- The MILP's LP relaxation is identically 0 (take a = 0, n_c = -theta k_r real), so branch-and-bound gets no
  pruning; at |X| = 15 it has not moved the dual bound off 0 in 120 s.

Run: `python3 run_small.py pt 1/3 60`, `python3 run_heur.py P3F2,LagF2,P3F3 1/3 10`.
