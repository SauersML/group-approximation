---
rg: 2
id: window-fakes-on-z4-z5-z7-klein-and-dinf-are-entropic-proof
kind: route
title: Solve the one-bit linear-atom LP on each host window, rationalise the optimal support, and check the direct sum of atom copies exactly
target: window-fakes-on-z4-z5-z7-klein-and-dinf-are-entropic
requires:
  - minimal-window-shannon-derivations-miss-rokhlin-domination
artifacts:
  - experiments/entropic-window-fakes-relaxed-2026-09-17/relaxed_target.py
  - experiments/entropic-window-fakes-relaxed-2026-09-17/atom_gen.c
  - experiments/entropic-window-fakes-relaxed-2026-09-17/atom_bin_lp.py
  - experiments/entropic-window-fakes-relaxed-2026-09-17/exact_support.py
  - experiments/entropic-window-fakes-relaxed-2026-09-17/exact_support_log.txt
  - experiments/entropic-window-fakes-relaxed-2026-09-17/rep_z5.json
  - experiments/entropic-window-fakes-relaxed-2026-09-17/rep_dinf.json
  - experiments/entropic-window-fakes-relaxed-2026-09-17/verify_dinf.log
  - experiments/entropic-window-fakes-2026-09-17/verify_linear.py
---
1. **Reduction to the host.** Every site of `X = FE ∪ {1}` lies in the host subgroup `H`, and so does every
   translation `p q^-1` between sites. Any `t` with `S` and `tS` both nonempty subsets of the window has this form. So
   (I), (D), (T) in `G ⊇ H` are literally the constraints in `H`. The referees of
   `shannon-window-fakes-on-klein-and-infinite-dihedral-hosts` accepted this step. The dihedral case split
   in the claim is elementary.

2. **Atoms.** Fix a host window with `m = |X|` sites and `r = |F|` codewords. An *atom* `a` assigns to each codeword `j` a
   vector `v_j in F_2^X` supported on the read set `fE` (possibly 0). Let `x in F_2^X` be uniform, and put `y_j = <v_j, x>`.
   Its entropy vector is
   `h_a(S) = |S ∩ X| + rank{ v_j restricted to X \ S : y_j in S }` bits.
   (I) and (D) hold for every atom, but (T) need not.

3. **Direct sums.** Let `n_a >= 0` be integers with `D = sum_a n_a`. Take `n_a` independent copies of each atom and
   concatenate them. Then `x_g` is uniform on `F_2^D`, each `y_j` is linear with rows supported on the blocks of `fE`,
   and the joint entropy of any set `S` is `sum_a n_a h_a(S)`, because ranks add over a direct sum of independent
   coordinates. In units of `D` bits the vector is `h = sum_a w_a h_a` with `w_a = n_a / D`. So (I) and (D) hold,
   (T) holds iff `sum_a w_a (h_a(S) - h_a(tS)) = 0` for all translation pairs, and `Phi(h) = sum_a w_a Phi(h_a)`.

4. **Finding and fixing weights.**
   - `relaxed_target.py` writes the read sets, the translation classes of `shannon_lp.build`, and the objective masks.
   - `atom_gen.c` enumerates every atom (`2^(sum_j |fE|)` of them: `4096` for `Z/4`, `Z/5`, Klein; `65536` for `D_inf`, `Z/7`) and writes `Phi(h_a)` and the (T) differences.
   - `atom_bin_lp.py` solves the LP (HiGHS). Its values are `0.79439` (`Z/4`, Klein), `0.8` (`Z/5`), `0.94545` (`D_inf`) and `0.86390` (`Z/7`).
   - `exact_support.py` recomputes the rank vectors of the support atoms in integer arithmetic. It solves the (T) rows and `sum w = 1` by Fraction elimination, with free variables set to rationalised LP weights. It then asserts `w >= 0`, that (T) holds exactly, and computes `Phi` exactly. Output (`exact_support_log.txt`):
     - `Z/4`: 29 atoms, `D = 107`, `Phi = 85/107`;
     - Klein: 29 atoms, `D = 107`, `Phi = 85/107`;
     - `Z/5`: 10 atoms, `D = 10`, `Phi = 4/5`;
     - `D_inf`: 34 atoms, `D = 220`, `Phi = 52/55`;
     - `Z/7`: 110 atoms, `D = 3424`, `Phi = 1479/1712`.

   By step 3, these are exact entropy vectors of `F_2`-linear configurations satisfying (I), (D), (T).

5. **Independent check on the concatenated codes.** `exact_support.py` writes the direct sum as a `verify_linear.py`
   representation (copy `c` of block `g` is bit `g D + c`). The verifier of `torsion-window-fakes-are-realized-by-f2-linear-codes`
   recomputes every rank of the concatenated codes, with no atom structure. It checks (I), the support condition (D),
   and every translation equality, then prints `Phi`:

       cd experiments/entropic-window-fakes-relaxed-2026-09-17
       python3 ../entropic-window-fakes-2026-09-17/verify_linear.py 4 0,1,2,3 0,1,2 rep_z4.json
         -> ground set 7, d=107, 189 translation equalities, rank(y_f)=[85,85,85], Phi = 85/107, ALL EXACT
       python3 ../entropic-window-fakes-2026-09-17/verify_linear.py 5 0,1,2,4 1,2,3 rep_z5.json
         -> ground set 8, d=10, 380 translation equalities, rank(y_f)=[8,8,8], Phi = 4/5, ALL EXACT
       python3 ../entropic-window-fakes-2026-09-17/verify_linear.py k2 '[(0,0),(1,0),(0,1),(1,1)]' '[(0,0),(1,1),(0,1)]' rep_k2a.json
         -> ground set 7, d=107, 189 translation equalities, Phi = 85/107, ALL EXACT
       python3 ../entropic-window-fakes-2026-09-17/verify_linear.py dinf '[(1,0),(-1,0),(-1,1),(1,1)]' '[(-1,1),(1,-1),(1,0),(1,1)]' rep_dinf.json
         -> ground set 12, d=220, 2147 translation equalities, rank(y_f)=[196,196,196,196], Phi = 52/55, ALL EXACT

   All four exit 0 (`verify_*.log`). In `torsion2_scan.py`, `D_inf` elements are `(sign, trans)`, so `(1,0) = 1`,
   `(-1,0) = r0`, `(-1,1) = r1` and `(1,1) = t`. For `Z/7`, step 4 is the certificate; the 44 MB representation was not re-verified.

6. **Hand-checkable `Z/5` certificate.** Sites are `x_0..x_4` (one bit each), and `y_1, y_2, y_3` read `{0,1,2,3}`,
   `{1,2,3,4}` and `{2,3,4,0}`. The ten atoms, each with weight `1/10`, are `(y_1; y_2; y_3)`:

       1: 0; 0; x0                    6: x0+x2+x3; x1+x2+x4; x2+x3
       2: 0; x4; x0+x4                7: x0+x1; x1+x2; x2
       3: x0; 0; 0                    8: x2+x3; x3+x4; x0+x2+x4
       4: x0+x1; x1; 0                9: x2+x3; x1+x3+x4; x0+x2+x3
       5: x0+x1+x3; x1+x2; x2+x3     10: x3; x3+x4; x0+x4

   - `h(y_j) = 8/10` for each `j`, since exactly two atoms have `y_j = 0`.
   - In every atom `x_0` lies in the span of `y_1, y_2, y_3`: `y_1 + y_3` for atoms 6 and 9, `y_1` for atom 3, `y_3` for atom 1, `y_1 + y_2` for atom 4, and `y_1 + y_2 + y_3` for atoms 2, 5, 7, 8 and 10. So `h(x_0 y_F) = h(y_F)`.
   - Hence `Phi = h(y_1) + h(x_0 y_F) - h(y_F) = 4/5`.
   - The 380 translation equalities are the machine check of step 5.

7. **No derivation.** Each vector in steps 4 and 5 is the entropy vector of genuine random variables. It satisfies
   every valid information inequality and the premises (I), (D), (T), and it has `Phi < 1`. So no derivation of `Phi >= 1`
   from those ingredients exists on these windows. By step 1, the same holds in every group containing the host.

8. **Why the true inequality is not contradicted.** On all these hosts `<F F^-1>` is finite or amenable. So a
   genuine configuration has `Phi >= 1` by `bernoulli-window-codeword-folner-ratio-bound`. So the direct sums cannot be
   configurations, i.e. `y_(tf)` is not a translate `psi(x_(tfE))` of one map `psi`. Consistently, the individual atoms
   are visibly not translation invariant: on `Z/5`, atom 3 has `y_1 = x_0 ≠ 0` but `y_2 = 0`. Only the mixture
   satisfies (T), and it does so in entropy, not in law.
