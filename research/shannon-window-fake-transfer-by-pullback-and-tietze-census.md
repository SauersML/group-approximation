---
rg: 2
id: shannon-window-fake-transfer-by-pullback-and-tietze-census
kind: route
title: Pull feasible polymatroids back along the letter map, then read a two-letter torsion relator off each fake's canonical host
target: shannon-window-fakes-transfer-to-canonical-hosts
requires: []
artifacts:
  - research/artifacts/shannon-fakes-canonical-host-transfer-2026-09-17.md
  - experiments/shannon-canonical-hosts-2026-09-17/host_tietze.py
  - experiments/shannon-canonical-hosts-2026-09-17/recheck_forced_torsion.py
  - experiments/shannon-canonical-hosts-2026-09-17/recheck_all.txt
---
The steps below refer to Sections 2 and 3 of the artifact.

1. **Transfer (item 1), Lemma 1.**
   - `pi` is injective on `F_H E_H ∪ {1}`. This forces injectivity on `E_H` as well, since `fe` and `fe'` are
     distinct points of the window. So `Pi(x_g) = x_{pi g}`, `Pi(y_f) = y_{pi f}` is a bijection of ground sets.
   - Let `h` be feasible for `G`. Then `h o Pi` is a polymatroid. It satisfies (I), because `Pi` maps `x`'s to
     `x`'s. It satisfies (D), because `Pi` maps the window of `y_f` onto the window of `y_{pi f}`.
   - For (T): if `S` and `tS` lie in the ground set of `H`, then `Pi(tS) = pi(t) Pi(S)`, since `pi` is a
     homomorphism. So `h(Pi tS) = h(Pi S)`.
   - The objective is carried to the objective.

   Every `G`-feasible point therefore gives an `H`-feasible point with the same value. For the particular case,
   the letter map `H_P -> K` of a realization `K` is such a `pi` (Corollary 2).
2. **Refutation criterion (item 2), Corollary 3.**
   - Let `(E,F)` be a fake in `G` whose canonical host `H_P` is torsion-free.
   - Step 1 applies to the letter map `H_P -> G`, which is injective on the window because `G` realizes `P`. It
     gives `LP_{H_P}(E_P, F_P) <= LP_G(E,F) < 1`.
   - So the torsion-free group `H_P` carries a configuration with `LP < 1`, and
     `torsion-free-windows-have-minimal-shannon-certificates` fails.
3. **Realization independence (item 3), Lemma 4.**
   - Tietze moves preserve `H_P`. So a relator `u^k` gives `rho(u)^k = 1` for the letter map `rho` into any
     realization.
   - `rho(u) != 1` because realizations keep the products `fe != 1`, keep distinct readers distinct, and keep
     distinct offsets distinct (the last because `F` is nonempty).
4. **Census.**
   - `recheck_forced_torsion.py` rebuilds `H_P` for each of the 151 configurations and runs the elimination.
     Elimination is exact word manipulation in free groups with no floating point. The order of elimination is
     reshuffled on up to 300 retries.
   - It checks the two-letter form of `u` and `k >= 2`, and prints each certificate as a `CERT` line in
     `recheck_all.txt`. The final count line reads `151` of `151`.
   - Artifact Section 3.2 does the `Z/3` case by hand.

**What this route does not give.** Suppose a fake's pattern is realized in some torsion-free group `K`, but
`H_P` has torsion. Step 1 bounds `LP_{H_P}`, not `LP_K`, so no refutation follows. Ruling out this case for all
fakes is exactly `fake-incidence-patterns-force-torsion` (OPEN). It is not claimed here.
