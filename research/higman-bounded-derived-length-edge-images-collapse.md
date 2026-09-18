---
rg: 2
id: higman-bounded-derived-length-edge-images-collapse
kind: claim
title: In a nontrivial quotient of Higman's group no opposite pair generates a virtually solvable group of derived length at most 11, so the normal closure of F^(11) is all of H4
distinct_from:
  higman-derived-length-three-edge-images-collapse: that is the case of derived length 3, with a hand-built three-step chain; this proves a general reduction from derived length k to k - 1 through order-(k-2) tower invariants and certifies them up to k = 11.
  solvable-by-metabelian-edge-images-collapse-higman-quotients: that needs the second derived subgroup of the image to have finite Hirsch length; this has no rank condition at all, only a bound on the derived length.
  higman-b-side-derived-closure-stays-in-bottom-layer: that shows the one-sided closure of F^(k) in G_b meets F inside P^(k-1); this shows the two-sided closure of F^(k) in H4 is everything for k <= 11.
artifacts:
  - experiments/higman-two-sided-ladder-2026-09-18/tower.py
  - experiments/higman-two-sided-ladder-2026-09-18/tower-output.txt
  - experiments/higman-two-sided-ladder-2026-09-18/ladder4.py
  - experiments/higman-two-sided-ladder-2026-09-18/ladder4-output.txt
---

**ESTABLISHED** by `higman-bounded-derived-length-tower-chain-proof`.

**Statement.** Let `Q` be a quotient of
`H4 = < a, b, c, d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2 >` (`x^y = y^-1 x y`), and let
`F = <a,c>`, which is free in `H4`. Let `k <= 11`.

1. **Powers.** If for some `m >= 1` the subgroup `A = <a^m, c^m>` of `Q` satisfies `A^(k) = 1`, then
   `Q = 1`. The same holds for `<b^m, d^m>`.
2. **Normal closure.** The normal closure of `F^(11)` in `H4` is `H4`.
3. **Edge images.** If the image of `<a,c>` or of `<b,d>` in `Q` has a finite-index subgroup that is
   solvable of derived length at most 11, then `Q = 1`.
4. **Trees.** If `Q != 1` acts on a tree without inversions, and every edge stabilizer is virtually
   solvable of derived length at most 11, then `Q` fixes a vertex. So a nontrivial quotient of `H4`
   never splits as an amalgam or HNN extension over such a subgroup.

**Mechanism.** Put `alpha = a^m`, `gamma = c^m`, `P = 2^m` and `N_j = 2^(P^j)`. Conjugation by `b`
raises each letter `gamma` at `alpha`-height `j >= 0` to the power `N_j`, and conjugation by `d` does the
same to `alpha` at `gamma`-height `j`. Take `w_0 in F^(k)`, all of whose `gamma`-letters are at
`alpha`-heights 0 and 1. Conjugate it alternately by `b, gamma^n, d, alpha^n', b, ...`, which is `k`
half-steps in all.

- **Tower invariants.** Each letter of a word gets a nested *type* built from the letters of the other
  kind before it. `S_r` is the signed count of letters by level-`r` type. `S_0` is the exponent count
  by height, which is the image in `P/P'` used for `k = 2`. `S_1` is the count `S` of the `k = 3` proof.
- **One step.** For a word `v` whose `alpha`-letters are at `gamma`-heights `>= 0`,
  `S^b_r(iota_d(v)) = sigma_*(S^d_(r+1)(v))`. Here `sigma` rewrites types by the substitution
  `h -> N_h`. For a large shift, `N_(h+1) >= N_h^2` makes `sigma_*` injective. The `gamma^n` or
  `alpha^n'` conjugation kills a nonzero invariant for at most one `n`.
- **Reduction.** If `S_(k-2)(iota_b(w_0)) != 0`, the chain ends in a word, trivial in `Q`, with
  exponent sums `(0, Y)`, `Y != 0`. The mirror chain gives `(Y', 0)`. Then `<alpha^L, gamma^L> <= A'`
  for `L = lcm(Y, Y')`. This subgroup has derived length `<= k - 1`, so the case `k - 1` applies. The
  base case is `virtually-metabelian-edge-images-collapse-higman-quotients` (`k = 2`).
- **Certification.** `tower.py` computes `S_0, ..., S_(k-2)` of `iota_b(w_0)` for an explicit iterated
  commutator `w_0 in F^(k)`, with `k = 2, ..., 11`. It works in block form, with linear hashing, where a
  nonzero hash certifies a nonzero sum. The runs are exact for `m = 1..4`, and symbolic in
  `M = N_1 = 2^P` for all `m >= 5`. In every case `S_(k-2) != 0`.
- **Consistency.** `S_0, ..., S_(k-3)` come out zero, as descent forces. The hashed values agree with
  an unhashed computation.

**What it kills for Attempt 5.** The glued construction `G_1' *_A G_1'` of `higman-group-is-sofic` now
needs an amenable edge image `A` none of whose finite-index subgroups is solvable of derived length
`<= 11`.

**Open.** The reduction proves `T(k)` for every `k` once, for each `k`, some `w_0 in F^(k)` with
`gamma`-letters at nonnegative `alpha`-heights has `S_(k-2)(iota_b(w_0)) != 0` at every `P = 2^m`.
That would kill every virtually solvable edge image. The certification is empirical in `k`: it covers
`k <= 11` and gives no proof for general `k`.
