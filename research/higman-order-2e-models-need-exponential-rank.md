---
rg: 2
id: higman-order-2e-models-need-exponential-rank
kind: claim
title: In any quotient of H4(3) where a has order divisible by 2^e, the orders of d, c, b are divisible by 2^(e-2), 2^(e-4), 2^(e-6), and every linear representation over any field in which a keeps order 2^e has degree at least 2^(e-2); so no fixed-rank family models ord(a) = 2^e for all e, and the smallest monolithic models of Gammabar_e found for e = 3, 4 have faithful degree 2^e and 2^(e+1)
distinct_from:
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that leaves open whether H4(3)/<<[a,c]^2>> has generators of infinite order; this does not settle that, and only bounds the shape of any finite family that would.
  higman-a-has-order-2e-in-gamma-3-2e-mod-r-for-e-le-10: that certifies ord(a) = 2^e in Gammabar_e for e <= 10 by 2-quotient computation; this proves lower bounds on the orders, linear degree and size of every such quotient, and records small monolithic models for e <= 5.
  non-free-higman-edge-images-contain-bs1n-subgroups: that excludes p-adic analytic images and hosts of subexponential orbit growth qualitatively; this gives the finite-level bound 2^(e-2) on linear degree in every characteristic, including characteristic 2.
artifacts:
  - experiments/higman-monolithic-models-2026-09-18/pqgap.sh
  - experiments/higman-monolithic-models-2026-09-18/p3.g
  - experiments/higman-monolithic-models-2026-09-18/p4.g
  - experiments/higman-monolithic-models-2026-09-18/p5.g
  - experiments/higman-monolithic-models-2026-09-18/mono2.g
  - experiments/higman-monolithic-models-2026-09-18/run2.g
  - experiments/higman-monolithic-models-2026-09-18/run2-output.txt
  - experiments/higman-monolithic-models-2026-09-18/mono3.g
  - experiments/higman-monolithic-models-2026-09-18/perm.g
  - experiments/higman-monolithic-models-2026-09-18/run3.g
  - experiments/higman-monolithic-models-2026-09-18/run3-output.txt
  - experiments/higman-monolithic-models-2026-09-18/run4.g
  - experiments/higman-monolithic-models-2026-09-18/run4-output.txt
  - experiments/higman-monolithic-models-2026-09-18/run5.g
  - experiments/higman-monolithic-models-2026-09-18/run5-output.txt
  - experiments/higman-monolithic-models-2026-09-18/run6.g
  - experiments/higman-monolithic-models-2026-09-18/run6-output.txt
---

**ESTABLISHED** (proposed) by `higman-order-2e-models-need-exponential-rank-proof`.

**Setting.** `H4(3) = < a, b, c, d | b^a = b^3, c^b = c^3, d^c = d^3, a^d = a^3 >` with
`x^y = y^-1 x y`, `R = [a,c]^2`, `Gammabar_e = H4(3)/<<a^m, b^m, c^m, d^m, R>>` with `m = 2^e`.
A *model of level e* is a finite quotient of `Gammabar_e` in which `a^(2^(e-1)) != 1`, so `a` has
order exactly `2^e`. The w15 lane certified models of level `e` for every `e <= 10`. The brief asks
for a uniform family of models, one for every `e`.

**Statement.** Let `Q` be any quotient of `H4(3)` (no `R` needed), and let `e >= 3`.
1. **Order ladder.** If `y^x = y^3` in a group and `2^f` divides `ord(y)` with `f >= 2`, then
   `2^(f-2)` divides `ord(x)` (read "divides" as true when the order is infinite). So if `2^e`
   divides `ord(a)` in `Q`, then `2^(e-2) | ord(d)`, `2^(e-4) | ord(c)` and `2^(e-6) | ord(b)`, as far
   as the exponents are at least 2. In a model of level `e`, the log2 order profile of `(a, b, c, d)`
   is at least `(e, e-6, e-4, e-2)` coordinatewise.
2. **Linear degree.** Let `K` be any field and `rho : Q -> GL_n(K)` a representation in which
   `rho(a)` has finite order divisible by `2^e`. Then `n >= 2^(e-2)`. If `char K = 2`, then even
   `n >= 2^(e-1) + 1`.
3. **Size.** Every model of level `e` has order at least `2^(2e-2)`, because
   `<a, d> >= <a> ⋊ <d>` with `d` inducing `x -> x^3` of order `2^(e-2)` on `<a>`. It also has a
   complex irreducible character of degree at least `2^(e-2)`.
4. **No fixed-rank family.** No sequence of models of unbounded level lies in `GL_n(K_i)` for a fixed
   `n`, over any fields `K_i` of any characteristics, or in `GL_n(Z/p^j)` with `p` odd. Families of
   finite images of one compact p-adic analytic group are excluded too, qualitatively, by the w10
   dead end (the generators are torsion there). So a uniform family must have linear degree at least
   `2^(e-2)` at level `e`, for example subgroups of iterated wreath products `C_2 wr ... wr C_2`.
   The step of the brief can succeed only through a wreath or Sylow-type family.
5. **Computed models** (GAP 4 on ANUPQ exports; randomized, so these are upper bounds on minimal
   models). Start from the class-`k` 2-quotient `P` of `Gammabar_e`: `(e, k, log2|P|) = (3, 3, 19)`,
   `(4, 4, 32)` and `(5, 7, 137)`. Then kill random hyperplanes of `Omega_1(Z(Q))` that avoid
   `a^(2^(e-1))` until the socle is cyclic. The result is a monolithic model with socle
   `<a^(2^(e-1))>`, which carries a faithful irreducible character.

   | e | smallest log2 order found | faithful irreducible degree | lower bound (item 2) | core-free permutation degree found |
   |---|---|---|---|---|
   | 3 | 8 | 8 = 2^e | 2 | 32 |
   | 4 | 12 (`run2`) | 32 = 2^(e+1) at log2 order 14 | 4 | 256 |
   | 5 | 50 | not computed | 8 | at most 2^42 (greedy) |

   The order profiles found are balanced, mostly `(e, e, e, e)`, and every
   coordinate is within 2 of `e`. The extreme profile `(e, e-6, e-4, e-2)` of item 1 is never approached. In a transitive faithful action of a
   monolithic model, `a` acts semiregularly with all cycles of length `2^e`, because the socle
   element `a^(2^(e-1))` is central and lies in no point stabilizer. The cycle types in
   `run4-output.txt` show exactly this.

**What it kills and what it leaves.**
- Every candidate for the uniform family made of matrix groups of bounded degree over fields is
  dead, in every characteristic including 2.
- The faithful degree found is `8` at `e = 3` and `32` at `e = 4`, well above the lower bound
  `2^(e-2)`. The smallest model grows from `2^8` to `2^12` to at most `2^50`. This is
  consistent with a wreath-type family `W_(k(e))` whose depth `k(e)` grows at least like `e`.
- Open: find the depth function `k(e)` and a recursion `Q_(e+1) -> Q_e wr C_2` (or into
  `W_(k(e+1))`). One way is to embed the `e = 3, 4` models into `W_5` and `W_8` and read off the
  sections of `a, b, c, d`. That would be a self-similar model, with sections longer than the
  length-2 recursions that w11 excluded.
