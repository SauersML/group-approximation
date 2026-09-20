---
rg: 2
id: thompson-t-near-central-pairs-have-golden-defect-gap
kind: claim
title: Near-central exact pairs for T have Lochak--Schneps defect at least (sqrt5-1)/2 - o(1), and this constant is sharp
distinct_from:
  thompson-t-has-full-mf-radical: that is the uniform gap over all exact pairs; this proves the gap only on the sector where J = A^2 nearly commutes with B, with the sharp constant (sqrt5-1)/2 there, so it is one half of a decomposition of that target.
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that turns the target into a gap for exact Z/4 * Z/3 pairs; this proves that gap on the near-central sector and finds its exact value there.
  thompson-t-pentagon-winding-rigidity: that asks for an integer winding invariant to vanish on all small-defect pairs; this is a norm lower bound on one sector, and it says nothing about winding.
  finite-group-corona-tail-exactification: that is the general lifting lemma for finite groups; this applies it to the quotient 2I = SL(2,5) of Delta(4,3,5) cut out by [a^2, b], and adds the exact defect table of 2I.
artifacts:
  - experiments/thompson-t-triangle-rep-census-2026-09-17/two_i_table.py
  - experiments/thompson-t-triangle-rep-census-2026-09-17/two_i_table.out
  - experiments/thompson-t-triangle-rep-census-2026-09-17/eta_table.py
  - experiments/thompson-t-triangle-rep-census-2026-09-17/eta_table.out
---

**ESTABLISHED** by `thompson-t-near-central-golden-defect-gap-proof` (written proof plus an exact finite
check).

## Setting

Use the notation of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`:

```text
G0 = Z/4 * Z/3 = < a, b | a^4, b^3 >,   X = bab,  J = a^2,
r_1 = [X, JXJ],   r_2 = [X, J b^2 J X J b J],   r_P = (ba)^5.
```

An exact pair is `(A, B)` in `U(n)^2` with `A^4 = B^3 = 1`. Put

```text
D_12(A,B) = max( ||r_1(A,B) - 1||, ||r_2(A,B) - 1|| ),
c(A,B)    = max( ||[A^2, B] - 1||, ||r_P(A,B) - 1|| )        (the near-centrality defect).
```

Let `m = (sqrt 5 - 1)/2 = 2 sin(pi/10) = 0.6180...`.

## Statement

1. **(Near-central gap.)** For every `delta > 0` there is `eta > 0` such that, in every dimension `n`,
   every exact pair `(A, B) != (1, 1)` with `c(A,B) < eta` has `D_12(A,B) > m - delta`.
2. **(Sharpness.)** The constant `m` cannot be increased. There is an honest representation
   `rho_2 : Delta(4,3,5) -> SU(2)` with `c(rho_2) = 0` and `D_12(rho_2) = m` exactly.
3. **(The finite model.)** `G = < a, b | a^4, b^3, (ba)^5, [a^2, b] >` is the binary icosahedral group
   `2I = SL(2,5)` of order 120. In `G`, `r_1 = 1` and `r_2 = [bab, ab^2]`. Over the 9 irreducible
   representations of `G`, `D_12` takes the values in the table below. The minimum over nontrivial ones is
   `m`, and only `rho_2` attains it.

| irrep of G | dim | D_12 |
|---|---|---|
| trivial | 1 | 0 |
| rho_2 = Sym^1 | 2 | 2 sin(pi/10) = 0.6180 |
| Sym^2 rho_2 | 3 | 2 sin(pi/5) = 1.1756 |
| Sym^3 rho_2 | 4 | 2 sin(3pi/10) = 1.6180 |
| Sym^4 rho_2 | 5 | 2 sin(2pi/5) = 1.9021 |
| Sym^5 rho_2 | 6 | 2 |
| rho_2' (Galois twin) | 2 | 1.6180 |
| Sym^2 rho_2' | 3 | 1.9021 |
| rho_2 (x) rho_2' | 4 | 1.9021 |

4. **(Consequence for the target.)** `thompson-t-has-full-mf-radical` is equivalent to the far-sector
   statement
   > (FC) for every `eta > 0` there is `epsilon > 0` such that every exact pair with
   > `D(A,B) < epsilon` has `||[A^2, B] - 1|| < eta`.

   Here `D = max(D_12, ||r_P - 1||)` is the defect of the criterion. So a refutation of the target is a
   sequence of nontrivial pairs with `D -> 0` along which `J = A^2` stays **uniformly non-central**: in
   the end, `||[A^2, B] - 1|| >= eta(m/2)`. Every candidate built near a representation of 2I,
   or near any pair in which `A^2` almost commutes with `B`, is excluded, and it is excluded with room
   `m`, not merely a small positive number.

## Remarks

- Item 4 only needs a positive gap on the near-central sector. Qualitatively, uniform simplicity of `T`
  also gives that. The new content is the sharp value `m` and its location. This value explains the whole
  low end of the honest `Delta(4,3,5)` census recorded in the Attempts of `thompson-t-has-full-mf-radical`.
  Every census minimizer with `D_12 < 0.65` (`n <= 6`) has `||[A^2, B] - 1|| <= 0.43` and lies
  within `0.03` of `m`; see `eta_table.out`.
- `eta` comes from a compactness (corona) argument, so it is not explicit. An explicit `eta` would follow
  from Kazhdan's operator-norm stability for finite groups, applied to the Cayley table of 2I. This has
  not been carried out.
- There is no conflict with `delta_1 = 2 sin(pi/12) = 0.5176 < m`. The one-dimensional pairs attaining
  `delta_1` have `||r_P - 1|| >= 0.5176`, so they lie outside the near-central sector once
  `eta < 0.5176`. Item 1 bounds `D_12` on that sector only; it does not bound the criterion's `D`
  globally.
