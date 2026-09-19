---
rg: 2
id: bs12-sharp-pair-dyadic-scale-ladder
kind: claim
artifacts:
  - experiments/bs12-twistfree-base-census-2026-09-17/ladder_check.py
  - experiments/bs12-twistfree-base-census-2026-09-17/ladder_check_out.txt
  - experiments/bs12-twistfree-base-census-2026-09-17/census_tf.py
  - experiments/bs12-twistfree-base-census-2026-09-17/out_N27_M27_s01.txt
  - experiments/bs12-twistfree-base-census-2026-09-17/out_N27_M25_s01.txt
  - experiments/bs12-twistfree-base-census-2026-09-17/out_N27_M23_s01.txt
title: The sharp BS(1,2) test pair has distance to exact pairs invariant, up to 4 pi s R/N, under the dyadic ladder D -> D^R; equivariant mu_3-colourings give twists on every base with an even squaring orbit; bases of order prime to 3 are far in census
distinct_from:
  bs12-twisted-clock-exact-pair-census: that measures d(s,N) over exact pairs with base spectrum the N-th roots of unity; this proves an exact gauge reduction of the test family and measures a different base class, of order M prime to 3.
  bs12-sharp-pair-twist-coherent-corrections-are-bounded-below: that proves the twist inequality for a given twist u; this shows which bases carry twists at all (the colouring twists) and which do not.
  bs12-trivially-padded-opnorm-correction: that is the open statement (TPC, equivalent to ESS Q3); this is a reduction plus a census on its sharp test family and does not settle it.
---

**ESTABLISHED (items 1 and 2: complete elementary proofs below; item 3 is a
floating-point census of explicit exact pairs, and those numbers are upper
bounds for their base class, not lower bounds).**

Notation (as in `bs12-twisted-clock-exact-pair-census`):
- `N` is odd and `w = e^(2 pi i/N)`.
- `D e_j = w^j e_j`, `W e_j = e_(j/2 mod N)`, `V e_j = e_(j+1)`.
- `H_R = V^R + V^(-R)` and `A_s = W e^(i s H_1)`.
- `d(s,N)` is the operator-norm distance
  `inf max(||C - A_s||, ||Z - D||)` over unitaries `C, Z` in `U(N)` with
  `C Z C^* = Z^2`.

## 1. Dyadic scale ladder

For `K >= 0`, let `R = 2^K` and let `d_R(s,N)` be the same distance for the
pair `(W e^(i s H_R), D)`. Then:

```text
|d(s,N) - d_R(s,N)| <= 4 pi s (R-1)/N,
d_R(s,N) = dist((A_s, D^R), exact pairs).
```

So the distance of the sharp pair from exact pairs is the same, up to
`O(sR/N)`, as the distance of `(A_s, D^R)` for every dyadic `R` much smaller
than `N/s`.

*Proof.*

1. **Conjugating by W.** Since `W^* e_k = e_(2k)`, we have
   `W^* V W e_j = e_(j+2)`, so `W^* V W = V^2`. Hence `W^* f(V) W = f(V^2)`
   for every function `f`.
2. **The gauge.** Put `Y = -s sum_{k<K} H_(2^k)` and `h = e^(iY)`. All
   functions of `V` commute, so
   ```text
   h^* A_s h = W (W^* e^(-iY) W) e^(i s H_1) e^(iY)
             = W exp(i(-Y(V^2) + s H_1 + Y(V))),
   ```
   and the exponent telescopes:
   `s sum_{k<K} H_(2^(k+1)) + s H_1 - s sum_{k<K} H_(2^k) = s H_(2^K)`.
   Therefore `h^* A_s h = W e^(i s H_R)` exactly.
3. **The base moves little.** `D V D^* = w V`, so `D h D^* = e^(i Y(wV))`. In
   the joint eigenbasis of `V`, `Y` is multiplication by
   `y(t) = -2s sum_{k<K} cos(2^k t)`, and `sup|y'| <= 2s (2^K - 1)`. So
   ```text
   ||h^* D h - D|| = ||D h D^* - h|| <= ||Y(wV) - Y(V)|| <= (2 pi/N) 2s (R-1).
   ```
4. **Comparing the two distances.** Conjugation by `h` maps exact pairs to
   exact pairs and preserves operator-norm distances. So an exact pair
   `(C,Z)` near `(A_s,D)` gives the exact pair `(h^*Ch, h^*Zh)`, with
   `||h^*Ch - We^(isH_R)|| = ||C - A_s||` and
   `||h^*Zh - D|| <= ||Z - D|| + 4 pi s (R-1)/N`. The reverse direction is
   the same.
5. **The second identity.** Let `sigma_R e_j = e_(Rj mod N)`, which is
   unitary because `N` is odd. It commutes with `W`, satisfies
   `sigma_R^* V^R sigma_R = V`, and satisfies `sigma_R^* D sigma_R = D^R`.
   ∎

*Why this is not a first-order remark.* The telescoping gauge is the
truncated Livsic solution of `-Y(V^2) + Y(V) = -s H_1`. Its full series
diverges: the doubling map has the fixed point `t = 0`, where every term
equals `-2s`. So the gauge exists only for `R << N/s`, and the ladder cannot
remove the twist. `ladder_check.py` confirms the exact identity to 1e-15
and the base bound for `N = 27, 81`, `s = 0.1, 0.5` and `R <= 16`
(`ladder_check_out.txt`; the `N = 243` rows were cut off by a 10-minute
timeout).

## 2. Colouring twists

Let `C Z C^* = Z^2` be exact in `U(n)`.
- The spectrum `S` of `Z` satisfies `S = S^2`, so squaring permutes the
  finite set `S`.
- A *colouring* is a map `f: S -> mu_3` with `f(lambda^2) = f(lambda)^2`.

For every colouring `f`, the unitary `u = f(Z)` satisfies

```text
u^3 = 1,   C u C^* = f(Z^2) = f(Z)^2 = u^2,
```

so `u` is a twist in the sense of
`bs12-sharp-pair-twist-coherent-corrections-are-bounded-below`.

On a squaring orbit of length `L`, a colouring that is not identically `1`
exists if and only if `2^L = 1 (mod 3)`, that is, if and only if `L` is even.
(Going once round the orbit gives `f = f^(2^L)`.)

Hence:
- `u = Z^(N/3)` is just the colouring `lambda -> lambda^(N/3)` when
  `Z^N = 1`.
- A base spectrum `{e^(2 pi i k/M)}` with `3` not dividing `M` still carries
  twists whenever some `ord_d(2)` is even for `d | M`. Examples:
  - `M = 25`: the orbit lengths are `1, 4, 20`.
  - `M = 5`, `M = 11`, `M = 13`, and others.
- Bases with only odd orbit lengths carry no colouring twist. Examples are
  `M = 7` (length `3`), `M = 23` (length `11`), `M = 31`, `47`, `73`. They
  are the genuinely twist-free order-`M` bases.

## 3. Census over order-M bases (computation)

The exact pairs are
```text
Z = U Z0 U^*,   C = U C0 Theta U^*,
```
where:
- `Z0` has spectrum `Z/M` together with `N - M` extra eigenvalues `1`;
- `C0` is the square-root permutation;
- `Theta` lies in the commutant of `Z0`;
- `U` is arbitrary.

These are all exact pairs with that spectrum (`census_tf.py`). The runs use
`N = 27`, `s = 0.1`, 4 restarts (identity, dense noise, and a banded
position blur), 150 L-BFGS iterations per stage and a Schatten-`p` surrogate.
They report true operator norms.

| M | 3 divides M | colouring twists | best max distance |
|---|---|---|---|
| 27 (control) | yes | yes | 0.1471 (the w14 census has 0.147) |
| 25 | no | yes (even orbits) | 0.6641 |
| 23 | no | none | 0.7948 |

The relation error and the unitarity error are at most 4e-14.

Two constraints explain the gap:
- **Spectrum.** Bhatia--Davis matching for unitaries only forces
  `||Z - D|| >= 0.232`.
- **Dynamics.** `(Z/N, x2)` has cycle type `1,2,6,18`, whereas
  `(Z/25 + 2 fixed points, x2)` has cycle type `1,1,1,4,20`. So no aligned
  permutation start exists, and a permutation mismatch costs at least
  `sqrt 2` at a fixed base.

In this census, the order-prime-to-3 bases are 4.5 to 5.4 times farther than
the order-`N` class. So the best exact corrections of the sharp pair keep an
order-`N` base, and they escape the twist bound only by being
twist-incoherent (`kappa > 0`). They do not escape it by removing the twist.
