---
rg: 2
id: sl2-laurent-torsion-quotients-and-cohn-norms-are-blind-proof
kind: route
title: "Unit entries are elementary, lift along nilpotents, split by CRT, and use Laurent units to force degrees and norms to collapse"
target: sl2-laurent-torsion-quotients-and-cohn-norms-are-blind
requires: []
---

Throughout, `S` is a commutative ring, and
`E_12(r) = [[1,r],[0,1]]`, `E_21(r) = [[1,0],[r,1]]`, `D(u) = diag(u,u^{-1})`.
Also `R = Z[t,t^{-1}]`.

## Lemma 1 (a unit entry makes a matrix elementary)

Let `g = [[a,b],[c,d]] in SL_2(S)` have some entry that is a unit. Then
`g in E_2(S)`.

*Proof.*
- **Diagonal units.** For a unit `u`, put `w(u) = E_12(u) E_21(-u^{-1}) E_12(u)`.
  Then `w(u) = [[0,u],[-u^{-1},0]]` and `w(u) w(1)^{-1} = D(u)`. So
  `D(u) in E_2(S)`, and `w(1)^{±1} in E_2(S)`.
- **`a` a unit.** `E_21(-c a^{-1}) g = [[a,b],[0,d']]`, and `d' = a^{-1}` by the
  determinant. Since `D(a) E_12(a^{-1} b) = [[a,b],[0,a^{-1}]]`, we get
  `g = E_21(c a^{-1}) D(a) E_12(a^{-1} b) in E_2(S)`.
- **`c` a unit.** `E_12((1-a) c^{-1}) g` has `(1,1)` entry
  `a + (1-a) = 1`, a unit, so it is elementary by the previous case, and hence
  so is `g`.
- **`b` or `d` a unit.** `g · w(1)^{-1} = [[b,-a],[d,-c]]` has that unit in its
  first column, so the previous two cases apply. ∎

## Lemma 2 (finite products)

If `S = S_1 x S_2`, then `SL_2(S) = E_2(S)` iff `SL_2(S_i) = E_2(S_i)` for
`i = 1, 2`.

*Proof.* `SL_2(S) = SL_2(S_1) x SL_2(S_2)` coordinatewise. Also
`E_ij((r_1,r_2)) = (E_ij(r_1), E_ij(r_2))` and `(E_ij(r_1), I) = E_ij((r_1,0))`,
so `E_2(S) = E_2(S_1) x E_2(S_2)`. ∎

## Lemma 3 (lifting along a nil ideal)

Let `N` be an ideal of `S` consisting of nilpotent elements. If
`SL_2(S/N) = E_2(S/N)`, then `SL_2(S) = E_2(S)`.

*Proof.* Let `g in SL_2(S)`. Its image is a product of elementary matrices
`E_{i_k j_k}(\bar r_k)`. Lift each `\bar r_k` to `r_k in S` and let
`h = Π_k E_{i_k j_k}(r_k) in E_2(S)`. Then `g h^{-1} ≡ I mod N`, so its `(1,1)`
entry is `1 + ν` with `ν` nilpotent. That entry is a unit, so `g h^{-1}` is
elementary by Lemma 1, and so `g in E_2(S)`. ∎

## Lemma 4 (quotients of `k[t,t^{-1}]` for a field `k`)

For every ideal `I` of `k[t,t^{-1}]`, `SL_2(k[t,t^{-1}]/I) = E_2(k[t,t^{-1}]/I)`.

*Proof.*
- **`I != 0`.** `I = (f)` with `f = t^m f_0`, `f_0 in k[t]`, `f_0(0) != 0`, and
  `k[t,t^{-1}]/I ≅ k[t]/(f_0)` because `t` is invertible modulo `f_0`. This is a
  finite-dimensional `k`-algebra, hence Artinian, hence a finite product of local
  rings. In a local ring with maximal ideal `m`, the first column `(a,c)` of an
  `SL_2` matrix cannot lie in `m` (else `ad - bc in m`). So some entry is a unit,
  and Lemma 1 applies. Lemma 2 handles the product.
- **`I = 0`.**
  - *Width.* Write `w(f) = (top degree) - (bottom degree)` for `f != 0`.
  - *Division.* If `f, g != 0`, there is `q` with `f - qg = 0` or
    `w(f - qg) < w(g)`. To see this, write `g = t^m g_0` and `f = t^n f_0` with
    `f_0, g_0 in k[t]` and `g_0(0) != 0`, so `deg g_0 = w(g)`. Divide:
    `f_0 = q_0 g_0 + r_0` with `deg r_0 < deg g_0`. Then
    `f - t^{n-m} q_0 g = t^n r_0`, which is `0` or has width
    `<= deg r_0 < w(g)`.
  - *Reduction.* Let `g = [[a,b],[c,d]] in SL_2(k[t,t^{-1}])`. If `a = 0` or
    `c = 0`, the other entry of the first column is a unit (determinant), and
    Lemma 1 applies. Otherwise, if `w(a) >= w(c)`, left multiplication by
    `E_12(-q)` replaces `a` by `a - qc`, which is `0` or of smaller width. If
    instead `w(c) > w(a)`, `E_21(-q)` does the same to `c`. The sum `w(a) + w(c)`
    strictly drops at each step unless an entry becomes `0`, so the process
    stops at a first column containing `0`. ∎

## Theorem (C)

Let `J` be an ideal of `R` containing an integer `n >= 1`, and `S = R/J`. Then
`SL_2(S) = E_2(S)`.

*Proof.*
1. **Split by CRT.** Write `n = Π_i p_i^{e_i}`. By the Chinese remainder theorem
   `Z/n ≅ Π_i Z/p_i^{e_i}`, so `R/nR ≅ Π_i (Z/p_i^{e_i})[t,t^{-1}]`. `S` is a
   quotient of `R/nR`, and every ideal of a finite product of rings is a product
   of ideals. So `S ≅ Π_i S_i`, with `S_i` a quotient of
   `(Z/p_i^{e_i})[t,t^{-1}]`. By Lemma 2 it suffices to treat one `S_i`.
2. **Reduce mod `p`.** In `S_i`, `p = p_i` satisfies `p^{e_i} = 0`, so `N = p S_i` is
   a nilpotent ideal. `S_i / N` is a quotient of `F_p[t,t^{-1}]`, so
   `SL_2(S_i/N) = E_2(S_i/N)` by Lemma 4. Lemma 3 gives
   `SL_2(S_i) = E_2(S_i)`. ∎

## Consequences 1–3 of (C)

1. **Surjectivity.** The reduction map sends `E_12(r)` to `E_12(\bar r)`, and
   every `\bar r` lifts. So `E_2(R) -> E_2(S) = SL_2(S)` is onto. For `A in G`,
   choose `e in E_2(R)` with the same image. Then `e^{-1} A in SL_2(R,J)`, which
   gives `G = E_2(R) SL_2(R,J)`, and `A ≡ e mod J`.
2. **Rows.** A row `(a,b)` with `ad - bc = 1` is the first row of `A`. Then
   `A e^{-1} ≡ I mod J`, so column operations `e^{-1}` take `(a,b)` to `(1,0)`
   modulo `J`.
3. **Subgroups.** If `E_2(R) <= H` and `SL_2(R,J) <= H`, then
   `H >= E_2(R) SL_2(R,J) = G`. If `R/J` is finite, its additive order `n`
   kills `1`, so `n in J`. A homomorphism `φ` killing `E_2(R)` and
   `SL_2(R,J)` kills `G` by the same identity. ∎

## Theorem (D)

Let `d` be as in the statement. Then `d = 0`.

*Proof.*
1. **Units.** `d(1) = d(1·1) = 2 d(1)`, so `d(1) = 0`. For a unit `u`,
   `d(u) + d(u^{-1}) = d(1) = 0` with both terms `>= 0`, so `d(u) = 0`. This
   applies to every `±t^k`.
2. **Sums.** Every nonzero `x in R` is a finite sum `x = Σ_{j=1}^m ε_j t^{k_j}`
   with `ε_j = ±1`, repetitions allowed. Induct on `m`. For `m = 1` this is
   step 1. For `m > 1`, write `x = y + z` with `z = ε_m t^{k_m}` and `y` the sum
   of the first `m-1` terms. If `y = 0`, then `x = z` and `d(x) = 0`. Otherwise
   `d(x) <= max(d(y), d(z)) = 0` by induction. So `d(x) = 0`. ∎

## Theorem (N)

No discrete norm exists on `R`.

*Proof.* Suppose `|.|` exists.
1. **Units.** `|1| = |1|^2` and `|1| >= 1` give `|1| = 1`. Also
   `|t^2| |t^{-2}| = 1` with both factors `>= 1`, so `|t^2| = 1`. Likewise
   `|-1|^2 = |1| = 1`, so `|-t^2| = 1`.
2. **`1 ± t` are non-units.** The units of `R` are `±t^k`, since `R` is a domain
   and the product of the top-degree terms, and of the bottom-degree terms, of `u`
   and `u^{-1}` is `±1`. Neither `1 + t` nor `1 - t` is a monomial, so both are
   nonzero non-units, and `|1 + t|, |1 - t| >= 2`.
3. **Contradiction.** `|1 - t^2| = |1+t| |1-t| >= 4`, but subadditivity gives
   `|1 - t^2| <= |1| + |-t^2| = 2`. ∎

## The failing candidates

- **Top degree.** It is additive and ultrametric but `deg(t^{-1}) = -1 < 0`.
  This is where Theorem (D) needs nonnegativity.
- **Width.** It fails the ultrametric inequality at `1 + t`.

In both cases the Laurent unit `t` is where the obstruction comes from. That is
consistent with Cohn's matrix `[[1+2t,4],[-t^2,1-2t]]`: it is non-elementary
over `Z[t]`, where top degree is a genuine degree function with `R_0 = Z`, and
elementary over `R`, because its entry `-t^2` is a unit (Lemma 1).
