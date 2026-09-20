---
rg: 2
id: mod-s2-bielliptic-centralizer-has-rational-h2-proof
kind: route
title: Build the invariant curves on the branched double cover of a torus, restrict to the J-eigenlattices, and pair with the SL_2(F_2)-invariant form on H_1(Gamma(2))
target: mod-s2-bielliptic-centralizer-has-rational-h2
requires:
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
artifacts:
  - experiments/mod-s2-bielliptic-sector-2026-09-17/check.py
---

The prerequisite is used only for the facts that `psi : M -> Sp_4(Z)` is a homomorphism and that `M` acts on
`H_1(S_2;Z)` preserving the intersection form `<,>`. Every integer identity below is checked by `check.py`
(`python3 check.py`, which prints `ALL CHECKS PASSED`).

## Step 1. The surface, the involution and a basis

- **The torus and the cut.** Let `E = R^2/Z^2`, `p = (1/2, 1/4)` and `q = (1/2, 3/4)`. Let `gamma` be the segment
  `x = 1/2, 1/4 <= y <= 3/4`.
- **The double cover.** Take two copies `E_1`, `E_2` of `E` cut open along `gamma`. Glue each side of the cut in `E_1`
  to the opposite side in `E_2`. The result `S` is the double cover of `E` branched at `p` and `q`. A closed curve in
  `E - {p, q}` lifts to a closed curve iff it crosses `gamma` an even number of times.
- **It is `S_2`.** `S` is closed and oriented, with the orientation pulled back from `E`. Its Euler characteristic is
  `2·0 - 2 = -2`, so it has genus 2.
- **The involution.** The deck transformation `g` exchanges the sheets and fixes exactly `p~`, `q~`. It preserves
  orientation, because it covers the identity away from the branch points.
- **The basis curves.** Let `alpha = {y = 1/10}` and `beta = {x = 1/5}`. Both miss `gamma`, so each lifts to two
  disjoint curves, one per sheet. Call them `a_1, a_2` and `b_1, b_2`, with `g(a_1) = a_2` and `g(b_1) = b_2` as
  oriented curves.
- **They form a symplectic basis.** `a_i` meets `b_i` once, transversally, and meets nothing else in the list. So
  the intersection matrix of `(a_1, b_1, a_2, b_2)` is the standard symplectic one. It is unimodular. The sublattice
  they span has rank 4 inside the unimodular lattice `H_1(S_2;Z)`, so its index `n` satisfies `n^2 = 1`. They are a
  symplectic basis, and `J := psi(g)` swaps `a_1 <-> a_2` and `b_1 <-> b_2`.
- **`g` has order 2 in `M`.** `J != I`, so `g` is nontrivial.

## Step 2. The invariant curves (claim item 1)

**The curve `c`.** Let `c` be the preimage of `alpha' = {y = 2/5}`.
- `alpha'` meets `x = 1/2` only at `y = 2/5`, which lies in `gamma`. So `alpha'` crosses the cut once, and `c` is
  one connected simple closed curve that double covers `alpha'`. Since `g c = c`, `T_c` commutes with `g`.
- `g|_c` is the nontrivial deck map of `c -> alpha'`. So `g` preserves the orientation of `c` pulled back from
  `alpha'`.
- `c` misses `a_1` and `a_2`, since the lines `y = 2/5` and `y = 1/10` are disjoint.
- `beta` meets `alpha'` once. The two preimages of that point lie one on `b_1` and one on `b_2`. `g` preserves
  orientation and carries `(c, b_1)` to `(c, b_2)` with orientations, so the two local signs agree:
  `<c, b_1> = <c, b_2> = ±1`.
- Pairing against the unimodular basis gives `[c] = ±(a_1 + a_2)`. It is nonzero, so `c` is nonseparating.

**The curve `c'`.** Let `c'` be the preimage of the arc `gamma' = {x = 1/2, 3/4 <= y <= 5/4}`, which runs from `q`
to `p` through `y = 0`.
- `gamma'` is embedded and meets the branch set only at its endpoints. So `c'` is the union of its two lifts, glued
  at `p~` and `q~`. It is a simple closed curve with `g c' = c'`.
- `g|_{c'}` swaps the two lifts and fixes their endpoints, so it *reverses* the orientation of `c'`.
- `c'` misses `b_1` and `b_2`, since `x = 1/2` and `x = 1/5` are disjoint.
- `alpha` meets `gamma'` once, at `(1/2, 1/10)`. The two preimages lie one on `a_1` and one on `a_2`. `g` carries
  `(a_1, c')` to `(a_2, -c')`, so `<c', a_1> = -<c', a_2> = ±1`.
- This gives `[c'] = ±(b_1 - b_2)`, which is nonzero.

**Disjointness.** `alpha' ∩ gamma' = ∅`, because `y = 2/5` is not in `[3/4, 5/4] mod 1`. So `c ∩ c' = ∅`.

**Twists.** Take an annular neighbourhood `N` of `c`, disjoint from `c'`.
- `T_c` is supported in `N`, and `T_c'` in an annulus disjoint from `N`, so they commute.
- For orientation-preserving `f`, `f T_c f^{-1}` is the twist in `f(N)` with the same handedness, i.e. `T_{f(c)}`.
  So `g T_c g^{-1} = T_c` and `g T_c' g^{-1} = T_c'`.
- **Action on `H_1`.** A transverse curve `x` crossing `c` at points with signs `s_j` is carried to a curve homologous
  to `x + (sum_j s_j) c`. So, for one fixed sign `eta = ±1` depending only on conventions,
  `psi(T_c) x = x + eta <x, c> c`. Both claims below hold for either sign.

## Step 3. Restriction to the eigenlattices

Put:
- `e = a_1 + a_2` and `f = b_1 + b_2`, a basis of `L+ = ker(J - 1)`;
- `e' = a_1 - a_2` and `f' = b_1 - b_2`, a basis of `L- = ker(J + 1)`.

`L+` and `L-` are primitive of rank 2, `<e, f> = <e', f'> = 2`, and `L+ ⊥ L-`.

**The map `Phi`.** Every `A` in `Z_{Sp_4(Z)}(J)` preserves `L+` and `L-`. Let `X` and `Y` be its matrices on
`(e, f)` and `(e', f')`.
- `A` preserves `<,>` on `L+`, which is twice the standard form, so `det X = 1`. Likewise `det Y = 1`.
- `e ≡ e'` and `f ≡ f'` mod `2 Z^4`, and `e, f` are independent mod 2. So `A e ≡ A e'` forces `X ≡ Y` mod 2.
- Hence `Phi : A -> (X, Y)` is a homomorphism from `Z_{Sp_4(Z)}(J)` to
  `G_Delta = {(X,Y) in SL_2(Z)^2 : X ≡ Y mod 2}`.

**The images of the twists.** In the convention of `check.py`:
- `Phi psi(T_c) = (A^{-1}, I)` with `A = [[1,2],[0,1]]`. The `L+` block is `f -> f + 2 eta' e`, and the `L-` block is
  trivial because `<e', c> = <f', c> = 0`.
- `Phi psi(T_c') = (I, B)` with `B = [[1,0],[2,1]]`.
- With the opposite sign convention, these become `(A, I)` and `(I, B^{-1})`.

## Step 4. `H_2(G_Delta;Q)` and the torus (claim items 2 and 3)

**The finite-index subgroup.** `H = Gamma(2) x Gamma(2)` is normal of finite index in `G_Delta`.
- `G_Delta/H` is the diagonal copy of `SL_2(Z)/Gamma(2) = SL_2(F_2)`.
- `Gamma(2) = {±I} x F(A, B)` (Sanov). So `H_1(Gamma(2);Q) = Q[A] + Q[B]` and `H_2(Gamma(2);Q) = 0`.
- By Künneth, `H_2(H;Q) = H_1(Gamma(2);Q) ⊗ H_1(Gamma(2);Q)`.
- With rational coefficients and a finite quotient, Hochschild–Serre gives `H_2(G_Delta;Q) = H_2(H;Q)_{G_Delta/H}`.
  Conjugation by `Gamma(2)` acts trivially on `H_1(Gamma(2))`, so the action is the diagonal action of
  `SL_2(Z)/Gamma(2)`.

**The invariant form.** `check.py` computes the action of `S = [[0,-1],[1,0]]` and `T = [[1,1],[0,1]]` on `H_1`, via
Sanov reduction of `S X S^{-1}` and `T X T^{-1}`:

```text
S: [A] -> -[B], [B] -> -[A]          T: [A] -> [A], [B] -> [A] - [B].
```

The bilinear form `b = [[2,1],[1,2]]` in the basis `([A], [B])` is invariant under both. Since `S` and `T` generate
`SL_2(Z)`, `b` is `SL_2(F_2)`-invariant. So `v ⊗ w -> b(v, w)` factors through the coinvariants, and it is a linear
functional on `H_2(G_Delta;Q)`.

**Evaluation on the torus.** The torus class maps to `[A^{-1}] ⊗ [B]` (or `[A] ⊗ [B^{-1}]`). Then
`b = -b([A],[B]) = -1 != 0` (`check.py` prints the value `+1` for its choice of `b = -[[2,1],[1,2]]`).

So `(Phi psi iota)_*[Z^2] != 0` in `H_2(G_Delta;Q)`. Hence:
- `psi_* iota_*[Z^2] != 0` in `H_2(Z_{Sp_4(Z)}(J);Q)` (item 3);
- `iota_*[Z^2] != 0` in `H_2(Z_M(g);Q)` (item 2), since `psi` maps `Z_M(g)` into `Z_{Sp_4(Z)}(J)`.

By universal coefficients over `Q`, `H^2 = Hom(H_2, Q)` contains a class taking the value `1` on the torus. QED.
