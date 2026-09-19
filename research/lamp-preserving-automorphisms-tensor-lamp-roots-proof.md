---
rg: 2
id: lamp-preserving-automorphisms-tensor-lamp-roots-proof
kind: route
title: Profinite density sends finite-orbit lamps to finite-orbit lamps, and a dimension count makes the finite-orbit site algebra beta-stable
target: lamp-preserving-automorphisms-never-compress-tensor-lamp-roots
requires:
  - automorphic-compressions-have-no-approximable-hilbert-hotel
---

Notation is as in the target. For `F subset X` write `M_F` for the tensors supported in `F`, so
`B_(Y) = M_Y`. For a group `D` acting on `X`, let `X_fin(D)` be the union of the finite `D`-orbits.

**Imported (Lemma+).** This is Step 2 of `automorphic-compression-orbit-rigidity-proof`, the route of
the required claim. Verbatim: "Let `W subset X` be finite and `A`-invariant. Then `W` is
`Gamma_0`-invariant, and `A` and `Gamma_0` induce the same permutation group on `W`." Its hypothesis is
(PE). By Step 1 of the same route, (PE) holds whenever `Gamma` is finitely generated,
`alpha in Aut(Gamma)` and `alpha(Gamma_0) <= Gamma_0`, and here `X = Gamma/H` has `H` a Chabauty limit
of finite-index subgroups.

## Step 0: standard facts about restricted tensor products

These are the facts used in Step 4 of the imported route.

- (F1) Each `b in B` has a least finite support `supp(b)`, with `b in M_(supp(b))`, and
  `M_F meet M_(F') = M_(F meet F')`.
- (F2) `supp(gamma . b) = gamma supp(b)`.
- (F3) Let `b in M_F` with `F` finite, and suppose `b` commutes with `M_E` for some `E subset X`. Then
  `b in M_(F \ E)`. Indeed `M_F = M_(F meet E) tensor M_(F \ E)` is a tensor product of central simple
  `k`-algebras, and the centralizer of the first factor is the second.
- (F4) `gamma` acts on `M_W` for a finite `gamma`-invariant `W` only through the permutation it induces
  on `W`.

## Step 1: finite orbits of elements

For a group `D` acting on `X`, and `b in B`: `D . b` is finite exactly when `supp(b) subset X_fin(D)`.

- (If) `supp(b)` lies in a finite `D`-invariant set `W`. Then `D . b` lies in `M_W`, where `D` acts
  through the finite group `Sym(W)`, by (F4).
- (Only if) Suppose `y in supp(b)` has an infinite `D`-orbit. By (F2), `gamma y in supp(gamma . b)` for
  all `gamma`. If `D . b` were finite, the finitely many finite supports `supp(gamma . b)` would cover
  `D y`, a contradiction.

## Step 2: `X_fin(A) = X_fin(Gamma_0)`

- A finite `Gamma_0`-orbit is a finite `A`-invariant set, hence a union of finite `A`-orbits.
- A finite `A`-orbit is finite and `A`-invariant, so it is `Gamma_0`-invariant by Lemma+, and it lies in
  `X_fin(Gamma_0)`.

Write `X_fin` for this set.

## Step 3: `beta` preserves finite-orbit elements

Apply `psi` to `u_gamma b u_gamma^(-1) = gamma . b`. This gives
`beta(gamma . b) = alpha(gamma) . beta(b)`. So `A . beta(b) = beta(Gamma_0 . b)`.

Hence if `Gamma_0 . b` is finite, then `A . beta(b)` is finite. By Step 1 (for `D = A`) and Step 2,
`supp(beta(b)) subset X_fin`. By Step 1 again (for `D = Gamma_0`), `Gamma_0 . beta(b)` is finite.

## Step 4: the finite-orbit site algebra is `beta`-stable

1. *`R_0 meet B = B_(Y_0)`.*
   - `S = sum_(gamma in Gamma_0) B_(Y_0) u_gamma` is a subring, because `gamma . B_(Y_0) = B_(Y_0)` for
     `gamma in Gamma_0`.
   - `S` contains the generators of `R_0`, so `R_0 <= S`.
   - Conversely, `R_0` contains `u_gamma M_d(k)_(p) u_gamma^(-1) = M_d(k)_(gamma p)`, so it contains
     `B_(Y_0)` and every `u_gamma`. Hence `R_0 = S`.
   - `R` is a free left `B`-module on the `u_gamma`. Comparing coefficients at `u_1` gives
     `R_0 meet B = B_(Y_0)`.
2. *`Y_f` is finite.* `Y_0 = union_(p in P) Gamma_0 p` has at most `|P|` orbits. So
   `Y_f = Y_0 meet X_fin` is a union of at most `|P|` finite orbits.
3. *Inclusion.* Let `b in B_(Y_f)`. Its `Gamma_0`-orbit lies in `B_(Y_f)` and is finite, by (F4).
   - `beta(b) in psi(R_0) meet B <= R_0 meet B = B_(Y_0)`, so `supp(beta(b)) subset Y_0`.
   - By Step 3, `supp(beta(b)) subset X_fin`.
   - Hence `supp(beta(b)) subset Y_f`, and `beta(B_(Y_f)) <= B_(Y_f)`.
4. *Equality.* `psi(k 1) = k 1`, so `psi` restricts to a field automorphism `sigma` of `k`. Then `beta`
   is `sigma`-semilinear and injective.
   - The image of a `k`-subspace is a `k`-subspace, since `sigma` is onto.
   - `beta` carries `k`-independent sets to `k`-independent sets.
   - So `beta(B_(Y_f))` is a subspace of `B_(Y_f)` of the same finite dimension `d^(2|Y_f|)`. Hence
     `beta(B_(Y_f)) = B_(Y_f)`.

## Step 5: `psi(z)` commutes with `B_(Y_0)`

`psi(z) = beta(z)`, since `z in B`.

- *Support in `X_fin`.* `z` commutes with `u_delta` for `delta in Gamma_0`, so `delta . z = z`. The
  orbit `Gamma_0 . z = {z}` is finite, so by Step 3 `Z'' := supp(beta(z))` lies in `X_fin`.
- *Commutation with `B_(Y_f)`.* `z` commutes with `B_(Y_f) <= R_0`. So `beta(z)` commutes with
  `beta(B_(Y_f)) = B_(Y_f)` (Step 4).
- *Support off `Y_0`.* `Z'' meet Y_0 subset X_fin meet Y_0 = Y_f`. By (F3) with `F = Z''` and
  `E = Y_f`, `beta(z) in M_(Z'' \ Y_f)`, and `Z'' \ Y_f` is disjoint from `Y_0`.
- *Conclusion.* `M_(Z'' \ Y_f)` commutes with `M_(Y_0) = B_(Y_0)`.

## Step 6: `psi(z)` commutes with `u_gamma`, for `gamma in Gamma_0`

- For `delta in Gamma_0`, `alpha(delta) . beta(z) = beta(delta . z) = beta(z)` (Step 3). So `beta(z)`
  is `A`-fixed, and by (F2) its support `Z''` is `A`-invariant and finite.
- By Lemma+, `Z''` is `Gamma_0`-invariant, and `A` and `Gamma_0` induce the same permutation group on
  `Z''`.
- For `gamma in Gamma_0`, pick `a in A` inducing the same permutation of `Z''`. By (F4),
  `gamma . beta(z) = a . beta(z) = beta(z)`. So `u_gamma` commutes with `psi(z)`.

## Step 7: conclusion

`R_0` is generated by `B_(Y_0)` and the `u_gamma^(+-1)`, for `gamma in Gamma_0`. By Steps 5 and 6,
`psi(z)` centralizes `R_0`. So `psi(z) p psi(z)^(-1) - p = 0` for every `p in R_0`, and `I = 0`.

**Where the hypotheses enter.**

- `psi(u_gamma) = u_(alpha(gamma))` is used only through the intertwining identity of Step 3. That
  identity is used in Steps 3 and 6.
- `psi(B) = B` is used in Step 4.3, to place `beta(b)` in `B`.
- `z in B` is used in Step 5.
- The full site algebras in `R_0` are used in Step 4.1.

Replacing `psi(u_gamma)` by `w_gamma u_(alpha(gamma))` with a lamp cocycle `w` breaks the
intertwining. It becomes `beta(gamma . b) = Ad(w_gamma)(alpha(gamma) . beta(b))`, and Step 3 fails. ∎
