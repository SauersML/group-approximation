---
rg: 2
id: bilateral-lift-at-coordinate-projection-proof
kind: route
title: Read a class-bijective lift along the coordinate projection as a fibre-map cocycle, and use the null-coset lemma to force every fibre map into the mirror group modulo the tail full group
target: bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift
requires:
  - jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group
---

Notation as in the target. Throughout, "a.e." refers to `mu` on `X`, to `mu_+-` on `X_+-`, or to the left counting
measure `nu` on `R_n` (`nu(C) = ∫ |C_x| dmu_+(x)`).

The imported facts, from `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`:
* **(MQ1)** `GL_n(J) = EL_n(J)`.
* **(MQ3)** `P -> E_+` is onto with kernel `L_-`. So for every `h in E_+` there is `h' in E_-` with the same symbol,
  and `ker(pi_-) = L_-`.

## Step 0. Operators on the dual spaces

* Every `j in J` acts on `F_2^N` (all sequences), through the transpose of its action on finitely supported vectors.
  `S` and `T` go to `T` and `S`.
* So every `h in M_n(J)` acts on `X_+ = (F_2^N)^n` by a matrix of the same kind: a finite-band Toeplitz matrix plus a
  finite matrix. This matrix maps `V_fin^+` into itself.
* The Laurent part `sigma` is the symbol of this matrix, i.e. its class modulo finite matrices, read in the bilateral
  index.
* The kernel of `sigma` on these matrices is exactly the finite matrices, i.e. those with finitely many nonzero
  entries. This is the ideal `M_n(<Q>)`, `Q = 1 - ST`.
* The same holds on `X_-` in the mirror basis.

For `(w, g) in G`, write the dual of `g` in block form with respect to `X = X_- x X_+`:

```text
(w,g).(x_-, x_+) = ( C_g x_- + B'_g x_+ + w_- ,  A_g x_+ + B_g x_- + w_+ ).          (0.1)
```

* `g` is a Laurent matrix of finite band. So `B_g` and `B'_g` are finite matrices: they couple only coordinates
  within band distance of the wall `0 | -1`. In particular each has finite image, contained in `V_fin`.
* `A_g` and `C_g` are finite-band Toeplitz matrices (compressions) with `sigma(A_g) = sigma(C_g) =: g^vee`, the dual
  Laurent matrix.
* `g -> g^vee` is an automorphism of `SL_n(A)`. Below we identify `Q` with its image.

## Step 1. The null-coset lemma

**Lemma 1.** Let `M` be a finite-band Toeplitz-plus-finite matrix on `X_+` (or on `X_-`) with `sigma(M) != 0`, and let
`F` be a countable subset of `X_+`. Then `mu_+{x : Mx in F}` is `0`.

*Proof.*
* `M` is a continuous endomorphism of the compact group `X_+`. Each set `M^(-1)(v)` is empty or a coset of the
  closed subgroup `ker M`. So it suffices to show that `mu_+(ker M) = 0`.
* Suppose not. A closed subgroup of positive Haar measure is open, so `ker M` contains a basic neighbourhood
  `U_k = {x : x_(j,i) = 0 for j < k}`.
* Now take the bilateral Laurent part `a = sigma(M) != 0`. Choose a column `i` of `a` that is nonzero. Choose `m >= k`
  larger than the band width plus the size of the finite correction.
* The delta sequence `e_(m,i)` lies in `U_k`. At that distance from the wall, `M` acts on it as the Laurent matrix
  `a`. So `M e_(m,i)` is the translate of column `i` of `a`, which is nonzero.
* This contradicts `e_(m,i) in ker M`. The same argument works on `X_-`. `□`

**Corollary 1.1 (symbol cocycle).**
* Take `M, M' in Ê_+` with `sigma(M) != sigma(M')`. Applying Lemma 1 to `M - M'` with `F = {0}` gives
  `mu_+{x : Mx = M'x} = 0`.
* `Ê_+` is countable. So off a null invariant set, `s(x, y) = sigma(M)` for `y = Mx` does not depend on the choice of
  `M`.
* `s` is a Borel cocycle `R_n -> Q`, since `sigma` is multiplicative.

**Corollary 1.2 (the mirror extension).**
* `Ê_-` maps `V_fin^-` into itself, in both directions. So it preserves `T_-` and normalizes `[T_-]`, and
  `N_- = Ê_- [T_-]` is a group.
* Take `f in Ê_- ∩ [T_-]`. Then `(f - 1)x in V_fin^-` for a.e. `x`, and `V_fin^-` is countable. Lemma 1 forces
  `sigma(f - 1) = 0`, i.e. `sigma(f) = 1`.
* So `f in ker(pi_-) = L_-` (MQ3). Conversely `L_-` acts by finite matrices, which move each point by a finitely
  supported vector, so `L_- <= [T_-]`.
* Hence `pi_-(f t) := sigma(f)` is a well-defined homomorphism `N_- -> Q`, with kernel `L_- [T_-] = [T_-]`. It is
  onto by (MQ3).

## Step 2. (ML) implies (BL_n at pr_+)

Let `beta : R_n -> N_-` be a measurable cocycle with `pi_- o beta = s`. Put

```text
S = { ((x_-, x_+), (beta(x_+, y_+) x_-, y_+)) : (x_+, y_+) in R_n }.                  (2.1)
```

**`S` is an equivalence relation, off a null set, and `pr_+` is class-bijective.**
* The cocycle identity and `beta(x,x) = 1` give transitivity and reflexivity. Symmetry holds because
  `beta(y,x) = beta(x,y)^(-1)`.
* Over each `y_+ in [x_+]` there is exactly one point of the class, so `pr_+` is a bijection of classes.
* All of this holds for a.e. point: countably many identities between elements of `Aut(X_-, mu_-)`, each holding
  a.e. Fubini applies.

**`S <= R'` (off a null set).** Fix `(x_+, y_+) in R_n` and `M in Ê_+` with `Mx_+ = y_+`.
* Write `beta(x_+, y_+) = f t`, with `f in Ê_-`, `t in [T_-]`, and `sigma(f) = s(x_+, y_+) = sigma(M) =: q`.
* Choose `g in SL_n(A)` with `g^vee = q`. By Step 0, `sigma(A_g) = sigma(M)` and `sigma(C_g) = sigma(f)`.
* So `M - A_g` and `f - C_g` are finite matrices and have images in `V_fin`.
* Hence

```text
y_+ - A_g x_+ - B_g x_-  = (M - A_g) x_+ - B_g x_-                 in V_fin^+,
f t x_- - C_g x_- - B'_g x_+ = f(t x_- - x_-) + (f - C_g) x_- - B'_g x_+   in V_fin^-,
```

  using `t x_- - x_- in V_fin^-` and `f V_fin^- <= V_fin^-`.
* So `(beta x_-, y_+) = (w, g).(x_-, x_+)` for the finitely supported `w` given by these two differences. That point
  is in the `R'`-class of `(x_-, x_+)`.

**Borel and measure.**
* `S` is Borel, being the image of a Borel map on a standard Borel space with countable-to-one fibres (Lusin--Novikov).
* `S` is a subrelation of the p.m.p. relation `R'`, so `mu` is `S`-invariant.
* `pr_+` pushes `mu` to `mu_+`.

This is `(BL_n)` with `N = n` and `r = pr_+`.

## Step 3. (BL_n at pr_+) implies (ML)

Let `S <= R'` be Borel, with `pr_+` class-bijective onto `R_n` off an `S`-invariant null set `Z`.

**3a. Fibre maps.**
* For `(x_-, x_+) notin Z` and `y_+ in [x_+]_(R_n)`, let `Phi_(x_+, y_+)(x_-)` be the `X_-`-coordinate of the unique
  point of `[(x_-, x_+)]_S` lying over `y_+`.
* The map `((x_-, x_+), y_+) -> Phi` is Borel. Its graph is `S` read in coordinates, and Lusin--Novikov applies.
* By uniqueness and transitivity of `S`:

```text
Phi_(y,z) o Phi_(x,y) = Phi_(x,z),      Phi_(x,x) = id,      Phi_(y,x) o Phi_(x,y) = id.     (3.1)
```

  Each of these holds a.e. on `X_-` for `nu`-a.e. `(x,y)`, by Fubini applied to `Z`.
* So each `Phi_(x,y)` is a Borel bijection of a conull subset of `X_-`.

**3b. The fibre maps preserve `mu_-`.**
* Let `phi : U -> V` be a Borel partial isomorphism whose graph lies in `R_n`. Put
  `Theta(x_-, x_+) = (Phi_(x_+, phi x_+)(x_-), phi x_+)` on `X_- x U`.
* `Theta` is a Borel injection whose graph lies in `S <= R'`. A partial Borel injection whose graph lies in a p.m.p.
  relation preserves the measure, so `Theta_* (mu|_(X_- x U)) = mu|_(X_- x V)`.
* Disintegrate over `X_+`:
  * the left side is `∫_U (Phi_(x, phi x))_* mu_- ⊗ delta_(phi x) dmu_+(x)`;
  * the right side is `∫_V mu_- ⊗ delta_y dmu_+(y)`;
  * `phi` preserves `mu_+`.
* Uniqueness of disintegration then gives `(Phi_(x, phi x))_* mu_- = mu_-` for `mu_+`-a.e. `x in U`.
* By Feldman--Moore, `R_n` is covered by the graphs of countably many such `phi`. So `Phi_(x,y) in Aut(X_-, mu_-)`
  for `nu`-a.e. `(x,y)`, and `beta := Phi` is a measurable cocycle `R_n -> Aut(X_-, mu_-)` by (3.1).

**3c. The linear part is forced to be the symbol.**
* Enumerate `G = {gamma_1, gamma_2, ...}`, `gamma = (w, g)`, and enumerate `Ê_+`.
* For each triple `(gamma, M)`, consider

```text
Z_(gamma, M) = { x_+ : (A_g - M) x_+ in w_+ + B_g X_- }.
```

  `B_g X_-` is finite, since `B_g` is a finite matrix. If `sigma(A_g) != sigma(M)`, then `Z_(gamma, M)` is
  `mu_+`-null by Lemma 1.
* Let `Z_+` be the `R_n`-saturation of the union of these null sets. It is null, since `R_n` is countable and p.m.p.
* Take `x_+ notin Z_+`, `y_+ = M x_+`, and a point `x_-` for which the pair `(x_-, x_+), (Phi x_-, y_+)` is
  `S`-related. Then `S <= R'` gives some `gamma = (w,g)` with `gamma.(x_-, x_+) = (Phi x_-, y_+)`.
* Reading the `+` coordinate in (0.1) gives `(A_g - M) x_+ = w_+ + B_g x_-`, so `x_+ in Z_(gamma, M)`. As
  `x_+ notin Z_+`, this forces `g^vee = sigma(A_g) = sigma(M) = s(x_+, y_+)`.

So, off a null set, **every** group element that realizes an `S`-edge over `(x_+, y_+)` has linear part equal to the
symbol `q = s(x_+, y_+)`, whatever `x_-` is.

**3d. Fibre maps lie in `N_-`.**
* Fix `(x_+, y_+)` as above and `q = s(x_+, y_+)`. Let `P_gamma` be the Borel set of `x_-` for which `gamma` is
  the first element in the enumeration realizing the `S`-edge.
* The sets `P_gamma` partition a conull subset of `X_-`, and on each of them `g^vee = q` by 3c. So, by (0.1),

```text
Phi_(x_+, y_+)(x_-) = C_g x_- + B'_g x_+ + w_-            for x_- in P_gamma.
```

* By (MQ3) and Step 0 fix `f_q in Ê_-` with `sigma(f_q) = q`. Then `C_g - f_q` is a finite matrix. So on every
  `P_gamma`, and hence a.e.,

```text
Phi(x_-) - f_q x_- = (C_g - f_q) x_- + B'_g x_+ + w_-  in V_fin^-.
```

* Put `t = f_q^(-1) o Phi`. It lies in `Aut(X_-, mu_-)` by 3b, and `t x_- - x_- = f_q^(-1)(Phi x_- - f_q x_-)` lies in
  `V_fin^-`. So the graph of `t` lies in `T_-` and `t in [T_-]`.
* Hence `beta(x_+, y_+) := Phi_(x_+, y_+) = f_q t in N_-`, with `pi_-(beta) = q = s(x_+, y_+)` (Corollary 1.2).
  By 3b, `beta` is a measurable cocycle.

This is `(ML)`.

**3e. Uniqueness.**
* Feeding this `beta` into (2.1) returns `S`, since both have the same fibre maps.
* Conversely, two cocycles giving the same `S` have the same fibre maps a.e.
* So the correspondence between `S` and `beta` is a bijection between the canonical lifts (modulo null sets) and the
  solutions of `(ML)`. This proves item 2 of the target.

## Step 4. The cohomological form (item 3)

* Let `beta_0 = f_(s(.,.))` be the pointwise lift through a fixed section `q -> f_q`. Every `N_-`-valued map with
  symbol `s` can be written `beta_0 t` with `t = beta_0^(-1) beta` measurable and `[T_-]`-valued, since
  `ker pi_- = [T_-]` by Corollary 1.2.
* So `(ML)` holds iff some `[T_-]`-valued `t` makes `beta_0 t` a cocycle. This is exactly the statement that the
  `L_-`-valued defect of `beta_0` is a nonabelian `[T_-]`-coboundary.

## Step 5. The conditional remark (item 4, not part of the ESTABLISHED statement)

* Suppose `tau : Ê_+ -> Ê_-` is a homomorphism with `sigma o tau = sigma`.
* Then `M -> (M, tau(M))` is an injective homomorphism `E_+ -> P = E_+ x_Q E_-`.
* `P` is LEF by (MQ2) of `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`. So `E` would be LEF.
* The non-LEF lemma for `EL_3(J)`, and hence for `EL_n(J)` with `n >= 3` (it contains `EL_3(J)` as a corner), is
  claimed by swarm-0917-w14-w14-ptl-pull (`jacobson-el3-is-not-lef`, unlanded when this was written). Granting it, no
  such `tau` exists. So no `(ML)` witness of the form `beta(x, Mx) = tau(M)` exists.
* So any witness must use genuinely point-dependent `[T_-]`-corrections. The finitary group `L_-` alone never
  suffices homomorphically.

