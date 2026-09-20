---
rg: 2
id: correlated-products-cannot-substitute-rounds-for-alphabet-proof
kind: route
title: Tensor near-optimal sdp+ solutions of the factors on the product probability space -- feasibility is coordinatewise and the objective is a product of [0,1] numbers, so only the marginals of mu matter -- then Theorem 3 at each base and Theorem 8 on the output; the base SDPs, solved to precision eta_Sigma/3l, decide the route
target: correlated-products-cannot-substitute-rounds-for-alphabet
requires:
  - steurer-hellinger-relaxation-rounding
  - steurer-parallel-repeated-unique-games-rounding
  - sdp-fixed-precision-solvable-gls
---

The notation is that of the target claim. (H0), (H1) and (H2) are the forms in
`steurer-hellinger-relaxation-rounding`. `sdp` is the basic SDP in the form of
`steurer-parallel-repeated-unique-games-rounding`.

## Step 1: elementary facts

- **(E1) Values in `[0,1]`.** Take any (H0)-feasible solution `{f_(u,i)}` of a
  unique game `G` and any constraint `e = (u, v, π)`. Put
  `val(e) := Σ_i ⟨f_(u,i), f_(v,π(i))⟩`. Then `0 <= val(e) <= 1`.
  - The lower bound holds because each term is the integral of a product of
    nonnegative functions.
  - For the upper bound, use Cauchy–Schwarz in `L^2`, then in `ℝ^Σ`, and the
    fact that `π` is a bijection:

    ```text
    val(e)  <=  Σ_i ‖f_(u,i)‖ ‖f_(v,π(i))‖  <=  (Σ_i ‖f_(u,i)‖^2)^(1/2) (Σ_i ‖f_(v,π(i))‖^2)^(1/2)  =  1.
    ```

  In the same way, every basic-SDP objective term is at most `1`, so
  `sdp(G) <= 1` and `sdp+(G) <= 1`.
- **(E2) `opt <= sdp`.** Let `σ` be a labelling. Fix a unit vector `z`. Put
  `u_i := z` if `i = σ(u)` and `u_i := 0` otherwise, at every vertex `u`. This
  satisfies `Σ_i ‖u_i‖^2 = 1` and `⟨u_i, u_j⟩ = 0` for `i ≠ j`. Its objective
  term at `(u, v, π)` is `1` if `π(σ(u)) = σ(v)` and `0` otherwise. So the
  objective is the value of `σ`, and `sdp(G) >= opt(G)`.
- **(E3) Product inequality.** For `a_1, ..., a_l in [0,1]`,
  `1 − Π_j a_j <= Σ_j (1 − a_j)`. The proof is by induction. The case `l = 1`
  is an equality. For the step, write `P = Π_(j<l) a_j in [0,1]`. Then
  `1 − P a_l = (1 − P) + P(1 − a_l) <= (1 − P) + (1 − a_l)`.
- **(E4) Marginal density.** Let `φ >= 0` be a function on `E_j`, and let `µ_j`
  have density at most `D_j` with respect to `w_j`. Then
  `E_(e~µ) φ(e_j) = Σ_(e in E_j) µ_j(e) φ(e) <= D_j Σ_e w_j(e) φ(e) = D_j E_(w_j) φ`.

## Step 2: the tensor solution (Theorem CP (a), first inequality)

Fix `δ > 0`. For each `j`, pick an (H0)-feasible solution
`{f^(j)_(u,i)}` of `G_j`, on a probability space `(Ω_j, µ^(j))`, with objective
`>= sdp+(G_j) − δ`. This is possible because (H0) defines `sdp+` as a
supremum. Fix a representative of each function, and read
`supp f := {ω : f(ω) ≠ 0}` for that representative.

Let `(Ω, ν) := Π_j (Ω_j, µ^(j))` be the product probability space. For a
vertex `U = (u_j)_j` of `H` on either side, and a label
`I = (i_j)_j in Σ_1 × ... × Σ_l`, define

```text
F_(U,I)(ω_1, ..., ω_l)  :=  Π_j f^(j)_(u_j, i_j)(ω_j).
```

This is well defined, because every coordinate of a left vertex of `H` is a
left vertex of its factor, and likewise on the right.

- **Nonnegativity.** `F_(U,I)` is a product of nonnegative functions, so it is
  nonnegative.
- **(2.7).** By Tonelli's theorem, for nonnegative functions on a product
  measure, `‖F_(U,I)‖^2 = Π_j ‖f^(j)_(u_j,i_j)‖^2`. Summing over all
  `I = (i_j)` and expanding the product of sums,

  ```text
  Σ_I ‖F_(U,I)‖^2  =  Π_j ( Σ_(i in Σ_j) ‖f^(j)_(u_j,i)‖^2 )  =  Π_j 1  =  1.
  ```

- **(2.8).** Let `I ≠ I'`, and choose `j0` with `i_(j0) ≠ i'_(j0)`. Then
  `supp F_(U,I)` is contained in `{ω : ω_(j0) in supp f^(j0)_(u_(j0), i_(j0))}`,
  and `supp F_(U,I')` is contained in the same set with `i'_(j0)` in place of
  `i_(j0)`. These two sets are disjoint by (2.8) for `G_(j0)` at the vertex
  `u_(j0)`. So `supp F_(U,I) ∩ supp F_(U,I') = ∅`.

So `{F_(U,I)}` is (H0)-feasible for `H` on `(Ω, ν)`. None of this depends on
`µ`.

**Objective at one constraint.** Take a constraint of `H`,
`E = ((u_j), (v_j), Π_j π_j)`, coming from `(e_1, ..., e_l)` with
`e_j = (u_j, v_j, π_j)`. Its label map sends `I = (i_j)` to `(π_j(i_j))_j`.
By Tonelli again, the inner product of product functions factorizes. Summing
over all `I`, the sum of products of nonnegative terms expands:

```text
val_H(E)  =  Σ_I ⟨F_(U,I), F_(V,(π_j(i_j)))⟩  =  Σ_I Π_j ⟨f^(j)_(u_j,i_j), f^(j)_(v_j,π_j(i_j))⟩
          =  Π_j val_j(e_j),
```

where `val_j` is the value (E1) of the chosen solution of `G_j`, and it lies
in `[0,1]`.

**Averaging over `µ`.** By (E3), then linearity, then (E4) applied with
`φ = 1 − val_j >= 0` (from (E1)),

```text
1 − E_(e~µ) val_H(E)  =  E_µ (1 − Π_j val_j(e_j))  <=  Σ_j E_µ (1 − val_j(e_j))
                      <=  Σ_j D_j E_(w_j)(1 − val_j)  <=  Σ_j D_j (1 − sdp+(G_j) + δ).
```

So `sdp+(H) >= 1 − Σ_j D_j (1 − sdp+(G_j)) − δ Σ_j D_j` for every `δ > 0`.
Let `δ → 0`. `square`

`µ` enters only through `D_j`. This is the coupling-blindness.

## Step 3: union-bound completeness (Theorem CP (a), second inequality)

Let `σ_j` be an optimal labelling of `G_j`. Label `H` by
`σ(U) := (σ_j(u_j))_j`. A constraint `E` from `(e_1, ..., e_l)` is satisfied
if every `e_j` is satisfied by `σ_j`, so

```text
1 − val(σ)  <=  P_(e~µ)[some e_j violated]  <=  Σ_j P_(µ_j)[e_j violated]  <=  Σ_j D_j (1 − opt(G_j)),
```

by the union bound and then (E4) with `φ` the violation indicator. `square`

## Step 4: rounding (Theorem CP (b))

Put `ε_j := 1 − sdp(G_j)`, which is `>= 0` by (E1). (H1) at `G_j`, which has
`k_j >= 2`, gives `1 − sdp+(G_j) <= C_3 ε_j ln k_j <= C_3 ε_j ln K`. By
Step 2,

```text
sdp+(H)  >=  1 − ε_H,        ε_H  :=  C_3 · D · ln K · Σ_j ε_j   (>= 0).
```

(H2) applies to `H`, which is a unique game: it has a finite vertex set, the
finite alphabet `Π_j Σ_j`, permutation constraints and the probability
distribution `µ` on constraints. It gives

```text
opt(H)  >=  1 − 2 sqrt(2 ε_H)  =  1 − 2 sqrt(2 C_3) sqrt(D ln K Σ_j ε_j)  =  1 − C_+ sqrt(D ln K Σ_j ε_j).
```

Nothing about `H` has to be computed for this. It is an existence statement
about its optimal labelling. `square`

## Step 5: the base-SDP test (Theorem CP (c))

**The test `T`.** On input `x`:

1. Compute `(G_(x,t), n_(x,t))` for `t = 1..m`. Put `l := Σ_t n_(x,t)`, which
   is computable exactly because the `n_t` are in binary. Put
   `τ := η_Σ / (3l)`, a rational of polynomial bit size.
2. For each `t`, run the basic-SDP solver of
   `parallel-repetition-cannot-substitute-rounds-for-alphabet-proof`, Step 0,
   on `G_(x,t)` with precision `τ`. This is `sdp-fixed-precision-solvable-gls`
   with the ball data `X0 = I/k`, `r = 1/k`, `R = 2Nk` of
   `spectral-gap-no-output-kill-proof`, item 2. By reading 3 of
   `steurer-parallel-repeated-unique-games-rounding-citation`, it solves the
   same program `sdp`. It returns a feasible `X*_t` with
   `sdp(G_(x,t)) − τ <= obj_t := obj(X*_t) <= sdp(G_(x,t))`, in time
   polynomial in `|G_(x,t)|` and `log(1/τ)`.
3. Compute the rational `s := Σ_t n_(x,t) (1 − obj_t)` exactly. Accept iff
   `s <= 1.5 η_Σ`.

**Running time.** `m` and every `|G_(x,t)|` are polynomial in `|x|`, because
the route runs in polynomial time. `log(1/τ) = log(3l/η_Σ)` is polynomial,
because `l <= m · 2^(poly)`. So `T` runs in polynomial time. It never writes
`H_x` or `µ`.

**YES inputs are accepted.** Let `x in Y`. By (E2),
`1 − sdp(G_t) <= 1 − opt(G_t)`. So `1 − obj_t <= 1 − opt(G_t) + τ`, and

```text
s  <=  Σ_t n_t (1 − opt(G_t)) + l τ  <=  η_Σ + η_Σ/3  <  1.5 η_Σ.
```

**NO inputs are rejected.** Let `x in N`, and suppose `T` accepts. Since
`obj_t <= sdp(G_t)`, the deficits satisfy
`Σ_t n_t ε_t <= s <= 1.5 η_Σ`, where `ε_t = 1 − sdp(G_t)`. Now
`Σ_j ε_j` over the `l` coordinates of `H_x` is `Σ_t n_t ε_t`, since `G_t`
occupies `n_t` coordinates. So Step 4, with `D = D_x` and `K = K_x`, gives

```text
opt(H_x)  >=  1 − C_+ sqrt(1.5 D_x η_Σ ln K_x)  >  1 − Γ,
```

which contradicts `x in N`. So `T` rejects.

Hence `T` decides `Pi` in polynomial time. `η_Σ` is hardwired, and `D_x`,
`K_x` and `Γ` are used only in the analysis. `square`

## Step 6: Theorem CP (d) and Corollary CP

**(d).** Suppose `Pi` is not in `P`. By (c), some `x in N` has
`Γ <= C_+ sqrt(1.5 D_x η_Σ ln K_x) <= C_+ sqrt(1.5 D η_Σ ln K)`. Divide by
`sqrt(D η_Σ) = sqrt(η_cert)`. Then `C_+^2 · 1.5 = 8 C_3 · 1.5 = 12 C_3`.
`square`

**Item 1.** The route's promise problem `Pi` is the pullback of the NP-hard gap
through the route, and so it is NP-hard. With `Γ = C sqrt(η_cert)`, (d)
gives, unless `P = NP`, `C sqrt(η_cert) <= sqrt(12 C_3 η_cert ln K)`, that is,
`ln K >= C^2/(12 C_3)`.

**Item 2.** NO outputs have `opt <= δ`, so `Γ = 1 − δ`. YES outputs are
certified at `η_cert <= ε`. (d) gives `1 − δ <= sqrt(12 C_3 ε ln K)`. Square
both sides.

**Item 3.** For `µ = w^(⊗l)`, we have `m = 1`, `n_1 = l` and `D = 1`. If
`opt(G) >= 1 − η` on YES, the union-bound completeness is `η_Σ = lη`, and (c)
reads: `Γ > C_+ sqrt(1.5 lη ln k)` implies `Pi in P`. This is the shape of
Theorem RA (a). `square`

## Step 7: why the listed survivors are not covered

- **Set-indexed products and fortification.** Step 2 needs an ordered tuple
  `U = (u_j)`, whose coordinate `j` is a vertex of `G_j`, and a coordinatewise
  label map. For an unordered set there is no coordinate `j0` to separate
  supports. Symmetrizing the tensor over orderings breaks (2.8), because the
  supports of different orderings overlap.
- **Better-than-union-bound completeness.** Step 5 uses only
  `Σ_t n_t (1 − sdp(G_t)) <= η_Σ` on YES inputs. The output deficit is not
  used. Take the diagonal coupling, `µ(e, ..., e) = w(e)`, which has `D = 1`.
  Labelling `H` diagonally gives `opt(H) >= opt(G)`, so
  `1 − opt(H) <= 1 − opt(G) = η_Σ / l`. Here `η_out` is `l` times smaller than
  `η_cert`. (d) then bounds `Γ` only against `sqrt(l η_out)`. The check file's
  T6 exhibits `1 − opt(H) < D η_Σ` at `l = 2`.
