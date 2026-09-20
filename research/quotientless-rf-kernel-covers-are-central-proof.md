---
rg: 2
id: quotientless-rf-kernel-covers-are-central-proof
kind: route
title: Residually finite actions of a quotientless group are trivial, so the cover is central and Schur finishes
target: quotientless-rf-kernel-covers-are-central
requires:
  - torsion-free-central-cover-forces-abelian-finite-subgroups
artifacts:
  - research/quotientless-rf-kernel-covers-are-central.md
---

Notation as in the claim. Standard facts used, all classical:

- **(F1) Baumslag.** The automorphism group of a finitely generated residually finite group is residually
  finite (G. Baumslag, *Automorphism groups of residually finite groups*, J. London Math. Soc. 38 (1963)
  117--118).
- **(F2) Mal'cev.** Finitely generated linear groups are residually finite (A. I. Mal'cev, 1940).
- **(F3) Mal'cev.** If `N` is torsion-free nilpotent, then `N/Z(N)` is torsion-free. Hence every upper
  central factor of `N` is torsion-free (see D. J. S. Robinson, *A Course in the Theory of Groups*, §5.2).

From `torsion-free-central-cover-forces-abelian-finite-subgroups` we use the main statement: if
`1 -> A -> C -> G -> 1` is central and `C` is torsion-free, every finite subgroup of `G` is abelian.

## Step 0. Quotientless groups

Let `E` be finitely generated with no nontrivial finite quotient.

- **(P0)** Every homomorphism `f` from `E` to a residually finite group is trivial. Indeed `f(E)` is
  residually finite. If `f(E) != 1`, some finite quotient of `f(E)` is nontrivial, and composing gives a
  nontrivial finite quotient of `E`.
- **(P1)** `E` is perfect. `E^ab` is a finitely generated abelian group, and every nonzero such group has
  a quotient `Z/m` with `m >= 2`.

The two facts pass to `E/M` for every `M ◁ E`, which is again finitely generated and quotientless.

## Step 1. (QC1)(a)

`c(E) <= Aut(N)`, and `Aut(N)` is residually finite by (F1). By (P0), `c(E) = 1`. So every element of `E`
centralizes `N`, that is `N <= Z(E)`, and `N` is abelian.

## Step 2. (QC1)(b)

`N` is torsion-free, so `N -> V = N ⊗ Q` is injective, with `dim_Q V = n`. Every `α ∈ Aut(N)` extends
uniquely to the `Q`-linear map `α ⊗ id`, which gives an injective homomorphism `Aut(N) -> GL(V) ≅ GL_n(Q)`.
So `c(E)` is a finitely generated linear group, residually finite by (F2), and trivial by (P0).

## Step 3. (QC1)(c)

Read "finite Hirsch length" as: every factor of the upper central series `1 = Z_0 < Z_1 < ... < Z_k = N`
has finite torsion-free rank. We induct on the class `k`, for all pairs `(E, N)` at once. The case `k = 1`
is Step 2.

Let `k >= 2`.

- **Centre.** `Z_1 = Z(N)` is characteristic in `N`, hence normal in `E`. It is torsion-free abelian of
  finite rank, so by Step 2 applied to `(E, Z_1)`, `E` acts trivially on `Z_1`.
- **Quotient.** `N/Z_1` is torsion-free by (F3). It is nilpotent of class `k - 1`, with upper central
  series `Z_(i+1)/Z_1`, so it satisfies the same hypothesis. It is normal in the finitely generated
  quotientless group `E/Z_1`. By induction `E/Z_1` acts trivially on `N/Z_1`, so `E` acts trivially on
  `N/Z_1`.
- **Gluing.** For `e ∈ E` and `x ∈ N`, put `δ_e(x) = c(e)(x) x^(-1)`, which lies in `Z_1` by the previous
  item.
  - `δ_e` is a homomorphism `N -> Z_1`:
    `δ_e(xy) = c(e)(x) δ_e(y) x^(-1) = δ_e(x) δ_e(y)`, since `δ_e(y)` is central in `N`.
  - `e -> δ_e` is a homomorphism `E -> Hom(N, Z_1)`: `δ_(ef)(x) = c(e)(δ_f(x) x) x^(-1) = δ_f(x) δ_e(x)`,
    since `E` fixes `Z_1` pointwise.
  - `Hom(N, Z_1)` is abelian and `E` is perfect (P1), so `δ_e = 0` for all `e`.

So `c(E) = 1`, `N <= Z(E)`, and `N` is abelian. This closes the induction.

## Step 4. (QC2)

Suppose `E -> Out(N)` is trivial. Put `C = C_E(N)`.

- **`E = N · C`.** For `e ∈ E`, `c(e)` is inner, say `c(e) = c(m)` with `m ∈ N`. Then `m^(-1) e ∈ C`.
- **The quotient.** `C ∩ N = Z(N)`, so `Q = E/N = NC/N ≅ C/Z(N)`.
- **Centrality.** `Z(N) <= N` commutes with `C`, so `Z(N)` is central in `C`.
- **The example.** If `N` is finitely generated and `Out(N)` is residually finite, the image of `E` in
  `Out(N)` is trivial by (P0).

## Step 5. (QC3)

Assume `E` is torsion-free.

**Case (QC1).** `N <= Z(E)` by Steps 1--3, so `1 -> N -> E -> Q -> 1` is central with `E` torsion-free.
By `torsion-free-central-cover-forces-abelian-finite-subgroups`, every finite subgroup of `Q` is abelian.

In case (a), `N` is finitely generated, abelian and torsion-free, so `N ≅ Z^n`. In cases (b) and (c), `N`
is torsion-free abelian of finite rank `n`.

For the rank bound, let `F <= Q` be finite with preimage `E_F`. Then `1 -> N -> E_F -> F -> 1` is central
and `E_F` is torsion-free.

- `N` has finite index in `E_F`, so by Schur `[E_F, E_F]` is finite.
- `E_F` is torsion-free, so `[E_F, E_F] = 1` and `E_F` is abelian.
- `E_F` is torsion-free abelian of rank `n`, since it contains `N` with finite index.
- For any torsion-free abelian `B` of rank `n` and any prime `p`, `dim_(F_p) B/pB <= n`. Take any `n + 1`
  elements. They satisfy `Σ m_i b_i = 0` with integers `m_i` not all zero. Dividing by `gcd(m_i)`, which
  is allowed because `B` is torsion-free, makes some `m_i` prime to `p`. This gives a nontrivial
  `F_p`-relation modulo `p`.
- `F = E_F/N` is a quotient of `E_F`, so `F/pF` is a quotient of `E_F/pE_F`, and every Sylow subgroup of
  the finite abelian group `F` has rank at most `n`. Hence `F` is generated by at most `n` elements.

**Case (QC2).** Step 4 gives the central extension `1 -> Z(N) -> C -> Q -> 1`, and `C <= E` is
torsion-free. The cited claim applies again. If `Z(N) = 1`, then `Q ≅ C` is torsion-free.

## Step 6. (QC4)

Let `n >= 3` and `R != 0` unital.

- **The finite group `M`.** `M` is the set of monomial `n x n` matrices with nonzero entries in
  `{1, -1}`. It is a finite group of order at most `2^n n!`, because `±1` are central in `R`. Since
  `1 != 0` in `R`, the position pattern gives a homomorphism `p: M -> S_n`.
- **Weyl words.** `w_ij = e_ij(1) e_ji(-1) e_ij(1)` acts on the `(i,j)` block as `[[0,1],[-1,0]]` and is
  the identity elsewhere. So `w_ij ∈ EL_n(R) ∩ M`, and `p(w_ij)` is the transposition `(i j)`.
  Let `W = <w_ij> <= EL_n(R) ∩ M`. Then `W` is finite and `p(W) = S_n`.
- **Central elements have trivial pattern.** Let `g ∈ M` commute with every `e_ij(1) = I + E_ij`. Then
  `g E_ij = E_ij g`. The left side has column `j` equal to column `i` of `g` and is zero elsewhere. The
  right side has row `i` equal to row `j` of `g` and is zero elsewhere. So column `i` of `g` is supported
  in row `i`, and `p(g)` fixes `i`. This holds for every `i`, so `p(g) = id`.
- **Passing to `EL_n(R)/Z`.** For every central `Z <= EL_n(R)`, `W ∩ Z <= ker p`. So `WZ/Z` is a finite
  subgroup of `EL_n(R)/Z` mapping onto `S_n`, which is nonabelian because `n >= 3`.

**Conclusion.** A group containing `EL_n(R)/Z` has a nonabelian finite subgroup. By Step 5 it is not
`E/N` for a torsion-free, finitely generated, quotientless `E` with `N` as in (QC1) or (QC2).

The named sources are all of this form, with `R` nonzero and unital:

- `LC(X,F_q) ⋊ Z` and `LC(X,Z) ⋊ Z`;
- the unital Steinberg algebra `R = A_(F_q)(𝒢)` of the odometer groupoid, whose unit space is compact,
  with `Z` the centre of `EL_N(R)`;
- the unital Leavitt and Kun--Thom rings, to which (STF1) of `steinberg-images-die-in-torsion-free-groups`
  already applies.
