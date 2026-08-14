# Isospectral conjugacy has dimension-free flag repair

Date: 2026-08-14

## 1. Outcome

Let `R,S in U(d)` have the same eigenvalue multiset and let `U in U(d)`
satisfy

```text
||U R U^*-S||_2<=epsilon.                             (FGR1)
```

There are isospectral unitaries `R',S'` and a unitary `V` such that

```text
V R' V^*=S'                                           (FGR2)
```

and, for an absolute constant `C`,

```text
||R-R'||_2, ||S-S'||_2, ||U-V||_2
 <=C epsilon^(1/3).                                   (FGR3)
```

The estimate is independent of `d`, the number of distinct eigenvalues,
and the minimum spacing between them.  If every eigenvalue of `R,S` has
odd finite order, the corrected spectra can be chosen from the original
spectrum; in particular `R',S'` still have one common odd finite exponent.

Applied after
`TRUE_IWAHORI_DEFECT_HAS_ODD_SPECTRAL_SHADOW.md`, this repairs either one of
the two approximate modular Weyl conjugacies without a spectral-gap
assumption.  Thus a single odd spectral flag is not an obstruction.

The two repairs cannot yet be performed independently: changing the
spectral labels to repair the first conjugacy can destroy the inverse-square
labels used by the second.  The surviving Iwahori endpoint is simultaneous
equivariant coarsening of the two fourth-power-linked flags.

## 2. Spectral coupling carried by the conjugator

Write the spectral decompositions

```text
R=sum_i lambda_i P_i,          S=sum_j mu_j Q_j.       (FGR4)
```

The projections in each family are pairwise orthogonal and sum to one.
Put

```text
w_(j,i)=||Q_j U P_i||_2^2.                             (FGR5)
```

Because `U` is unitary, these weights form a coupling between the empirical
spectral measures, including the normalized ranks of repeated eigenspaces.
Direct orthogonality gives the exact identity

```text
||U R U^*-S||_2^2
 =sum_(i,j) |lambda_i-mu_j|^2 w_(j,i).                (FGR6)
```

Let `d_T` be angular geodesic distance on the unit circle.  Since

```text
d_T(z,z')<=(pi/2)|z-z'|,                              (FGR7)
```

Cauchy--Schwarz and `(FGR1)--(FGR6)` imply

```text
sum_(i,j) d_T(lambda_i,mu_j)w_(j,i)
 <=(pi/2)epsilon.                                     (FGR8)
```

Put `c=pi/2`.

## 3. Randomly shifted arc coarsening

Fix an integer `N>=2`, put `h=2pi/N`, and partition the circle into `N`
half-open arcs of angular length `h`.  Rotate the entire partition by a
uniform offset in `[0,h)`.

For two fixed points at angular distance `r`, the probability that a
partition boundary separates them is at most

```text
min(1,r/h)<=r/h.                                      (FGR9)
```

Average `(FGR9)` against the coupling `(FGR5)` and use `(FGR8)`.  Some
offset has total cross-arc mass

```text
eta=sum_(arc(lambda_i)!=arc(mu_j)) w_(j,i)
 <=c epsilon/h.                                       (FGR10)
```

For every nonempty arc, choose one unit scalar `zeta_k` in that arc and set

```text
E_k=sum_(lambda_i in arc k)P_i,
F_k=sum_(mu_j in arc k)Q_j,
R'=sum_k zeta_k E_k,
S'=sum_k zeta_k F_k.                                  (FGR11)
```

Because `R` and `S` have the same eigenvalue multiset, the ranks of `E_k`
and `F_k` agree for every `k`.  Moreover

```text
||R-R'||_2<=h,              ||S-S'||_2<=h.            (FGR12)
```

If the original spectrum has odd finite order, choose `zeta_k` to be one
of the original eigenvalues in the arc whenever the arc is nonempty.  Then
all corrected eigenvalues still have odd finite order.  Since there are
finitely many of them, one odd exponent annihilates both `R'` and `S'`.

## 4. Blockwise polar correction

Pinch `U` to the matching coarse blocks:

```text
T=sum_k F_k U E_k.                                    (FGR13)
```

Orthogonality and `(FGR10)` give

```text
||U-T||_2^2=eta.                                      (FGR14)
```

For each `k`, the contraction

```text
T_k=F_k U E_k:E_k C^d->F_k C^d                       (FGR15)
```

is square because the two projections have equal rank.  Take its polar
part and extend across its kernel and cokernel to a unitary

```text
V_k:E_k C^d->F_k C^d.                                 (FGR16)
```

If `s_1,...,s_r` are the singular values of `T_k`, then

```text
sum_a(1-s_a)^2<=sum_a(1-s_a^2).                       (FGR17)
```

Summing `(FGR17)` over `k` and normalizing by `d` gives

```text
||V-T||_2^2<=eta,             V=sum_k V_k.            (FGR18)
```

Indeed the right side is precisely the mass of `U` outside the diagonal
coarse blocks.  Therefore

```text
||U-V||_2<=2sqrt(eta)<=2sqrt(c epsilon/h).             (FGR19)
```

By construction `V E_k V^*=F_k` for every `k`, so `(FGR11)` gives the exact
conjugacy `(FGR2)`.

## 5. Optimized dimension-free estimate

Set

```text
q=(c epsilon)^(1/3).                                  (FGR20)
```

For `epsilon<=2`, one has `q<pi`.  Choose an integer `N` so that

```text
q<=h=2pi/N<=2q.                                       (FGR21)
```

Then `(FGR10)`, `(FGR12)`, and `(FGR19)` give

```text
||R-R'||_2,||S-S'||_2<=2q,
||U-V||_2<=2q.                                        (FGR22)
```

Thus one may take

```text
C=2(pi/2)^(1/3)                                       (FGR23)
```

in `(FGR3)`.  For larger `epsilon` the statement is trivial after increasing
the absolute constant, since the distance between unitaries is at most two.

## 6. Iwahori application and surviving simultaneous gate

The odd spectral-shadow theorem produces nearby `X_o,Y_o` with

```text
Spec(X_o^2)=Spec(Y_o^(-1)),
Spec(Y_o^2)=Spec(X_o^(-1)).                            (FGR24)
```

The original modular Weyl unitaries approximately implement both
conjugacies in `(FGR24)`, with defect `O(delta)`.  Applying the present
theorem to either line yields an exact conjugacy after an
`O(delta^(1/3))` perturbation, and the correction may retain odd-order
spectral representatives.

Applying it separately to both lines is invalid.  The coarse labels chosen
for `X_o^2` and `Y_o^(-1)` in the first application need not be carried by
inverse square to the coarse labels chosen for `Y_o^2` and `X_o^(-1)` in
the second.  Restated dynamically, the partition used in Section 3 need not
be equivariant under the fourth-power permutation constructed in the odd
spectral-shadow theorem.

The remaining analytic statement is therefore:

> **Simultaneous odd-flag repair.**  Choose one coarsening of the finite
> fourth-power spectral cycles such that both conjugator couplings have
> vanishing cross-block mass and the coarsening is closed under the two
> inverse-square transitions.

Once such a common coarsening is available, the two blockwise polar
corrections above repair both Weyl conjugacies.  The remaining finite block
relations can then be treated inside the common odd-order packets.  This is
the precise point at which the two modular vertex origins must be used
together.
