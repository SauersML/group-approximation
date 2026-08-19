# One compressor jointly recovers both outer transition systems

Date: 2026-08-14

## 1. Outcome

In the rank-five realization, place the four-root chain entirely inside the
rank-four core. The same comb compressor `u` then implements

```text
alpha(a)=s_0 a t_0                                   (JOT1)
```

on both commuting outer root groups `X_12` and `X_34`. The two transition
measurements should therefore not be exactified or rounded separately.

Let `F<=G` be the selected finite additive coefficient packets and let

```text
rho_L,rho_R:F->U(M),
sigma_L,sigma_R:G->U(M)                              (JOT2)
```

be the exactified outer-root representations. The left and right images
commute, so

```text
rho(a,b)=rho_L(a)rho_R(b),
sigma(x,y)=sigma_L(x)sigma_R(y)                     (JOT3)
```

are representations of `F x F` and `G x G`. Exactification must be applied
to these product groups, preserving the cross-root commutation relation.

The actual compressor unitary `U` has joint covariance for

```text
alpha x alpha:F x F -> G x G.                       (JOT4)
```

If its separate root-mean-square covariance defects are `e_L,e_R`, the
joint defect satisfies

```text
e_joint <=e_L+e_R.                                  (JOT5)
```

Applying `TRUE_COVARIANCE_CONTROLS_TOTAL_TRANSITION_VARIANCE.md` once to
the product group gives one joint fine extension-character PVM. Its two
outer transition measurements are deterministic marginals of this same
PVM. There is consequently no relative rounding gauge, marginal-matching
problem, or measurement-compatibility problem between the two outer roots.

## 2. Covariance telescope

Write

```text
A=U rho_L(a) U*,       B=U rho_R(b) U*,
A'=sigma_L(alpha(a)),  B'=sigma_R(alpha(b)).         (JOT6)
```

Unitarity gives

```text
U rho_L(a)rho_R(b) U*=AB.                           (JOT7)
```

The elementary product telescope is

```text
AB-A'B'=(A-A')B+A'(B-B').                           (JOT8)
```

All four factors are contractions. Hence

```text
||AB-A'B'||_2 <=||A-A'||_2+||B-B'||_2.              (JOT9)
```

Minkowski's inequality in the normalized `L^2(F x F;L^2(M))` space proves
`(JOT5)`. The constant is independent of both packet sizes and the matrix
dimension.

## 3. Joint Fourier projection

Let `P_(chi_L,chi_R)` be the joint source character PVM and
`Q_(zeta_L,zeta_R)` the joint target character PVM. Since the two outer root
representations commute, these are exactly the products of their marginal
spectral projections.

Under exact covariance,

```text
U P_(chi_L,chi_R) U*
 =sum_(zeta_L o alpha=chi_L,
       zeta_R o alpha=chi_R)
    Q_(zeta_L,zeta_R).                              (JOT10)
```

For approximate covariance, the total commutator energy against the joint
fine PVM is at most `2 e_joint^2`, and the intrinsic effects

```text
P U*Q_(zeta_L,zeta_R)U P                            (JOT11)
```

round to one PVM with ambient total squared error below
`9 e_joint^2`. Summing its atoms over `zeta_R` or `zeta_L` gives the two
outer marginal measurements. Because they are coarsenings of one PVM, they
commute exactly and share their joint outcome by construction.

This is stronger than applying single-edge recovery twice and then invoking
`TRUE_COMMUTING_TARGET_PACKETS_SYNCHRONIZE_TRANSITIONS.md`. That theorem
remains useful when two different compressor words are unavoidable; here
the common comb word supplies the joint construction directly.

## 4. Exact scope

This closes all compatibility attributable merely to using two different
outer root positions. It also removes the need to compare two commutant
gauges: the joint transition family `(JOT11)` is intrinsic to one represented
unitary and one product-group Fourier PVM.

It does **not** yet create the finite paired-radical endomorphisms. A joint
outcome `(zeta_L,zeta_R)` supplies two complete outer additive characters,
but a finite coefficient window is not invariant under all four maps

```text
a |-> a t_i,       b |-> s_j b.                     (JOT12)
```

The finite `UT_4(F_2)` model still realizes `(JOT10)` locally. The remaining
theorem must use proper-compressor covariance across growing windows to make
the induced radical-quotient arrows endomorphisms of common finite label
spaces with vanishing boundary/mismatch rate.

Thus the live gate is no longer joint PVM recovery. It is:

> **Finite-window endomorphism decoder.** From the single joint outer
> extension-character PVM, extract finite separating paired quotients on
> which `R_0,R_1,L_0,L_1` are common-coordinate endomaps and the two
> diagonal/one crossed pairing errors tend to zero.

Once this is proved, the robust `1/36` floor closes the contradiction.

No local computation or build was run for this note.
