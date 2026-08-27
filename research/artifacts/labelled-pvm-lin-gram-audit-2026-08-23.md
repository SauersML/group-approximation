# Labelled-PVM Lin Gram audit (2026-08-23)

## Exact operator package

Let `(E_i)` and `(F_i)` be orthogonal projection families and let `T_i` be
contractions.  The user-supplied branch operator is

```text
G=sum_i F_i T_i E_i.                                  (LPA1)
```

Orthogonality gives, with no approximation,

```text
G^*G=sum_i E_i T_i^*F_iT_iE_i <=sum_i E_i,
GG^*=sum_i F_iT_iE_iT_i^*F_i <=sum_i F_i,             (LPA2)

F_iG=GE_i=F_iT_iE_i,
||G||_2^2=sum_i||F_iT_iE_i||_2^2.                    (LPA3)
```

Thus `G` is a contraction, is exactly label-intertwining, and puts every
surviving branch on one Gram state.  If each compressed branch is a partial
isometry with source `E_i`, then `G` is a partial isometry with source
`sum_iE_i`.

For arbitrary nonzero `G=U|G|`, equations `(LPA3)` imply

```text
[G^*G,E_i]=0.
```

Every positive spectral layer `P_lambda` of the normalized Gram density
`|G|/||G||_2` therefore commutes with the source PVM, and polar cancellation
on that layer gives

```text
F_i U P_lambda=U E_i P_lambda.                        (LPA4)
```

This is exactly the common labelled-PVM corner needed after Lin's spectral
layering.  In the partial-isometry case all positive-measure layers collapse
to the one source projection, as in
`partial-isometry-gram-state-collapses-lin-corners`.

## Sharp binary covariance constants

For complete PVMs indexed by `a in {+1,-1}^k`, one common contraction `T`,
and

```text
A_j=sum_a a_jF_a,       Z_j=sum_a a_jE_a,
G=sum_a F_aTE_a,
D_j=A_jT-TZ_j,
```

the full block decomposition gives

```text
||T-G||_2^2=sum_(a!=b)||F_aTE_b||_2^2,

sum_j||D_j||_2^2
 =4 sum_(a,b) Hamming(a,b)||F_aTE_b||_2^2.            (LPA5)
```

Hence for two endpoint bits

```text
4||T-G||_2^2
 <=sum_(j=X,Y)||D_j||_2^2
 <=8||T-G||_2^2.                                     (LPA6)
```

If `T^*T=Q`, then

```text
||G||_2^2
 >=tau(Q)-(1/4)sum_j||D_j||_2^2.                     (LPA7)
```

Moreover, without assuming `[Q,Z_j]=0`,

```text
[Q,Z_j]=D_j^*T-T^*D_j,
||[Q,Z_j]||_2<=2||D_j||_2.                           (LPA8)
```

Thus once literal common Gram and compressed covariance are present, the
source-commutator terms in `(SEC4)` are not independent.

## One-bit anchor when the source endpoints do not commute

The live S3 cell does not initially declare the two shared source words
`Z_X,Z_Y` commuting.  A four-atom source PVM must therefore not be silently
assumed.  Anchor only `X`: its two spectral projections always form a PVM.
For

```text
G_X=sum_(e=+-1) ((1+eA_X)/2)T((1+eZ_X)/2)
```

orthogonality of the four sign blocks gives the exact identities

```text
A_XG_X=G_XZ_X,
||T-G_X||_2^2=(1/4)||A_XT-TZ_X||_2^2,
||G_X||_2^2=tau(Q)-(1/4)||A_XT-TZ_X||_2^2             (LPA9)
```

when `T^*T=Q`.  With `D_j=A_jT-TZ_j`, the other endpoint obeys

```text
||A_YG_X-G_XZ_Y||_2<=||D_X||_2+||D_Y||_2.             (LPA10)
```

If the target endpoints commute and `R_Y=A_YG_X-G_XZ_Y`, then

```text
G_X[Z_X,Z_Y]=-A_XR_Y+R_YZ_X,
||G_X[Z_X,Z_Y]||_2<=2||R_Y||_2.                       (LPA11)
```

Thus Lin need not manufacture a joint source PVM.  The binary anchor makes
one label exact; positive mass and the still-mixed `Y`, role, and return
packet covariance must all be forced on this same `G_X`.

For completeness, if both original covariance rows are retained, the joint
source PVM can be recovered with no new asymptotic hypothesis.
`one-s3-row-rounds-joint-source-pvm` proves that, for
`d_j=||A_jV-VZ_j||_2`, there are commuting corner reflections `R_X,R_Y` with

```text
||R_X-QZ_XQ||_2<=sqrt(2)d_X,
||R_Y-QZ_YQ||_2
 <=sqrt(2)d_Y+(3+sqrt(2))(d_X+d_Y).                   (LPA11a)
```

The proof is compression, spectral sign, and one binary pinching.  This
justifies the complete-label formulation downstream of `(SEC2)` but cannot
be invoked downstream of a scalar mass condition which has discarded those
rows.

## Exact finite enumeration

`experiments/labelled_pvm_lin_gram_audit.py` enumerates all permutation
branches between the four two-bit label atoms, then every three-role stack.
It checks `(LPA3)--(LPA7)` combinatorially.

Remote directory:
`/projects/standard/hsiehph/sauer354/cairn-s3-packed-root-20260823`

Environment: `acn112`, Python `3.11.13`.  Canonical JSON SHA-256:

```text
3a7f77468c14ccc4ca4fca047a2b5058e9a039f7e7d30024fbc01dc57dd53a4f
```

Results:

```text
single permutation branches:       24 checked, 0 failures
three-role S3 stacks:              13,824 checked, 0 failures
one-X-bit anchor permutations:     24 checked, 0 failures
sharp covariance/loss ratios:      minimum 4, maximum 8
cyclic-shift unitary branch:        Gram mass 0, loss 1
```

The last line is the remaining firewall.  Complete source and target PVMs
and unitary branch maps do not imply positive `G` mass: a cyclic label shift
has every diagonal compression zero.  Mixed covariance on the **same**
branch reservoir, or an equivalent saturation scalar, is still necessary.

## S3 consequence and boundary

On a three-role amplification, repeat the one source label PVM and put the
three target PVMs on the diagonal role blocks.  Applying `(LPA1)` role by
role produces one contraction `G`; normalized trace averages the three
branch masses.  Its label consistency and source commutation are exact, so
Lin's spectral layers no longer have a cross-context gauge problem.

What remains is the scalar, same-reservoir estimate

```text
||G||_2^2 >= gamma tau(Q)-K E_rel-o(1),               (LPA12)
```

together with construction of the source labelled PVM from the original
shared endpoint words if the complete-label variant is used.  Alternatively,
the one-bit variant needs `(LPA12)` **and** small genuinely mixed packet
covariance on the same `G_X`.  Neither `(LPA1)` nor Lin's spectral theorem
proves these hypotheses.  Root/Julia naming also does not authenticate them:
the proper-ideal and zero-carrier models in
`one-julia-root-anchor-has-ideal-kernel-escape` set the relevant mixed block
to zero while retaining the surrounding finite packet.

The obstruction persists at fixed positive mass, not only in the cyclic
zero-mass example.  `positive-cross-gram-mass-alone-has-no-holonomy-floor`
constructs, for every `0<gamma<1`, exact intertwiners whose cross-Gram square
has mass `gamma` while an arbitrary relative commutant gauge survives.  The
unanchored packet covariance in `(SEC12)` is exactly what must see that gauge.

Accordingly the Lin package removes label synchronization, separate context
gauges, analytic PVM alignment, and explicit source-commutator rows.  It does
not remove the same-Gram mixed covariance.  The surviving relation must force
both positive branch mass and that covariance from ordinary relator energy.
