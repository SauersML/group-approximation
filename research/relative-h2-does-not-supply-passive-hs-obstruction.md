---
rg: 2
id: relative-h2-does-not-supply-passive-hs-obstruction
kind: claim
title: Relative H2 does not by itself supply an exact-core Hilbert-Schmidt obstruction
distinct_from:
  passive-core-quotient-has-relative-rational-h2: that computes the nonzero mapping-cone class for the passive-core quotient; this audits whether standard relative almost-flat machinery promotes it to the required matrix sequence.
  sl2-half-rational-h2-refutes-torsion-normalized-op-basin: that obtains an absolute operator-norm countersequence with exact torsion rows; this explains why it does not automatically exactify the opposite passive-core rows or obstruct flexible normalized-HS repair.
  authenticated-core-union-basin-is-relative-liftability: that states the positive relative HS lifting target; this proves the available relative H2 invariant has vanishing normalized density on every operator-small sequence.
---

**ESTABLISHED NO-GO FOR THE STANDARD RELATIVE PROMOTION AND FIXED INDEX
PAIRING.**  Keep the surjective quotient

```text
q:K -> G=PSL_2(Z[1/2])                                (RHO1)
```

from `passive-core-quotient-has-relative-rational-h2`.  The nonzero class
in `H_2(Cone(Bq),Q)` does not, by the currently available relative
almost-flat correspondence, produce a quasirepresentation of `G` whose
pullback is a genuine representation of `K`.  Moreover, its standard
fixed-cycle determinant pairing has vanishing normalized density on every
operator-small sequence.  These are statements about those two standard
promotion mechanisms, not a universal exclusion of every possible
analytic invariant built from relative homology.

There are two independent reasons.

## 1. Relative almost monodromy forgets the kernel of a surjection

Kubota's relative almost-monodromy theorem defines a stably relative
quasirepresentation for a homomorphism `phi:Lambda->Gamma` using two
quasirepresentations of `Gamma`, a representation of `Lambda`, and an
approximate stable intertwiner between the pullbacks.  Remark 6.3 states
that these data are in one-to-one correspondence with the data for
`phi(Lambda)` and contain no information about `ker(phi)`; see Definition
6.2, Remark 6.3, and Theorem 6.12 of
[Almost flat relative vector bundles and the almost monodromy correspondence](https://arxiv.org/abs/1908.10575).

For `(RHO1)`, `q(K)=G`.  The relative datum therefore compares the two
quasirepresentations on all of `G`; it does not encode that one tuple
satisfies the defining relations of `K` exactly while only the two kernel
relators added by `q` are approximate.  Thus this theorem cannot supply
the exact-core countersequence required to refute
`passive-iwahori-off-zero-cb-normal-splitting`.  The absolute Dadarlat
construction likewise contains no such exact-on-`K` refinement.

There is a conditional central-extension construction, but one of its
hypotheses is presently missing.  A multiple of the free class in
`H^2(G,Z)` restricts trivially to `K`, because `H^2(K,Z)` is torsion, so its
central extension splits over `K`.  Here is the integral calculation.  The
two vertex abelianizations in the amalgam for `K` are

```text
H_1(BS(1,4),Z)=Z<R> (+) Z/3<S>,
H_1(D_infinity,Z)=(Z/2)<R> (+) (Z/2)<X>.              (RHO2)
```

The edge map from `H_1(<R>,Z)=Z` is injective because its first coordinate
is the free generator `R` of the Baumslag--Solitar abelianization.  The
integral Mayer--Vietoris sequence therefore gives

```text
H_2(K,Z)=0,                  H_1(K,Z) finite.         (RHO3)
```

The universal coefficient sequence makes `H^2(K,Z)` finite.  The integral
Mayer--Vietoris sequence for the amalgam of `G` has a rank-one free kernel
in degree two, so `H^2(G,Z)` has free rank one.  Multiplying a class in that
free part by the order of its restriction makes the restriction zero and
splits the pulled-back central extension over `K`.

To turn that split extension into the desired finite-dimensional projective
models, however, the extension class must be of finite type.  Residual
finiteness of the middle extension would suffice; see Dadarlat--Glebe,
[Central Extensions and Almost Representations](https://arxiv.org/abs/2502.04590).
No residual-finiteness or finite-type theorem for this particular extension
is established here.  This remains a conditional operator-norm attack, not
a proved counterexample.

## 2. The fixed relative index has vanishing normalized density

Even if an exact-core operator-norm countersequence is constructed, the
fixed two-homology pairing alone does not provide a positive
normalized-HS wall.  Let `z` be one fixed integral cellular two-cycle and
let `rho_n` be matrix-valued quasirepresentations whose finitely many
relator values used by `z` have operator defects at most
`epsilon_n<1/2`.  The associated winding/pre-determinant pairing is a
finite signed sum of principal logarithms.  If its integer value is
`kappa_n` in dimension `d_n`, then

```text
|kappa_n|/d_n <= C_z epsilon_n.                        (RHO4)
```

Indeed `||log U||_op<=2||U-I||_op` for `||U-I||_op<1/2`, while
`|Tr(log U)|<=d_n||log U||_op`; summing the fixed coefficients of `z` and
dividing by `2 pi d_n` proves `(RHO4)`.

Therefore every operator-norm asymptotic sequence has

```text
kappa_n/d_n ->0.                                      (RHO5)
```

The class may remain a nonzero integer and obstruct operator-norm
perturbation, exactly as a Bott index does.  But `(RHO5)` says that this
fixed additive pairing has sublinear normalized index density.  Through
this pairing alone there is therefore no positive trace-density quantity
from which the standard dimension-independent normalized
Hilbert--Schmidt lower bound could follow.  This calculation does **not**
construct an `o(d_n)`-rank surgery and does not rule out a different
geometric or analytic obstruction associated with the same homology class.

## Consequence

The class computed in `passive-core-quotient-has-relative-rational-h2`
correctly warns that exact-zero Newton estimates are only local.  It does
not, through Kubota's kernel-insensitive correspondence or the fixed
trace-log pairing above, refute the ultimate normalized-HS passive lifting
target.  A future finite-type split-central-extension construction could
still refute the **operator-norm** off-zero splitting currently used as a
sufficient Newton gate.  Proving an actual flexible surgery, or excluding
all other relative analytic obstructions, lies outside this claim.
