---
rg: 2
id: atlas-mixed-minor-needs-nuisance-quotient-rank
kind: claim
title: An authenticated mixed Atlas minor kills multiplicity holonomy exactly at nuisance-quotient rank three
distinct_from:
  atlas-authenticated-s3-extension-minor-decodes-pairings: that asks the literal projected Atlas rows to pass this criterion; this proves the amplification-uniform operator-valued linear algebra and its converse.
  separated-channel-identities-retain-rectangular-escape: that tensors two separated identity systems and retains the rectangular model; this treats genuinely mixed rows but shows that their desired columns may still be cancelled by nuisance multiplicity monomials.
  atlas-hard-packet-authenticates-s4-extension-triple: that asks for a common typed source and target for the three extension coordinates; this proves what the subsequent coefficient calculation must establish after that authentication.
---

Let `K` be any Hilbert space.  In the Atlas application it is one fixed
normalized-Hilbert--Schmidt corner

```text
K=L2(P M Q,tau).                                      (AMQ1)
```

Let

```text
C in Mat_(m,p)(C),       D in Mat_(m,q)(C)             (AMQ2)
```

be fixed scalar coefficient matrices.  Write `X in K^p` for the desired
operator monomials, `Y in K^q` for every other reduced multiplicity monomial
occurring in the same projected rows, and

```text
E=C X+D Y in K^m.                                    (AMQ3)
```

Let `P_D` be the orthogonal projection of `C^m` onto
`ker(D^*)=(ran D)^perp`.  The following are equivalent.

1. There is a constant `Kappa<infinity`, independent of `K`, such that

   ```text
   ||X||_(K^p) <= Kappa ||C X+D Y||_(K^m)             (AMQ4)
   ```

   for every Hilbert space `K` and all `X,Y`.
2. The desired columns have full rank modulo all nuisance columns:

   ```text
   rank [C D]=rank D+p.                               (AMQ5)
   ```
3. The quotient coefficient map `P_D C:C^p -> ker(D^*)` is injective.

When these conditions hold, if

```text
gamma=sigma_min(P_D C)>0,                             (AMQ6)
```

then `(AMQ4)` holds with `Kappa=gamma^(-1)`.  Equivalently there is a fixed
scalar matrix `A` with

```text
A C=I_p,             A D=0,                           (AMQ7)
```

and one may take `Kappa=||A||`.  All constants depend only on the finite
coefficient census and not on external multiplicity.

## Proof

Conditions `(AMQ5)` and `(AMQ6)` say that the images of the desired columns
are independent in `C^m/ran(D)`.  Apply `P_D tensor I_K` to `(AMQ3)`.  The
nuisance term disappears and

```text
(P_D tensor I_K)E=(P_D C tensor I_K)X.                (AMQ8)
```

Singular values are unchanged by Hilbert-space amplification, so `(AMQ6)`
gives

```text
gamma ||X|| <=||(P_D tensor I_K)E||<=||E||.           (AMQ9)
```

This proves `(AMQ4)` dimension-freely.  Taking a left inverse of `P_D C`
and composing it with `P_D` gives `(AMQ7)`.

Conversely, if `(AMQ5)` fails, choose `0!=x in C^p` with
`Cx in ran(D)` and choose `y in C^q` satisfying `Cx+Dy=0`.  For any nonzero
`T in K`, put

```text
X_i=x_i T,             Y_j=y_j T.                     (AMQ10)
```

Then `E=0` while `X!=0`, refuting every estimate `(AMQ4)`.  This also proves
that no matrix-size argument can repair a failed coefficient rank without
adding further rows: the cancellation is exact at every amplification.

## Consequence for the authenticated S3 decoder

After common-corner authentication, put `p=3` and take the desired entries
to be

```text
R0^* W L0-W,       R1^* W L1-W,       R0^* W L1.      (AMQ11)
```

Inventory **all** other reduced path monomials in the selected literal rows
as the nuisance vector `Y`.  If `(AMQ5)` holds, projected relator defects
give

```text
sum_i ||X_i||_2^2
 <=gamma^(-2) sum_r ||E_r||_2^2.                      (AMQ12)
```

This is the sought same-reservoir holonomy ceiling.  Because every selected
row is a fixed compression of an actual packet relator (or a fixed bounded
normal-closure consequence), its right side is bounded by a fixed constant
times the packet energy.  The three defects in `(AMQ11)` then feed directly
into `finite-window-decoder-from-s3-hard-packet` and the spectral Leavitt
floor.  Thus a verified literal quotient-rank-three certificate is already
strong enough to prove the explicit nonhyperlinear endpoint.

There are two sharp falsification gates.

* A nonzero `3 by 3` minor of `C` alone is insufficient.  For example
  `C=I_3,D=I_3` has such a minor, but `Y=-X` makes every row vanish.  The
  required certificate is `(AMQ5)`, not `rank C=3`.
* Equal carrier dimensions, equal traces, or separately authenticated
  extension labels do not make `(AMQ3)` typed.  Scalar row operations are
  legitimate only after all terms have fixed source `Q` and target `P`, or
  after literal packet transports identifying those corners have themselves
  been included among the unknowns and eliminated by `(AMQ5)`.  Arbitrary
  choices of such identifications differ by the full external multiplicity
  unitary group and are precisely the holonomy one is trying to control.

Therefore the authenticated mixed-minor route is analytically sound, but
the exact finite computation it needs is stronger and more precise than the
phrase “a nonzero minor on the three desired columns.”  The live Atlas task
is a typed row census followed by the quotient-rank test `(AMQ5)`.
