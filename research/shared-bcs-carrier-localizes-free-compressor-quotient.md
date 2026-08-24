---
rg: 2
id: shared-bcs-carrier-localizes-free-compressor-quotient
kind: claim
title: Localize a prescribed free-compressor quotient pair on the shared BCS forbidden carrier
distinct_from:
  finite-inclusion-is-free-self-compressor-quotient: That constructs the abstract parent and child quotient shadows; this must force the quotient kernels to vanish on the matrix-model carrier selected by the original shared contextual tuple.
  compressor-covariant-packet-reynolds-return: That asks for a Kazhdan-scaled coefficient return and an ordinary energy payment; this asks only for the positive-density child-only adjoint sector needed by macroscopic tracial self-copy collapse.
  shared-bcs-matrix-only-supercritical-atom-selection: That selects a supercritical family for a recursive ordinary-space carrier ladder; this localizes one finite packet inclusion on a positive-density adjoint carrier and uses self-copy fixed-space equality as the terminal theorem.
---

**OPEN CARRIER-LOCALIZATION FACE.**  Fix the shared robust BCS and one of its
predicate packet inclusions `A_f<B_f`.  Apply
`finite-inclusion-is-free-self-compressor-quotient` to obtain

```text
theta:F->B_f,                 theta(alpha(F))=A_f.
```

Construct a finite group presentation extending the BCS and the ascending
HNN extension of `alpha` such that every sufficiently accurate canonical
matrix microstate has a predicate-selected adjoint projection `K` with:

1. the normalized adjoint rank of `K` is bounded below by a fixed constant
   times the square of the forbidden mass;
2. on `K`, the parent `F` action factors, up to a dimension-independent
   normalized-HS error, through `theta:F->B_f`;
3. on `K`, the child `alpha(F)` action factors through the restricted image
   `A_f`; and
4. some fixed parent generator moves `K` by a dimension-independent amount
   exactly on the packet's forbidden types.

The same finite presentation must have an exact finite-tracial model of the
shared BCS in which forbidden mass is zero and the marked word survives.
Thus no quotient-kernel relation may be imposed globally: it must be
localized by the shared contextual payload and become effective only in
finite matrix models.

Once these four estimates hold,
`predicate-rank-jump-forces-adjoint-reynolds-gap` supplies positive adjoint
density, while the free HNN gives an honest one-sided self-copy.  The terminal
fixed-projection equality then rules out the resulting child-only sector.

The load-bearing operation is conditional kernel annihilation.  Merely
adjoining the relations in `ker(theta)` globally collapses the parent to the
finite packet and makes the HNN conjugacy impossible; merely commuting an
independent packet with `F` leaves the tensor-decoupled countermodel.

Only a finite conditional relation list is needed.  Choose finite words
`r_1,...,r_s` normally generating `ker(theta)`.  If the extracted carrier is
invariant under the parent generators and every `r_j` acts trivially on it,
then every conjugate of every `r_j` acts trivially there, so the whole kernel
does.  Equations `(FQS1b)--(FQS1c)` give the corresponding fixed-word HS
estimate.  Thus the open face is not an infinite-kernel uniformization
theorem: it is a finite, payload-conditional fixed-space theorem for the
normal generators and the carrier invariance.

## Exact coefficient-ring compiler

The conditional equations themselves have a finite exact algebraic model.
Work over the splitting field of the predicate packet.  Let `P_f` be its
forbidden central idempotent, let `r_1,...,r_s` normally generate
`ker(theta)`, and start from the free product of the shared BCS coefficient
algebra with the group algebra of the free HNN base.  Impose the finite ring
relations

```text
[P_f,x_i]=0,                    [P_f,t]=0,
(x_i-b_i)P_f=0                 (theta(x_i)=b_i in B_f), (BCL0)
(r_j-1)P_f=0                    (1<=j<=s),              (BCL1)
t x_i t^(-1)=alpha(x_i).                               (BCL2)
```

The identification rows `(BCL0)` are indispensable.  The kernel rows
`(BCL1)` by themselves produce some representation of the abstract quotient
`B_f` on `P_fH`, but do not identify it with the named predicate packet
representation selected by `P_f`.  Without `(BCL0)`, the quotient action can
remain on an independent multiplicity factor, exactly as in
`agent-free-compressor-hnn-letter-preserves-product-split`.  With `(BCL0)`,
`agent-free-compressor-minimal-nonretractive-corner` proves the exact
coefficient-module rank contradiction.

In every honest coefficient-module representation, `(BCL0)--(BCL1)` make `P_fH`
reducing for the parent and stable letter, and `(FQS1b)` makes the parent
action there factor through `B_f`.  The child action factors through the
image `A_f`.  Hence the forbidden packet Reynolds difference is literally a
child-only adjoint sector.  If `P_f=0`, all conditional kernel relations are
vacuous, so the exact perfect BCS representation retains the free HNN
component and the marked central sign.

There is a stronger algebraic obstruction to this exact compiler as written.
By `agent-free-compressor-bcl-root-is-abstractly-zero`, `(BCL0)--(BCL2)`
conjugate the surviving simple algebra `P_fk[B_f]` injectively into the
strictly smaller algebra `P_fk[A_f]`.  Therefore the presented coefficient
ring already has `P_f=0`.  The displayed rows do not localize a positive
carrier; they erase it algebraically.  In particular their Steinberg payload
root is abstractly trivial and cannot be an injected bridge edge.

This finite ring presentation can be wordized by a rank-five Steinberg
presentation: impose one root word for each relation in `(BCL0)--(BCL2)`, and
`atlas-steinberg-context-absorption` propagates it through the generated
two-sided ideal.  Therefore additive corner syntax and finite
presentability are not the remaining issue.

The actual HNN letter does not by itself authenticate this corner.
`agent-free-compressor-hnn-letter-preserves-product-split` gives exact finite
rank-five models of `[P_f,F]=[P_f,t]=0`, `(r_j-1)P_f=0`, and all HNN rows in
which the payload root occupies one product-ring factor and the complete
mapping-torus action occupies another.  Thus the surviving decoder must tie
the physical `P_f` carrier to the prescribed nonstationary `B_f/A_f` packet
type.  It cannot stop after showing that the stable letter preserves the
root spectral support.

Accordingly, metric decoding of this complete quotient is not the remaining
issue: its root identity has a fixed finite derivation.  A surviving version
must weaken or conditionalize the named/HNN rows so that `P_f` remains
nonzero in the abstract coefficient ring, and only then solve the physical
payload-to-root problem.  An arbitrary unitary
normalized-HS microstate of the resulting Steinberg group need not arise
from a coefficient-module representation.  Its exponent-character root
spectra can be diffuse, and HS-small root errors can have full rank.  Thus a
completion of a corrected, abstractly nontrivial compiler still needs a
physical packet-to-root theorem such as
`bcs-atom-detects-its-e5-central-root`; decoding the already-zero BCL root
cannot supply it.

## Central-relator alternative and its density loss

Replacing the conditional equations by the relation-centralized extension
`F/[F,ker(theta)]` does make the adjoint action factor through the finite
packet on each central-character diagonal block.  It does not supply the
required carrier.  By
`centralized-quotient-shadow-density-dichotomy`,
an infinite central relation module has canonical diagonal-block density
`o(d^2)`, while a finite central relation module makes the base image finite
and destroys the proper self-copy.  Shrinking spectral boxes trades quotient
accuracy for vanishing density.  Thus projective kernel phases do not replace
the prescribed positive-density conditional decoder.

Adding a Kazhdan source cannot repair this alternative.  By
`kazhdan-relation-centralized-quotient-is-finite`, centralizing a relation
kernel with finite quotient in any property-`(T)` source makes the entire
centralized quotient finite.  Hence a Kazhdan correction step leaves no
proper injective compressor on which to run the return argument.
