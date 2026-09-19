---
rg: 2
id: lcs-parity-gadgets-preserve-odd-dictator-affine-hull
kind: claim
title: Every perfectly complete parity gadget preserves the odd affine hull of its honest dictators
artifacts:
  - research/lcs-odd-dictator-affine-hull-no-go-proof.md
distinct_from:
  taller-vidick-positive-noise-collapses-central-sign: that finds a two-equation contradiction in the published positive-noise support; this treats every parity-equation modification which remains perfectly complete on the honest scalar atoms.
  perfect-correlated-masks-have-undamped-conditioned-spectrum: that proves a Fourier multiplier obstruction for mask distributions; this proves the distribution-free affine closure of all binary LCS gadgets, including auxiliary variables and new parity equations.
  linear-encoding-lcs-admits-odd-subset-cheats: that studies when local odd subsets assemble through the source overlaps; this gives the exact local extension theorem and does not assume global extendability.
---

Let `Q` be a finite set of folded binary query variables and let
`D={d_phi:phi in S} subseteq {+1,-1}^Q` be the honest dictator
assignments on a nonempty spectral support `S`.  Consider any finite binary
LCS gadget on `Q` and an arbitrary finite set of auxiliary binary variables
`A`.  Assume exact atomwise completeness:

```text
for every phi in S, d_phi has a scalar satisfying extension
(d_phi,a_phi) in {+1,-1}^{Q union A}.                    (ODA1)
```

Then every odd product of honest dictators also has a scalar satisfying
extension:

```text
(product_(phi in beta) d_phi,
 product_(phi in beta) a_phi)
is satisfying whenever |beta| is odd.                   (ODA2)
```

Equivalently, the projection of the scalar solution set to `Q` contains
the affine hull `Aff(D)` over `F_2`.  This holds equation by equation, so
it also applies to probabilistic tests: value one on each honest atom forces
value one on every odd product for every positive-weight parity test.

The conclusion is sharp.  For every finite `D`, the set `Aff(D)` itself
is the scalar solution set of a finite family of parity equations on `Q`.
Thus no parity-only extension can have a smaller scalar projection while
retaining all members of `D`.

For the full folded long code on `S`,

```text
Q={functions S->{+1,-1}}/{f~-f},
d_phi([f])=chosen_representative([f])(phi),              (ODA3)
```

the odd products are pairwise distinct.  Hence

```text
|Aff(D)|=2^{|S|-1},
Aff(D)={product_(phi in beta)d_phi: |beta| odd}.         (ODA4)
```

Consequently `Aff(D)=D` exactly when `|S|<=2`.  If `|S|>=3`, every
finite parity-equation gadget satisfying `(ODA1)` has a perfect scalar
solution labelled by an odd subset of size at least three.  Auxiliary LCS
variables, changing the folding section, deleting or reweighting masks, and
adding further parity equations cannot remove all such modes.

Applied to the Taller--Vidick zero-noise seam, this strengthens the mask-law
boundary.  Masks supported on the honest-spectrum annihilator are only one
instance of the obstruction: any support/folding-only repair whose
auxiliaries remain atomwise scalar is trapped by `Aff(D)`.  A live repair
must instead use a genuinely non-affine test before groupification, couple
different contexts so that the local atoms do not have separate scalar
extensions, or begin with a native LCS gap.  This claim is a route no-go, not
a nonhyperlinear-group construction.
