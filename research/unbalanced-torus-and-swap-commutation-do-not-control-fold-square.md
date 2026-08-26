---
rg: 2
id: unbalanced-torus-and-swap-commutation-do-not-control-fold-square
kind: claim
title: The unbalanced torus word and all displayed swap commutators still leave the fold square free
invalidates:
  - sl3-swap-fold-square-from-unbalanced-torus-alone
artifacts:
  - research/unbalanced-torus-swap-countermodel-proof.md
distinct_from:
  unbalanced-root-leak-does-not-charge-off-spectral-separators: that four-dimensional packet makes the unbalanced word exact but deliberately leaves one displayed coefficient noncentral for the HNN letter; this two-dimensional packet makes the swap commute with every coefficient occurring in both torus closures and tests the fold square itself.
  unbalanced-torus-relator-closes-product-projective-sector: that assumes one exact lattice representation tensored with a single denominator multiplicity unitary; this proves that the torus word and the swap commutators do not manufacture that product normal form.
  single-hecke-edge-has-exact-two-sheet-atlases: that keeps the full lattice and one parahoric edge but its literal sheet flip already has fold square one; this keeps two displayed torus closures and realizes fold square minus one, at the price of omitting the rest of the lattice presentation.
  sl3-swap-extension-has-defect-only-fold-square-rigidity: that uses every relation in a fixed presentation of the arithmetic actor; this is an exact countermodel only to the strictly smaller local interface obtained by forgetting mutual lattice-word consistency among the displayed coefficients.
---

Use the two rank-one torus closures

```text
D_12=A_12 H B_21 H^* A_12 W_12^*,
D_23=A_23 H B_32 H^* A_23 W_23^*,
R_tor=H^*D_12D_23
```

from `two-torus-closures-detect-denominator-multiplicity`.  Adjoin positive
root slots `E_12,E_23` and impose the displayed rank-one consistency

```text
A_12=E_12^2,       W_12=E_12 B_21 E_12,
A_23=E_23^2,       W_23=E_23 B_32 E_23.                 (UTS0)
```

There is an exact packet in `M_2` for which `(UTS0)` holds and

```text
S^2=H^*H=I,
[S,A_12]=[S,B_21]=[S,W_12]
 =[S,A_23]=[S,B_32]=[S,W_23]=0,
[S,E_12]=[S,E_23]=0,
R_tor=I,                                                   (UTS1)
```

while, for `V=HSH^*S`,

```text
V^2=-I,
Re tr(V^2)=-1,
tr(QPQ-(QPQ)^2)=1/8,                                     (UTS2)
```

where `P=(I-S)/2`, `Q=HPH^*`, and all traces are normalized.  Thus the
fold-square defect is maximal even though the unbalanced arithmetic word and
every displayed swap--coefficient commutator have zero defect.

The packet is deliberately **not** an assignment of the full lattice
presentation.  Each displayed rank-one doubling and Weyl identity is exact,
but the remaining relations forcing both packages to lie in one
representation of `SL_3(Z)` are not imposed.  That omitted actor consistency
is exactly the point: the unbalanced torus word closes the pure
product-multiplicity escape, but it does not by itself extract such a
multiplicity coordinate from an arbitrary actor outlier.

Consequently any full-double mixed-word estimate proving fold-square rigidity
must consume at least one further relation coupling these coefficient values
inside the actual lattice presentation.  Treating each displayed branch separately as
commuting-with-the-swap inputs to `R_tor`, even with every error equal to zero,
cannot work.  Together with the existing bounded-depth rank-one fences, this
puts an `A_2` commutator/chamber relation first among the surviving local
candidates; the present countermodel itself does not assert that every larger
rank-one packet is impossible.

The first literal mixed word does detect this packet.  In `SL_3(Z)`,

```text
w_12 x_23(1) w_12^(-1)=[x_12(1),x_23(1)]=x_13(1).      (UTS3)
```

For the matrices below the left side of the eliminated equality is `E_23`,
whereas the right side is `I`, because all displayed coefficients are
diagonal.  Thus `(UTS3)` is an exact location of the next seam, not a theorem
that it alone pays the fold energy.  A positive continuation must turn this
or another genuinely mixed actor defect into a dimension-free fold-square
estimate on arbitrary outlier assignments.

DERIVATION
unbalanced-torus-swap-countermodel-proof
