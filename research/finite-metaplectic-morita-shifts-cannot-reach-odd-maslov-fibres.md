---
rg: 2
id: finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres
kind: claim
title: Finite metaplectic Morita shifts cannot reach an odd Maslov fibre
invalidates:
  - odd-maslov-llp-via-finite-metaplectic-morita-shift
distinct_from:
  metaplectic-half-shift-preserves-twisted-fibre-llp: that constructs the valid shift by one-half; this proves that the same finite equivariant tensor-compression mechanism cannot cross from its two-element orbit to the odd one-third orbit.
  deligne-triple-cover-fd-central-invisibility: that rules out exact projective representations in the mod-three sector; this identifies such a representation as a necessary coefficient of every finite equivariant Morita shift into that sector.
  maslov-generator-complete-order-model-is-llp-strength: that says a successful generic complete-order model would prove full LLP; this rules out only the natural finite generator-equivariant Morita/tensor bridge supplied by residual finiteness of the metaplectic base.
---

**ESTABLISHED SCOPED NO-GO.**  Put

```text
A_theta=C^*(Sp_4(Z); exp(2 pi i theta b)).
```

Consider a finite-dimensional generator-equivariant tensor/Morita shift:
on canonical projective generators it is implemented, up to a scalar
one-cochain, by

```text
u_g^theta |-> u_g^phi tensor v_g,                       (FMS1)
```

where the `v_g` act on one finite-dimensional coefficient space.  Exact
multiplicativity in `(FMS1)` forces `v` to be an exact projective
representation whose multiplier class is `theta-phi`.  The same conclusion
holds for a finite equivariant Morita bimodule: its finite coefficient action
is a projective representation carrying the difference of the two twists.

For `Sp_4(Z)`, no such finite coefficient exists when

```text
theta-phi is 1/3, 2/3, 1/6, or 5/6.                    (FMS2)
```

Indeed a coefficient with class `1/3` or `2/3` gives a finite-dimensional
representation of Deligne's triple cover on which its central `Z/3` acts
nontrivially, contradicting `deligne-triple-cover-fd-central-invisibility`.
The `1/6` and `5/6` cases restrict to the same nontrivial character of the
order-three kernel in

```text
1 -> Z/3 -> E_6 -> E_2 -> 1,
```

and are impossible for the identical reason.  Tensor products, conjugates,
finite direct sums, and matrix amplifications of exact representations coming
from the residually finite metaplectic base produce only difference classes
`0` and `1/2`; they never leave that two-element subgroup.

Thus the exact finite metaplectic model proves the half-shift theorem but
cannot transport LLP from the untwisted/metaplectic fibres to the odd Maslov
fibre.  This does **not** rule out a non-equivariant ucp retract or some new
intrinsic proof of odd-fibre LLP; those remain exactly
`sp4-mod3-twisted-fibres-have-llp`.

The proof is `finite-morita-shift-detects-projective-difference-proof`.

