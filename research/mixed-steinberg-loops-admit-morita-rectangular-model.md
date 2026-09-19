---
rg: 2
id: mixed-steinberg-loops-admit-morita-rectangular-model
kind: claim
title: Pure mixed Steinberg loops admit an exact finite Morita-rectangular model
distinct_from:
  outer-root-leavitt-table: that proves the diagonal/crossed nested commutator words in one ring; this realizes those words and all their rank-five/six associativity refinements with unequal source and target reservoirs.
  rectangular-escape: that gives the paired-label and Weyl representation model; this explains algebraically why adding more Steinberg commutator triangles does not close the escape.
  weyl-commutant-superrank-detects-rectangular-return: that detects unequal reservoirs once a return identifies their commutant projections; this proves the existing mixed loops do not supply that identification.
---

ESTABLISHED.  Let `E` be a nonzero finite-dimensional vector space over
`F_p`, let `F=E direct_sum E`, and let

```text
s_i:E->F,            t_i:F->E       (i=0,1)              (MSM1)
```

be the coordinate inclusions and projections.  Then

```text
t_i s_j=delta_(ij) 1_E,
s_0t_0+s_1t_1=1_F.                                      (MSM2)
```

Place arbitrary finite-dimensional vector spaces at the vertices of a
rank-five or rank-six root chain and use rectangular linear maps as root
coefficients.  For a composable coefficient
`a:V_j->V_i`, let `e_ij(a)` be the corresponding block transvection on the
direct sum of all vertex spaces.  Direct block multiplication gives every
Steinberg mixed relation:

```text
[e_ij(a),e_jk(b)]=e_ik(ab),
[e_ij(a),e_kl(b)]=1             when the roots are distant. (MSM3)
```

Because matrix composition is associative, every rank-five/six loop made by
pasting these commutator triangles commutes exactly.  Substituting `(MSM1)`
in the outer-root paths gives both diagonal returns and both crossed-zero
relations of `outer-root-leavitt-table` exactly.  Further bounded mixed
triangles add no constraint: they are associativity diagrams in this finite
linear category.

The model is genuinely rectangular.  The two identities in `(MSM2)` are
`1_E` and `1_F`, not one common object identity.  On Weyl phase sectors this
is precisely the source-factor/target-factor trade measured by
`(WCS4)`.  Taking a regular unitary representation of the finite block group
also supplies exact finite-dimensional unitary matrices and canonical trace
on every nonidentity block-group word.

Therefore the presently named rank-five/six **mixed commutator loops do not
transport the commutant projection back to the identical reservoir**.  A
successful extra loop must contain a same-object identification after a net
one-to-two refinement.  Equivalently, it must distinguish `1_E` from `1_F`
in the finite Morita model.  More multiplication triangles, Hall--Witt
reassociations, distant-root commutations, or Weyl permutations of root
indices do not do this: they preserve the coefficient's source and target
sort.

This does not give an exact representation of the full affine-Leavitt
Steinberg presentation with surviving mark; such a representation is
impossible by `affine-leavitt-steinberg-mark-is-fd-invisible`.  It is the
sharp countermodel to the proposed **mixed-loop decoder language**.  The
full presentation can beat it only through a relation whose decoding
retains the equality of the coefficient reservoir across the refinement,
which is exactly the matrix-coordinate same-factor return still missing.
