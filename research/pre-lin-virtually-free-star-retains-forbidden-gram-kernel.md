---
rg: 2
id: pre-lin-virtually-free-star-retains-forbidden-gram-kernel
kind: claim
title: Pre-Lin exactification of the finite packet star retains the forbidden Gram kernel
distinct_from:
  role-hyperoctahedral-type-has-an-orthogonal-amalgam-model: that gives two freely rotated selected types over a common D8 representation; this treats the whole finite star, the order of HS exactification and Lin rounding, and the forbidden-weighted scalar `(CPS12)`.
  predicate-preserving-nonscalar-frames-miss-forbidden-source: that proves the common-kernel inequality for an already exact family of selector-equivariant transports; this shows simultaneous virtually-free exactification cannot remove that kernel and Lin's projection-density rounding preserves it exactly.
  exhaustive-marked-type-energy-summation: that sums typewise estimates once one estimate exists on every type of one fixed packet; this proves that the context-star decompositions do not create those estimates and states the exhaustive-type dichotomy.
---

Let `Pi_star` be a finite star of finite context packet groups, with every
edge group equal to the literal common D8 packet.  For each context-menu
vertex `v=(c,T)`, let `P_v` be its selected predicate carrier.  Suppose the
edge transport preserves the context selector algebra and its allowed set
`R_c`, exactly as required for the transported row still to represent the
same predicate.  Let

```text
T=e_+ j e_-,       Q=T^*T,
Ftilde_c=T^*F_c T=Q(1-p_(R_c)).                        (PLV1)
```

Here `T,Q` are the word-visible Gram block and source from the common D8
packet, `F_c` is the target forbidden projection, and `Ftilde_c` is its
source pullback.  After **simultaneously exactifying the whole star**, every
pulled selected carrier `R_v` satisfies

```text
R_v<=Qp_(R_c),            R_v Ftilde_c=0.              (PLV2)
```

Consequently any finite or exhaustive family of predicate-preserving
selected vertices has the same forbidden common kernel.  If `R_c^sel` is
the join of their ranges, then

```text
R_c^sel Ftilde_c=0.                                    (PLV3)
```

On that kernel the selected covered energy is zero and the uncovered Gram
energy is exact (equivalently after pushing back to the target by `T`):

```text
C_forb,c=0,
L_forb,c=||(1-R_c^sel)Ftilde_c||_2^2
        =||Ftilde_c||_2^2
        =||(1-P_c)F_cT||_2^2.                         (PLV4)
```

The order of the two analytic operations cannot change `(PLV2)--(PLV4)`.
The fundamental group of the star is virtually free, so normalized-HS
stability may exactify all vertex packets and edge identifications at once.
But an exact representation of the star is already a zero-defect input to
that theorem.  In particular, the D8-commutant rotations from the
orthogonal-amalgam model remain exact fixed points; stability supplies no
new relation between their multiplicity carriers.

Now apply Lin rounding to the normalized Gram vector `T`.  By
`partial-isometry-gram-state-collapses-lin-corners`, every positive-measure
spectral layer is the same word-visible projection `Q`.  Hence Lin does not
average, enlarge, or move any `R_v`, and the forbidden kernel `Ftilde_c` survives
on every layer.  Exactifying before Lin therefore avoids a later Reynolds
twirl but still does not imply `(CPS12)`.

This failure has exact finite-dimensional witnesses with positive marked
mass.  Choose a rejected selector character `a notin R_c`.  The regular
stationary type flow of the finite graph of finite groups contains its
marked atom with positive multiplicity.  Equivalently, residual finiteness
of the virtually-free star gives a finite quotient injective on all vertex
groups, and its regular representation has

```text
tau(Qp_a)>0.                                           (PLV5)
```

Choose the D8-multiplicity intertwiners so that the same character is used
for each occurrence of every shared variable on this atom.  Then the
literal consistency residual is zero on its Gram compression, while
`P_vp_a=0` for every selected row and at least one context rejects `a`.
Thus on this finite compressed Gram atom,

```text
C_forb=0,       E_cons=0,       L_forb>0.              (PLV6)
```

This is the zero-defect orthogonal-amalgam escape in the precise scalar
form that contradicts `(CPS12)` if `(CPS12)` is claimed from the packet-star
relations and predicate-preserving selected rows alone.

There is a sharp exhaustive-type dichotomy.

1. If every added type carrier remains supported on `R_c`, then `(PLV3)`
   holds no matter how many context vertices are added; the menu is
   exhaustive only among allowed carriers and still misses `F_c`.
2. If one includes **all** marked irreducible types of a single context
   packet, their central projections do sum to `Q`.  But supplying an exact
   positive predicate row on every such type is precisely the algebraic
   exhaustive detector forbidden by induced representations in
   `algebraic-exhaustive-marked-type-detectors-violate-induction`.

Thus a virtually-free star can exactify all local packets before Lin, or an
exhaustive type decomposition can cover `Q`, but the two facts do not
authenticate forbidden-weighted predicate rows.  Closing `(CPS12)` still
requires a non-predicate-preserving mixed two-cell or a genuinely
finite-matrix capacity/trace return; no ordering of the existing
exactification and rounding steps supplies it.
