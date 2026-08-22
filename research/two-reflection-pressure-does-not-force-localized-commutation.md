---
rg: 2
id: two-reflection-pressure-does-not-force-localized-commutation
kind: claim
title: Positive affine disagreement pressure does not force localized cross-commutation
distinct_from:
  twisted-disagreement-return-factors-through-localized-commutator: that proves localized cross-commutation is sufficient for a wandering return; this gives an amplification-stable two-reflection countermodel to deriving that commutation from disagreement mass alone.
  deleting-one-gap-row-has-the-wrong-orientation: that derives a lower bound for one omitted game row; this shows that even granting such a lower bound, no positive reducing subcorner with small commutator need exist.
  uniform-affine-lcs-rank-return: that asks an additional global return to make affine failure rank pay; this proves the local affine failure bit cannot itself supply that return.
---

**ESTABLISHED NO-GO.**  There are exact self-adjoint involutions in every
even matrix dimension for which disagreement has full positive density but
the commutator is maximally large on every nonzero common reducing corner.

Let

```text
Z=[[1,0],[0,-1]],             X=[[0,1],[1,0]],
C=Z tensor I_m,               B=X tensor I_m              (TRP1)
```

in `M_2 tensor M_m`, with normalized trace.  If `Q` is any projection which
commutes with both `C` and `B`, then

```text
||Q(C-B)||_2^2=2 tau(Q),
||Q(CB-BC)||_2^2=4 tau(Q).                              (TRP2)
```

In particular, no sequence of positive-density common reducing projections
can have localized commutator defect `o(1)`, despite retaining a fixed
positive disagreement row.  The example is stable under arbitrary matrix
amplification.  Adjoining a central sign represented by `J=-I` does not
change either formula.

This closes the proposed purely affine/local shortcut into
`twisted-disagreement-return-factors-through-localized-commutator`.  A parity
or Alice--Bob consistency failure bit can provide positive disagreement or
rank pressure, but the two-involution algebra has a free principal-angle
parameter.  Affine pressure alone does not select the commuting endpoints of
that parameter.

## Consequences for the existing lanes

- `oracularizable-tracial-source-gives-affine-rank-pressure` supplies a fixed
  positive mass of Taller--Vidick parity and consistency failure sectors.
  The calculation above shows that this mass cannot be fed directly to the
  localized-commutator terminal.  One still needs the global packet alignment
  in `uniform-affine-lcs-rank-return`; that theorem is precisely what removes
  the free relative angle.
- The Fanizza common modular swap proves exact left--right commutation in the
  intended infinite standard-form representation, but not on a common
  positive-density carrier in arbitrary finite ordinary-word microstates.
  Exposing such a carrier remains the
  `common-partial-isometry-swap-game-compiler` / heterogeneous-row gate.
- The arithmetic relative-commutant lane has the correct matrix-only shape:
  a projective commutant-transfer theorem would remove the relative angle
  without imposing the cross-commutator as a group relator.  Its current
  `projective-commutant-transfer-for-arithmetic-pair` frontier is therefore a
  genuine possible source, not a consequence of local affine pressure.

The obstruction also survives attaching any independent fixed finite packet:
tensor `(TRP1)` with an exact packet representation and take `Q` inside a
packet spectral projection tensored with the full two-reflection factor.
Thus packet exactification which does not contain a mixed relation or a
matrix-only global transfer cannot help.  If the mixed commutation is instead
imposed as an ordinary group relator, the HNN commutator word ceases to be
Britton-wandering.  The only surviving input is consequently a genuinely
finite-matrix-only global alignment theorem.

