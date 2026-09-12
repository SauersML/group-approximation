---
rg: 2
id: bcs-commuting-square-transfer-collapses-britton-commutator
kind: claim
title: The ordinary BCS commuting square collapses the candidate Britton commutator
distinct_from:
  two-reflection-pressure-does-not-force-localized-commutation: that gives a matrix countermodel to obtaining localized commutation from disagreement pressure alone; this identifies the separate syntactic collapse when BCS context commutation and an anchor row are used to obtain it.
  twisted-disagreement-return-factors-through-localized-commutator: that proves localized cross-commutation is sufficient; this audits the most direct private/shared BCS source and shows why making its inputs relators kills the target word.
  fd-invisible-anchor-does-not-localize-bcs-consistency: that tests the intermediate idea of identifying the missing anchor defect with a word killed in every exact finite-dimensional representation, and shows that even positive-density localized collapse still requires new normalized-HS input.
---

Let `a,a_0,b_0,t` be group words and put

```text
c=t^(-1)a t,                 c_0=t^(-1)a_0 t.          (BCS1)
```

The standard private/shared BCS commuting square uses the private context
relation `[a,a_0]=1` and the anchor consistency relation `c_0=b_0`.  These
relations imply

```text
[c,b_0]=1                                                     (BCS2)
```

as an abstract group identity.  Consequently `[t^(-1)a t,b_0]` cannot be
the nontrivial Britton commutator used by
`twisted-disagreement-return-factors-through-localized-commutator`.

There is a dimension-free analytic version.  For unitary matrices `A,A_0,
B_0,T`, set `C=T^*AT` and `C_0=T^*A_0T`.  Then

```text
||[C,B_0]||_2
 <= ||[A,A_0]||_2 + 2||C_0-B_0||_2.                  (BCS3)
```

If a projection `Q` reduces `C`, the localized estimate is

```text
||Q[C,B_0]||_2
 <= ||Q[C,C_0]||_2 + 2||Q(C_0-B_0)||_2.              (BCS4)
```

Thus the private/shared machinery really does have the correct analytic
shape: a context-commutation row plus one anchor-consistency row controls a
cross commutator.  The problem is syntactic, not an estimate.  Making both
rows ordinary relators proves `(BCS2)` in the regular representation and
destroys wandering.  Leaving either row out requires that row to become
small only in finite canonical microstates.  The non-CE BCS energy gap does
not supply such a conclusion: it lower-bounds a sum of predicate,
commutation, and consistency energies, and
`deleting-one-gap-row-has-the-wrong-orientation` shows that deleting a row
can force it to be large rather than small.

The exact tracial standard-form model does not close this gap.  There the
left and right actions and the common modular swap make `(BCS2)` hold
semantically, but `perfect-tracial-bcs-has-one-common-module-swap` explicitly
does not expose that swap in finite ordinary-word microstates.  Conversely,
the finite Bass--Serre models in
`context-local-fanizza-exits-do-not-control-global-leakage` keep every local
row exact while a cross-context commutator stays macroscopically nonzero.

Therefore the minimal surviving compiler is precisely a **matrix-only
commuting square**: on one unnamed positive-density reducing corner, one of
the two inputs in `(BCS4)` must be inferred with `o(1)` defect without being
an abstract group consequence.  Once that is available, the direct Britton
commutator is already terminal; forbidden-mass disagreement and the central
sign add no further leverage.

Exact finite-dimensional invisibility does not provide the omitted input.
`fd-invisible-anchor-does-not-localize-bcs-consistency` tensors a central
invisible involution with an exact two-point packet and obtains a fixed
central reducing carrier of trace `1/2` on which the anchor defect remains
of squared normalized-HS norm `1` in canonical sofic microstates.  Thus even
the localized version of the anchor row is not a formal consequence of its
holding in every honest matrix representation.
