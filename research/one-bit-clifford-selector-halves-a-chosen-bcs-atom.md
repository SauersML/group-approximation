---
rg: 2
id: one-bit-clifford-selector-halves-a-chosen-bcs-atom
kind: claim
title: A two-involution Clifford selector cuts a canonical half from any chosen BCS assignment atom
distinct_from:
  schur-pauli-words-name-atomwise-half-quarter-flags: That extracts relative Pauli flags from the full Schur predicate packet; this is a smaller standalone ordinary-group gadget attached to one already named context atom.
  central-sign-bcs-atoms-are-subgroup-reynolds-projections: That names the whole assignment atom as a Reynolds projection; this adjoins a conditional Pauli pair whose spectral cut has exactly half of that atom's trace.
---

**ESTABLISHED.**  Let `J` and the shared BCS variables `x_v` be involutions,
with `J` central, and use Boolean convention

```text
x_v=(-1)^(a(v))
```

on the context assignment atom `P_(c,a)`.  Choose one `v_0 in c`.  Adjoin
involutions `p_(c,a),q_(c,a)` satisfying

```text
[p_(c,a),J]=[q_(c,a),J]=1,
[p_(c,a),x_v]=[q_(c,a),x_v]=1       (v in c),
[p_(c,a),q_(c,a)]=J^(1-a(v_0)) x_(v_0).                (OCS1)
```

On the marked `J=-1` assignment atom the right side of `(OCS1)` is `-1`.
Thus the two selector involutions anticommute there.  If `Q<=Q_-=(1-J)/2`
reduces the context tuple and the selectors, put

```text
E_(c,a)=Q P_(c,a),
R_(c,a)=(1+p_(c,a))/2,
A_(c,a)=E_(c,a)R_(c,a).                                (OCS2)
```

Conjugation by `q_(c,a)` exchanges the two `p_(c,a)` spectral halves while
fixing `E_(c,a)`.  Hence

```text
tau(A_(c,a))=tau(E_(c,a))/2.                            (OCS3)
```

For a fixed finite BCS menu, approximate involution, context-commutation,
and selector relations can be rounded locally on `Q`; the trace form of the
same conjugacy calculation gives

```text
|tau(Ahat_(c,a))-tau(QP_(c,a))/2|<=C_sel sqrt(E),        (OCS4)
```

with `C_sel` independent of matrix dimension.  Local rounding may be done
separately for each context because `(OCS4)` is only a scalar selection
estimate; it does not assert a simultaneous exactification of the shared BCS.

The gadget is consistent with the perfect tracial BCS model.  Put `J=-1`,
let `z=J^(1-a(v_0))x_(v_0)`, `e_+=(1+z)/2`, `e_-=(1-z)/2`, and on a fresh
`M_2` factor set

```text
p=1 tensor Z,
q=e_+ tensor 1+e_- tensor X.                            (OCS5)
```

Then `p,q` are involutions, commute with the context variables, and
`[p,q]=z`.  Separate tensor factors realize the finite family of selector
gadgets simultaneously.  Every forbidden `P_(c,a)` is zero in the perfect
model, so all selected pieces vanish there.

The selected half is not merely a spectral polynomial.
`clifford-selected-half-is-an-index-two-reynolds-surplus` identifies it with
the difference of two explicit finite-subgroup Reynolds projections.  Hence
local subgroup-HNN transport is already available whenever a later cell
really needs the balanced half.
