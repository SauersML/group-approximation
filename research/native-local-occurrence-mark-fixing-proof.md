---
rg: 2
id: native-local-occurrence-mark-fixing-proof
kind: route
title: Apply the disjoint-root Steinberg law to the complete native local packet
target: native-local-occurrence-closure-fixes-mark
requires:
  - literal-prefix-coupling-of-j1-j2-has-gl7-model
  - odd-native-s-factor-return-diamond-has-gl7-model
  - native-a1-b2-hecke-triangle-has-gl7-model
  - support-return-gives-gauged-native-loop
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
  - literal-prefix-whitehead-relative-word-fixes-mark
---

For Steinberg roots one has

```text
[x_ij(a),x_kl(b)]=1
```

whenever `j!=k` and `i!=l`.  If `i,j` both lie outside `{1,3}`, these two
inequalities hold for `(k,l)=(1,3)`.  Hence

```text
[x_ij(a),x_13(q)]=1.                                  (1)
```

Inspect the literal indices in the required authenticated tables.  The two
native Whiteheads and their prefix compiler use only `7,8,9`; the returned
diamonds and their opposite Whitehead add only `6`; the Hecke triangles and
support returns add only `2,4,5`; and the common recentering option adds
only `18,19`.  Thus every displayed elementary factor has both indices in

```text
I={2,4,5,6,7,8,9,10,18,19},
```

which is disjoint from `{1,3}`.  Equation `(1)` applies factor by factor.
The marked-overlap double-commutator witnesses with indices `(4,1)` and
`(3,2)` are not factors of either scale transport and are not included in
this transport closure.
The centralizer of `z=x_13(q)` is a subgroup, so it contains every product,
inverse, commutator, Whitehead word, and support-return composite built from
these factors.  This proves `(NLO1)`.

If `g_1,g_2` belong to that subgroup, so does `u=g_1^(-1)g_2`, proving
`(NLO2)`.  Finally, the image of `z` in the elementary-matrix quotient is
`I+qE_13`, whereas the image of a nonzero root in a position disjoint from
`{1,3}` is `I+cE_ab`.  These matrices are unequal, proving incompatibility
with `(NLO3)`.

For the scoped finite escape, take the exact `GL_7(F_2)` occurrence model
from the first required claim and form its direct product with `C_2`.  Put
the marked sign in the second factor and every local occurrence generator
in the first.  The mark survives and is centralized exactly.  This model is
only for the displayed finite occurrence table, as required for the fence;
it is not asserted to represent the full binary-Leavitt Steinberg group.
