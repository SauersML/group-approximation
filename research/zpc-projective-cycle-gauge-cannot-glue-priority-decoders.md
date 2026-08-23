---
rg: 2
id: zpc-projective-cycle-gauge-cannot-glue-priority-decoders
kind: claim
title: Projective cycle holonomy cannot glue priority-decoded ZPC context copies
distinct_from:
  priority-decoded-contexts-are-not-glued-by-raw-gate-equality: that gives a mismatch with no transport or projective phase gadget; this gives exact covariance transports and a genuinely noncommutative central-sign commutator around two cycles.
  selector-gated-equality-is-not-affine-pp-definable: that is a scalar affine definability obstruction; this is a matrix gauge obstruction for noncommuting projective cycle words and has an exact marked central-sign model.
  existential-cycle-gauge-absorbs-square-and-reynolds-readouts: that treats equal finite-packet types and free commutant returns; this identifies the independent VERTEX gauge of decoded context copies and shows that even noncommuting Pauli cycle curvature does not control their literal mismatch.
---

**ESTABLISHED NO-GO for pure cycle gadgets.**  Consider a finite connected
graph of local predication contexts.  Suppose its extra gluing letters are
edge transporters `T_e` and its gluing relations consist of

```text
T_e U_(s(e)) T_e^* = U_(t(e))                           (ZCG1)
```

for the priority-decoded unreadable involutions, together with projective
central-sign relations on products of the `T_e` around cycles.  If those
cycle relations depend only on the return words and central letters, then
they cannot imply a dimension-free estimate of literal decoded mismatch.

The reason is an exact vertex-gauge symmetry.  For arbitrary local unitaries
`S_c`, replace

```text
U_c |-> S_c U_c S_c^*,
T_e |-> S_(t(e)) T_e S_(s(e))^*.                        (ZCG2)
```

All edge covariance relations are unchanged.  Every based cycle return is
merely conjugated by the gauge at its base vertex, so every group word
relation and every central phase relation on returns is unchanged.  However
`||U_c-U_d||_2` in the common ambient identification is not gauge invariant.
Cycle curvature can constrain chord holonomy after a spanning-tree gauge has
been chosen; it cannot choose the spanning-tree gauge itself.

This remains true for any finite projective cycle packet, not just a square
or commutator.  After transporting along a spanning tree, its return words
act in the commutant of the base decoded overlap.  If the packet has a
finite-dimensional representation with its marked central involution equal
to `-I`, amplify every context by that representation and put the packet
there.  The local decoded operators are untouched.  Thus a
completeness-preserving projective return packet can be tensored onto every
unitarily transportable bad local family.

## Sharp central-sign countermodel

The failure already occurs in dimension four.  On

```text
H=C^2_(payload) tensor C^2_(cycle)
```

write `X,Z` for the Pauli involutions and set

```text
U_c= Z tensor I,                U_d=-Z tensor I.         (ZCG3)
```

Use exact singleton priority sectors in the two contexts:

```text
(Z_(c,1),Z_(c,2))=(-I,+I),
(Z_(d,1),Z_(d,2))=(+I,-I).                              (ZCG4)
```

Both selector products are `-I`; priority decoding chooses branch `1` at
`c` and branch `2` at `d`.  Choose the active predicated gates to be the two
operators in `(ZCG3)` and all inactive predicated gates to be `I`.  Every
within-context selector, parity, commutation, and canonical predication
identity is exact.

Join the two contexts by three parallel covariance edges with transporters

```text
T_0=X tensor I,       T_1=X tensor X,       T_2=X tensor Z. (ZCG5)
```

Each one satisfies `T_j U_c T_j^*=U_d`.  Relative to the tree edge `T_0`,
the two fundamental cycle returns are

```text
V_1=T_0^*T_1=I tensor X,
V_2=T_0^*T_2=I tensor Z,
[V_1,V_2]=-I=:J.                                      (ZCG6)
```

Hence the edge covariances, the noncommutative projective commutator, and the
marked central-sign equation `[V_1,V_2]=J=-I` all have zero defect.  Yet

```text
||U_c-U_d||_2^2=4.                                     (ZCG7)
```

Tensoring the construction by `I_m` gives the same zero loss and mismatch in
every dimension `4m`.  Therefore no inequality

```text
D_glue <= C times (edge covariance loss + projective cycle loss)
```

can hold with any finite `C` for this class of gadgets.

The no-go does not refute a selector--payload incidence that fixes a vertex
gauge by comparing named raw coefficients in one common context.  Such a
relation is not a pure projective cycle readout: it is exactly the matched
selector/raw-gate alignment hypothesis already sufficient in
`priority-decoder-lipschitz-under-selector-gate-alignment`.  Thus the central
sign escape in `zpc-context-mismatch-transducer` is closed unless the gadget
directly authenticates a payload coefficient or a proper selected corner.

