---
rg: 2
id: two-orientation-hnn-packet-prepays-escape
kind: claim
title: The two-orientation HNN packet has local escape but prepays every reusable level
distinct_from:
  balanced-hnn-conditional-gap-forces-carrier-escape: that proves the abstract conditional-overlap estimate for a globally balanced edge; this computes the proposed controlled-Clifford edge on each primitive orientation and gives its exact finite-depth compensation model.
  finite-packet-flow-keeps-payload-orientation-balanced: that gives the stationary regular profile for arbitrary finite packet diagrams; this shows explicitly how the missing rank-one corner is stored in the sibling rank-three orientation and why fresh primitive cuts consume the entire apparent growth.
  odd-row-unoriented-fine-return-has-quarter-floor: that charges a Whitehead row which returns to the unoriented fine atom; this tests separate HNN letters conjugating the coarse Pauli sign to the two oriented controlled signs.
---

**ESTABLISHED LOCAL ACTUATOR AND FINITE-DEPTH FIREWALL.**  In the marked
spin sector of the controlled Pauli group `G_CZ`, write

```text
e=(1-Z_1)/2,             s=t,
f_+=(1-s)/2,             f_-=(1-Js)/2.                (TOH1)
```

For the two primitive spin types,

```text
s z_+= C z_+,       s z_-=-C z_-,       C=1-2f,

f_+=f z_+ +(1-f)z_-,
f_-=(1-f)z_+ +f z_-.                                  (TOH2)
```

Thus `e` has rank two on either four-dimensional type, whereas the target
has rank one on the named orientation and rank three on its sibling.

Adjoin HNN letters with

```text
U_+ Z_1 U_+^*=s,             U_- Z_1 U_-^*=Js,         (TOH3)
```

and let them centralize a payload group commuting with `G_CZ`.  These are
valid regular-safe HNN edges: `<Z_1>`, `<s>` and `<Js>` are order-two
subgroups, and globally

```text
tau(e)=tau(f_+)=tau(f_-)=1/2.                           (TOH4)
```

The proposed local escape estimate is genuine.  If `Q<=z_+` reduces the
packet and payload, `P` is a payload projection, and

```text
A=QPe,                 D=U_+ A U_+^*,                  (TOH5)
```

then `D<=P f_+` and

```text
tau(QD)<=tau(QP f_+)=tau(A)/2.                         (TOH6)
```

Hence at least half of `A` leaves `Q`.  The identical assertion holds on
`Q<=z_-` with `U_-`.  Fixed-packet exactification and the HNN covariance
estimate make `(TOH6)` robust with `O(sqrt(E_pres))` loss.

This does **not** give escape from the orientation-union carrier needed at
the next BCS step.  On the balanced marked module

```text
V=S_+ direct-sum S_-                                  (TOH7)
```

there are exact unitaries satisfying `(TOH3)` for which

```text
U_+(e z_+)V <= f_+z_- V,
U_-(e z_-)V <= f_-z_+ V.                              (TOH8)
```

Indeed the source in either line has dimension two and the indicated
sibling target has dimension three.  Extend either isometry to a unitary
mapping the full four-dimensional `e`-space onto the corresponding
four-dimensional `f_+`- or `f_-`-space.  Mapping the negative eigenspaces is
equivalent to the required conjugacy.  Thus every apparent primitive-type
exit may land completely in its sibling, and the full balanced carrier has
zero conditional gap.

Fresh packets do not repair this.  For `N` commuting copies sharing `J`, the
exact tensor model `V^(tensor N)` satisfies all packet, payload-centralizer
and HNN relations with each `U_(n,+/-)` acting on its own factor.  A carrier
which is already confined to one primitive type in each of the `N` future
packets has relative trace `2^(-N)`.  After using the `n`th HNN letter, the
packet-reducing hull can fill the sibling irreducible and thereby release at
most the factor two which that primitive cut prepaid.  After `k` levels its
trace may be `2^(k-N)`, and after all `N` levels it is merely the full
balanced carrier.

Equivalently, if future packet orientations are not cut in advance, their
balanced union is already in the parent carrier and `(TOH8)` routes the
putative first-hit exit into a sibling layer of that same parent.  If they
are cut in advance, each reusable level divides the seed by two, while the
local selected-BCS recurrence grows by a factor strictly smaller than two.
No fixed depth can exhaust normalized trace.

The countermodel tensors with any exact finite-dimensional structural BCS
tuple having a positive forbidden atom, so the payload can remain marked
and nonzero while all proposed packet relations are exact.  Therefore the
two HNN orientations are a correct one-use conditional actuator, but not a
compiler into pairwise orthogonal first-hit layers.  A successful version
still needs a relation which prevents the rank-three companion from entering
the sibling reached carrier; that is precisely a payload-conditioned
nonstationary return, not another fresh finite orientation packet.

DERIVATION
two-orientation-hnn-prepaid-escape-proof

