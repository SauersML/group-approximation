---
rg: 2
id: universal-block-return-violates-the-regular-firewall
kind: claim
title: A fixed group-algebra block linearization cannot be the trace-cyclic return cell
distinct_from:
  regular-trace-blocks-exact-local-predicate-return: that treats forbidden Boolean atoms and arbitrary exact tracial payments; this directly audits the two cyclic products required by the single-triangle actuator, including matrix block and Steinberg linearizations.
  trace-cyclic-rank-mismatch-checksum: that proves the desired finite-matrix scalar checksum once two returned products are decoded; this proves that those products cannot be fixed universal group-algebra identities.
  single-triangle-trace-cyclic-return-cell: that permits a genuinely finite-dimensional-only decoder; this rules out the tempting functorial implementations but does not rule out such a decoder.
---

Let `Gamma` be a group and let `E,H,X,Y` be fixed matrices over
`C[Gamma]`, with `E,H,E-H` projections in the left regular representation
and `0!=H<=E`.  There cannot be universal identities

```text
YX=E,                    XY=E-H                         (UBR1)
```

in every unitary representation of `Gamma`.  More generally, there cannot
be a tracially functorial estimate

```text
|tau(YX)-tau(E)|+|tau(XY)-tau(E-H)| <= omega(def),     (UBR2)
```

with `omega(0)=0`, valid for every finite tracial representation of the
presentation, including matrix amplifications.

Indeed, apply `(UBR1)` or `(UBR2)` at zero defect in
`M_n(L(Gamma))`.  Cyclicity gives

```text
tau(YX)=tau(XY),
```

and hence `tau(H)=0`.  Faithfulness of the canonical trace on the positive
projection `H` gives `H=0`, a contradiction.

Therefore none of the following can close the single-triangle actuator by
itself:

- a Julia/block-unitary dilation whose block equations are consequences of
  the group relators;
- a Steinberg matrix linearization which yields the two products as fixed
  group-algebra identities;
- a literal Toeplitz/Cuntz proper-corner relation; or
- fixed finite-packet exactification followed only by operations valid in
  arbitrary finite tracial von Neumann algebras.

## The stabilized Halmos proper-corner specialization

This firewall applies exactly, not just abstractly, to the stabilized
Leavitt/Morita dilation.  In a ring with

```text
ts=1,               p=st,               e=1-p,
```

put

```text
U=[s e; 0 t],       V=[t 0; e s],       Q=[1 0; 0 0].   (UBR3)
```

Direct multiplication gives `UV=VU=1` and

```text
U Q V=R=[p 0; 0 0] <= Q,        Q-R=[e 0; 0 0].         (UBR4)
```

Thus the Halmos stabilization really does turn the nonunital full-corner
map into conjugation by one invertible matrix.  However, suppose an ordinary
group-word compiler exposed `U,Q,R` as fixed matrices over `C[Gamma]`, with
`U` unitary in every unitary representation and `(UBR4)` following from the
group relators.  In `M_k(L(Gamma))`, cyclicity gives

```text
tau(R)=tau(U Q U*)=tau(Q).
```

Since `R<=Q`, faithfulness gives `Q-R=0`.  The left regular representation is
faithful on `M_k(C[Gamma])`, so the exit coefficient `e` is zero algebraically,
not merely in finite-dimensional representations.  Every representation,
including the proposed properly infinite marked model, therefore loses that
exit.  Stabilization changes neither the argument nor its constant.

There is a sharp amplification-stable approximate version once packet
localization has produced actual projections `Q,R` and a unitary `W`.  Set

```text
delta_c=||R-WQW*||_2,          delta_i=||R-RQ||_2.
```

Then

```text
tau(Q(1-R)Q)
 =tau(Q)-tau(QR)
 <= |tau(Q)-tau(R)|+|tau(R)-tau(RQ)|
 <= delta_c+delta_i.                                      (UBR5)
```

Both defects and the trace in `(UBR5)` are unchanged by common matrix
amplification.  Hence finite-matrix trace cyclicity would provide exactly the
wanted positive exit payment **if** the fixed group words supplied the
conjugacy and containment.  But if both are universal consequences of the
presentation, their zero-defect version is `(UBR4)` in the regular factor and
collapses the marked exit universally.  A surviving construction must make
at least the containment/localization inference genuinely matrix-only; the
Halmos unitary itself does not do that.

The exact HALT Hilbert-hotel representation is consistent only if the return
estimate is obtained by a step that is unavailable in `L(Gamma)`.  Thus at
least one load-bearing inference must use finite matrix coordinates: integer
multiplicity, finite rank, determinant on an extensive family of bounded
blocks, or an equivalent non-tracial-functorial compactness failure.  A
fixed block linearization does not provide that inference; it merely hides
the regular-representation contradiction in notation.
