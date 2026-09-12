---
rg: 2
id: mixed-whitehead-cell-moves-signed-source
kind: claim
title: The shortest mixed Whitehead transports the two-scale cell but moves its signed source
artifacts:
  - research/mixed-whitehead-cell-source-fence-proof.md
  - experiments/fixed_q_two_scale_mixed_relation_audit.py
distinct_from:
  positive-signed-actor-two-scale-profile-is-partial-and-gauged: that finds the fixed-Q actor g-star and leaves its two cell gauges independent; this adds the natural ordinary word conjugating the complete first cell to the second.
  endpoint-whitehead-signed-source-has-only-relative-hecke-overlap: that moves one endpoint against a spare coordinate and computes an endpoint-isolating intersection; this simultaneously moves the endpoint and middle coordinates of the concrete depth-two/depth-three cell.
  endpoint-detector-cell-retains-coboundary-gauge: that transports a root-free depth-three detector cell around a three-endpoint profile; this treats the non-root-free g-star cell and the single depth-two-to-three mixed swap.
  external-normalizer-dressed-cell-has-full-gauged-gram: that constructs a second transport by dressing this word with the unique external signed-normalizer centralizer and computes its full relative Gram; this stops at the first transport.
---

**ESTABLISHED MIXED-RELATION SOURCE FENCE.**  Put

```text
c_2=s_000t_00,                  d_2=s_00t_000,
P=x_42(c_2)x_24(d_2)x_42(c_2),
J=x_98(c_2)x_89(d_2)x_98(c_2),
H=PJ.                                                    (SMP1)
```

Here `P` is the fresh endpoint Whitehead from actor endpoint `2` to `4`,
while `J` is the actual native prefix Whitehead from middle coordinate `8`
to `9`.  The two factors commute.  For

```text
g_*=x_28(1)x_49(1)
```

the faithful coefficient calculation gives the exact ordinary relations

```text
H^2=1,                      Hg_*H=g_*,
HY_2H=Y_3,                  HA_(2,2)H=A_(4,3).          (SMP2)
```

Thus `H` conjugates the complete depth-two nested mark-return cell in
`(PSA4)` to the depth-three cell.  This is the shortest natural mixed
prefix/endpoint relation, and it genuinely ties the two global occurrences.

It does not tie their restrictions to the original signed source.  The word
`H` does not normalize `(L_0,lambda_0)`; only three of the ten displayed
generators even remain constant actor-supported after conjugation.  Exact
intersection gives

```text
K=L_0 intersect HL_0H,          |K|=16,
HkH=k for k in K,               lambda_0|K has signs 8/8. (SMP3)
```

The two characters agree on `K`.  Consequently the canonical regular Hecke
coefficient is

```text
tau(QHQH)=tau(Q)/512.                                  (SMP4)
```

This is not an arbitrary-profile common-source floor.  There are `32`
characters of `L_0` trivial on `K`; for example the character negative only
on the generator `5->4` is trivial there.  The corresponding exact
two-character signed-source profile has

```text
Q perpendicular to HQH.                               (SMP5)
```

In that profile `(SMP2)` compares the depth-two cell on `Q` with the
depth-three cell on `HQH`, not with the depth-three cell on `Q`.

The remaining short relations add no fixed-frame information.  The pairs
`Y_2,Y_3`, `A_(2,2),A_(4,3)` and both opposite cross pairs commute.  Their
common-tail products are merely swapped or fixed by `H`.  Multiplication of
`H` by `L_0`, or by any constant signed normalizer, cannot return the source:
the signed normalizer is a subgroup containing `L_0`, while `H` lies outside
it.  Applying `H` twice only gives the tautological inverse return.

Equivalently, double the scoped occurrence packet into the two charts
`Q,HQH`.  Let `H` swap the charts and interchange the two cells.  On the
`Q` chart the two edge gauges may be arbitrary commuting involutions
`D_2,D_3`; on the other chart use them in the reversed order.  All equations
`(SMP2)` and all four cross commutators remain exact, while no operator
preserving `Q` conjugates `D_2` to `D_3`.  This is an exact finite profile
countermodel to fixed-source gauge locking, not a representation of the
full Steinberg group.

The mixed word therefore closes the global occurrence-conjugacy question
but not the MF source/range Gram seam.  A further ordinary relation must
return `HQH` to `Q` on positive mass without being the inverse move.  No
Property `(T)`, canonical-trace hypothesis for the MF model, literature
input, local computation, or Lean compilation is used.

A nontrivial second transport now exists, but it confirms rather than removes
this source fence.  `external-normalizer-dressed-cell-has-full-gauged-gram`
uses `H'=Hx_59(1)`.  The external root centralizes the whole depth-two cell
and normalizes the signed pair, so the relative loop is a genuine nonidentity
normalizer.  Both transports still go from `Q` onto the same moved `Q'`, and
their cross Gram is the full unitary `x_59(1)Q` carrying the uncontrolled
external multiplicity involution.  Thus the second edge adds no return from
`Q'` to `Q` and no proper range.

DERIVATION
mixed-whitehead-cell-source-fence-proof
