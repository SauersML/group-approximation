---
rg: 2
id: tagged-shift-shear-has-unbounded-fixed-mark-area
kind: claim
title: The tagged coefficient shear gives an exact two-diagonal edge identity but not a uniform fixed-mark cell
distinct_from:
  tagged-shift-stabilizer-normalization-has-unbounded-row-holonomy: that rules out simultaneous pair charts by two endpoint row holonomies; this tests a non-chart commutator cancellation using one explicit coefficient shear and finds the obstruction in its fixed-mark centralizer area.
  binary-leavitt-tagged-shift-table-has-centralizer-collisions: that exact table remains a viable algebraic escape from the fixed-column fence; this rules out only the natural two-diagonal shear filling, not arbitrary diagrams for its edge commutators.
artifacts:
  - research/binary-leavitt-bounded-area-chromatic-code.md
---

**ESTABLISHED EXACT SHEAR; UNIFORM SAME-MARK CELL IMPOSSIBLE.**  Retain the
tagged-table notation

```text
A_rB_s=delta_(rs)q,             A_rD_(ij)=0,
c_r=x_12(A_r),                  h_(ij)=x_23(B_i+D_(ij)),
z=x_13(q).                                                   (TSC1)
```

For `i!=j`, put

```text
N_(ij)=B_iA_j,                  u_(ij)=1+N_(ij).             (TSC2)
```

In characteristic two, `N_(ij)^2=0`, so `u_(ij)^(-1)=u_(ij)`.  Moreover

```text
A_i u_(ij)=A_i+A_j,
A_j u_(ij)=A_j,
u_(ij)(B_i+D_(ij))=B_i+D_(ij).                              (TSC3)
```

Let `r_(ij)` be any Steinberg lift of
`diag(1,u_(ij),1)` in the three displayed matrix coordinates.  Conjugation
therefore gives the exact group identities

```text
r_(ij)c_i r_(ij)^(-1)=c_ic_j,
[r_(ij),c_j]=[r_(ij),h_(ij)]=[r_(ij),z]=1.                 (TSC4)
```

This produces a genuine non-chart two-diagonal cancellation.  For arbitrary
group words `a,b,h,z`, define

```text
delta_0=[a,h]z^(-1),             delta_1=[ab,h]z^(-1).
```

The elementary identity `[ab,h]=a[b,h]a^(-1)[a,h]` gives

```text
[b,h]=a^(-1) delta_1 delta_0^(-1) a.                      (TSC5)
```

Thus, with `a=c_i` and `b=c_j`, uniformly bounded fillings of the ordinary
and sheared diagonal discrepancies would give a two-cell uniform filling of
the tagged edge.  Algebraically both diagonals equal the same `z`, because
`A_i(B_i+D_(ij))=(A_i+A_j)(B_i+D_(ij))=q`.

The natural plan to obtain the sheared diagonal by conjugating the ordinary
one cannot have uniform area.  To turn the conjugate mark
`r_(ij) z r_(ij)^(-1)` back into the literal fixed word `z`, the shear cell
must pay

```text
Area([r_(ij),z]).                                          (TSC6)
```

The elements `r_(ij)` all centralize the same nontrivial involution `z`, and
an infinite subfamily occupies distinct cosets modulo `<z>`.  Therefore
`finite-mark-centralizer-commutator-area-is-proper` forces the quantities in
`(TSC6)` to be unbounded, for every choice of words representing the lifts.
In particular no bounded list of mixed-root, opposite-root, or Whitehead
prototype cells can make this shear a uniform **same-mark conjugacy** from
`delta_0` to `delta_1`.

This does not prove that the sheared diagonal discrepancies themselves have
unbounded area by every possible diagram.  A direct diagram for `delta_1`
which does not compare it to `r_(ij)delta_0r_(ij)^(-1)` would evade `(TSC6)`
and remains open, as does a direct non-shear filling of `[c_j,h_(ij)]`.

No Property `(T)`, Kazhdan input, matrix approximation, trace, or literature
theorem is used.

DERIVATION
binary-leavitt-tagged-shear-centralizer-proof
