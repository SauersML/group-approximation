---
rg: 2
id: capacity-gated-common-corner-bcs-two-cell
kind: claim
title: One common off-capacity source intertwining every allowed context controls the full localized BCS leakage
distinct_from:
  context-local-fanizza-exits-do-not-control-global-leakage: that gives an exact countermodel when every context owns a different exit carrier; this states the minimal common-source interface which defeats that countermodel.
  corner-localized-non-ce-bcs-energy-gap: that turns a supplied globally reducing BCS-quiet matrix corner into an energy floor; this constructs such a corner quantitatively from context packet intertwiners sharing one source projection.
  shared-bcs-eight-slice-full-overlap-actuator: that asks for the final source-to-capacity scalar overlap; this controls only the off-capacity leakage functional needed to select a positive cross-Gram overlap and does not amplify that overlap to the full source.
  common-source-hnn-bridges-need-one-gram-saturation-identity: that audits ordinary HNN bridges and isolates the single source-Gram estimate required to construct the common-source intertwiners assumed here.
---

Fix the finite shared BCS `B`, with variables `Z_x`, contexts `c`, and
residual list `R_B`.  Let `Q` be one projection in `M_d(C)`.  For every
context `c`, suppose there are

```text
V_c,                    V_c^*V_c=Q,                    (CGC1)
A_(c,x),                x in U_c,                      (CGC2)
```

where `V_c` is a partial isometry and the `A_(c,x)` are contractions.  Think
of the `A_(c,x)` as the exactified allowed context packet on the range of
`V_c`.  Define the covariance and target-context energy

```text
D_(c,x)=A_(c,x)V_c-V_cZ_x,

E_cov=sum_c sum_(x in U_c)||D_(c,x)||_2^2,
E_tar=sum_c sum_(R belonging to c)||R(A_c)V_c||_2^2.   (CGC3)
```

Here each fixed residual is evaluated in its owning context; an involution
residual may be assigned to any incident context.  Then there is a constant
`K_B`, depending only on the finite BCS, such that

```text
sum_x||[Q,Z_x]||_2^2
 +sum_(R in R_B)||R(Z)Q||_2^2
 <=K_B(E_cov+E_tar).                                   (CGC4)
```

This is the exact analytic form of the mixed two-cell missing from
`(NCL13)`.

## Proof

Fix one incidence `(c,x)` and abbreviate `A=A_(c,x)`, `V=V_c`, `Z=Z_x`,
and `D=AV-VZ`.  Since `V^*V=Q`,

```text
V^*D=V^*AV-QZ,
D^*V=V^*A^*V-Z^*Q.                                    (CGC5)
```

When the packet variables and shared variables have been involution-rounded,
`A=A^*` and `Z=Z^*`.  Therefore

```text
||[Q,Z]||_2<=2||D||_2.                                 (CGC6)
```

The same estimate holds with the fixed rounding errors added if the
involutions are only approximate.

For a monomial `W=Z_(x_1)...Z_(x_k)` in context `c`, repeatedly insert
`VZ_x=A_(c,x)V-D_(c,x)` to obtain

```text
||VW(Z)-W(A_c)V||_2
 <=sum_(j=1)^k||D_(c,x_j)||_2.                         (CGC7)
```

Every factor is a contraction, so there is no dimension or multiplicity
loss.  Fixed coefficient and word-length bounds give, for every residual
`R` of `c`,

```text
||V R(Z)Q||_2
 <=||R(A_c)V||_2+K_R(sum_(x in U_c)||D_(c,x)||_2^2)^(1/2).
                                                               (CGC8)
```

The left side is `||Q R(Z)Q||_2`.  The missing off-diagonal part of
`R(Z)Q` is controlled by `[Q,R(Z)]`, and fixed-word telescoping together
with `(CGC6)` gives

```text
||(1-Q)R(Z)Q||_2
 <=K'_R(sum_(x in U_c)||D_(c,x)||_2^2)^(1/2).          (CGC9)
```

Combining `(CGC8)--(CGC9)`, squaring, and summing the fixed finite list proves
`(CGC4)`.

## Application to the off-capacity exits

For the exits of `localized-non-ce-leakage-forces-cross-gram-overlap`, take

```text
Q=L_i=(1-C)E_i.                                        (CGC10)
```

If one family `(V_(i,c))_c` satisfies `(CGC1)--(CGC3)` with this **same**
source `L_i` for every context, then `(CGC4)` gives

```text
Lambda_i<=K_B(E_cov,i+E_tar,i).                        (CGC11)
```

Thus `(NCL13)` follows as soon as the named actuator relators bound the sum
of the common-source covariance and target-context packet energies by
`E_rel`.  No additional compactness or Gram estimate is needed at this
stage.

Using one projection `Q_(i,c)` per context is invalid.  The Bass--Serre
countermodel in `context-local-fanizza-exits-do-not-control-global-leakage`
rotates those private sources independently.  The load-bearing datum in
`(CGC1)` is not merely shared variable names; it is literal equality of the
source projection on the multiplicity space before the contexts split.

## Regular-trace and exact-witness audit

This interface does not assert a universal tracial inequality killing `Q`.
If `B` has an exact non-Connes-embeddable tracial representation `pi`, take

```text
Q=I,
V_c=I,
A_(c,x)=pi(Z_x).                                       (CGC12)
```

All terms in `(CGC3)--(CGC4)` vanish.  Hence the common-corner two-cell is
perfectly compatible with an exact non-CE tracial model and cannot be
rejected by the regular-representation firewall.  It becomes obstructive
only after `corner-localized-non-ce-bcs-energy-gap` is applied to matrices or
a tracial matrix ultraproduct.

For the Fanizza HALT completeness witness there is an even cheaper
extension.  Every forbidden source projection vanishes in the perfect BCS
model, so `E_i=L_i=0`; choose `V_(i,c)=0`.  The common-source clauses are
then exact.  Countable amplification may be used for the remaining packet
and actuator relations.  Thus the proposed interface does not impose a
finite or tracial extension on the HALT-side groupifier.

## Remaining group-word construction

The two-cell is deliberately stated after packet compression.  Ordinary
group generators are invertible and cannot literally be the `V_c` when
`Q<1`.  A valid construction must decode the `V_c` as fixed Hecke/packet
blocks of unitary words and make their source Gram projections agree with
the single analytic projection `(1-C)E_i`.  Finite vertex/edge restriction
tables do not do this: they align representation types but leave independent
multiplicity unitaries.  The new finite construction target is therefore:

```text
one capacity-gated source Gram moment
  + one context intertwiner row for each of the four native contexts
  + one two-cell identifying all source Gram projections.             (CGC13)
```

For the native Fanizza incidence this is a fixed finite object: the only
cycle is the `C_Z-C_D-C_R` triangle and `C_X` is one attached leaf.  The leaf
must be included in the source-Gram two-cell; transporting only the three
triangle separators leaves the exact countermodel `(CFL11)` untouched.

`common-source-hnn-bridges-need-one-gram-saturation-identity` proves that
ordinary context HNN edges do not identify these source projections.  Their
precise missing scalar is the saturation deficit
`sum_c||(1-p_c)U_cQ||_2^2`; countable amplification makes that identity
compatible with the exact witness, while finite selector induction prevents
it from following from the edge restriction tables alone.
