---
rg: 2
id: affine-safe-support-admits-a-tailored-rstar-cap-pp-lift
kind: claim
title: Affine safety is exactly sufficient for a support-tailored R-star cap pp lift
distinct_from:
  fano-cap-witness-sections-force-source-affine-safety: that proves necessity for every fixed pp gadget; this proves sufficiency by choosing a new gadget tailored to the affine hull of the positive source support.
  source-affine-safety-does-not-imply-rstar-profile-compatibility: that fixes one three-row gadget whose profile cover misses an affine support; this changes the pp presentation while preserving its full visible relation.
  rstar-core-character-profiles-induce-an-exact-affine-cover: that classifies the profile pieces of a fixed gadget; this constructs a gadget whose cover contains the prescribed affine piece.
  boolean-relations-have-affine-complete-rstar-pp-gadgets: that uses all nonzero characters in one relation-dependent gadget and therefore does not need the positive support when constructing it; this is its one-support precursor.
---

**ESTABLISHED TAILORED-LIFT EQUIVALENCE.**  Let `C subseteq F_2^n` be a
nonempty Boolean relation and let `S subseteq C` be nonempty.  There exists
a finite pp gadget over

```text
R_*={x in F_2^4 : x_1+x_2+x_3+x_4=1} minus {1000}       (TAL1)
```

whose visible projection is exactly `C` and which admits a deterministic
witness section on `S` having cap range in every target row if and only if

```text
Aff(S) subseteq C.                                      (TAL2)
```

The gadget can be chosen with size depending only on `n`.  If `S` is the
positive joint spectral support of a perfect commuting source context, the
section is realized by affine functional calculus in that same abelian
von Neumann algebra.  It therefore preserves the trace and Connes
embeddability and changes no visible overlap.

The forward implication is
`fano-cap-witness-sections-force-source-affine-safety`.  For the converse,
put `A=Aff(S)`.  The construction below defines all of `C`, not merely `A`,
but protects `A` by a cap-valued branch in every clause.

## Protected forbidden-point clause

Fix `b notin C` and translate `u=x+b`, so the one assignment to exclude is
`u=0`.  Since the affine space `A+b` does not contain zero, write
`A+b=a+V` with `a notin V` and choose a linear functional `lambda` such that

```text
lambda(V)=0,          lambda(a)=1.                       (TAL3)
```

Introduce `s=lambda(u)`.  The clause

```text
s OR u_1 OR ... OR u_n                                 (TAL4)
```

is equivalent to `u!=0`: it fails at zero, while every nonzero `u` already
has a true coordinate.  On the protected affine space `A+b`, however,
`s=1` identically.

Compile the translations and `(TAL3)` by affine xor rows.  Convert `(TAL4)`
to the standard 3-CNF chain

```text
(s OR u_1 OR y_1),
((NOT y_1) OR u_2 OR y_2), ...,
((NOT y_k) OR u_(n-1) OR u_n).                         (TAL5)
```

On `A+b` choose every chain bit `y_i=0`.  Thus every clause in `(TAL5)` has
one literal identically equal to one.  Negated chain literals and all affine
partial sums are affine functions on `A`.

The exact `R_*` encoding of a ternary OR clause is

```text
OR(a,b,c)       iff       exists t, R_*(t,a,b,c).        (TAL6)
```

Indeed parity determines `t=1+a+b+c`; when `a=b=c=0`
this is the deleted ghost, and otherwise it is an allowed point.  Under the
protected section, `(t,a,b,c)` is an affine function of the point of `A` and
always belongs to `R_*`.  Its range is therefore an affine subset of `R_*`,
hence a Fano cap by `rstar-fano-ghost-affine-hull-criterion`.

For completeness, all affine equations used above have a fixed-cap pp
encoding.  Private variables `z,o` are pinned by

```text
R_*(z,o,o,o),             giving (z,o)=(0,1),            (TAL7)
```

and `R_*(p,q,r,o)` enforces `p+q+r=0`.  These rows all have fourth coordinate
one and hence lie in the maximal cap `x_4=1`.

Finally conjoin the protected clause gadget for every `b notin C`.  Its
visible solutions are exactly the points of `C`.  On `A`, concatenate the
sections supplied above; auxiliary variables are private between forbidden
points, so every target occurrence has cap range simultaneously.  This
proves `(TAL2)`.

For a fixed Culf--Mastel source context, this removes the dense-core
compatibility issue after its positive support is known to be affine-safe.
The stronger
`boolean-relations-have-affine-complete-rstar-pp-gadgets` places
all possible separating characters into one relation-dependent gadget, so
even the pp presentation can be selected uniformly before the support is
known.  The remaining source-trace gate is affine safety itself.
