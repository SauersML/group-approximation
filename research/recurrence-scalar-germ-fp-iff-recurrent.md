---
rg: 2
id: recurrence-scalar-germ-fp-iff-recurrent
kind: claim
root: true
title: A finitely generated scalar shift germ group is finitely presented exactly when its integer tail profiles are eventually recurrent
distinct_from:
  block-power-germ-schedules-with-fp-germ-group-are-exponential: that supplies only a necessary recurrence and exponential-growth condition for block-power germs; this is an exact equivalence including finite rational rank and type F_infinity for finitely many eventually integral profiles.
artifacts:
  - research/artifacts/beyond-polynomial-germs/recurrence-and-matrix-proofs.md
---

Let `f₁,…,f_s` be finitely many eventually integer-valued one-sided
profiles, modulo eventual equality. Let `σf(n)=f(n+1)`, let `M` be the
additive span of `1` and all positive and negative shifts of the profiles,
and put `J=M⋊_σℤ`. The following are equivalent:

1. Every profile eventually satisfies a homogeneous constant-coefficient
   rational recurrence.
2. `dim_ℚ(M⊗ℚ)<∞`.
3. `J` is finitely presented.
4. `J` is of type `F_∞`.

The forward integral lattice map need only be injective. There is no
unit-endpoint or surjectivity requirement; `1,a^n` gives
`J≅ℤ×BS(1,a)` for `a≥2`. In the arithmetic realization
`R_f(y)=q^(f(ν_p(y)))y`, this is the actual scalar germ group generated
by the radial profiles and p-zoom.

## Attempts

Sections 1–4 of the artifact reconstruct the third supplied manuscript.
The forward direction embeds the span of forward integral solution tails
in `ℤ^d` and constructs an injective ascending HNN extension. The reverse
direction expresses `J` as a direct limit of finite-window abelian HNN
groups, uses finite presentation to stabilize a window, and uses Britton's
lemma to force an ascending orientation. Both substantive assertions are
explicit unresolved prerequisites. No empty-prerequisite proof route,
Lean certificate or independent referee approval is supplied here.
