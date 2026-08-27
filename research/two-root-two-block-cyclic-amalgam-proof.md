---
rg: 2
id: two-root-two-block-cyclic-amalgam-proof
kind: route
title: Substitute y equals t-s and compute the adjacent-root order
target: two-root-two-block-kl-word-is-cyclic-amalgam
requires:
  - full-leavitt-idempotent-defect-saturation
  - leavitt-gl-equals-el-and-perfect-unit-group
  - leavitt-unit-group-has-no-finite-normal-subgroup
---

The machine-checked theorem
`HilbertHotel.normalClosure_elementaryRoot_eq_top` says every nonzero
elementary root in rank at least five normally generates `EL_n(R)`.  Hence the
two displayed roots, transported through `EL_20(R) ~= G`, are nontrivial
normal generators.  Characteristic two makes each an involution.

In the standard three-by-three corner write `r=I+E_12`, `s=I+E_23`.  Then

```text
rs=I+E_12+E_23+E_13,
(rs)^2=I+E_13 != I,
(rs)^4=I.
```

Thus `c=rs` has order exactly four.

In the relative presentation set `y=ts`; since `s^2=1`, this is an invertible
Tietze change with `t=ys`.  The relator becomes

```text
r t s t = r (ts)t = r y(ys)=r y^2 s.
```

Therefore `w=1` is equivalent to `y^2=rs=c`.  If
`C_8=<y | y^8=1>`, its square has order four, and the normal-form theorem for
amalgamated products gives

```text
<G,y | y^2=c> ~= G *_(<c>=<y^2>) C_8.
```

This proves the first isomorphism in `(RTB1)` and embeds `G`.

The degree map sends `G` to zero and `y=ts` to one modulo two.  Its index-two
kernel has two `G` vertices, one `C_4=<y^2>` vertex, and two edge groups
`C_4`; collapsing the middle vertex yields `G *_<c> G`, exactly as in the
one-root square calculation.  It is infinite, perfect, nonsolvable, and has
no finite quotient: the vertex copies of `G` embed, are perfect, and admit no
finite quotient.  Hence this is an explicit obstruction quotient, completing
the proof.

