---
rg: 2
id: amenable-base-mikhailova-co-amenable-proof
kind: route
title: Pull back the invariant mean, exhibit the diagonal free group, and quote Mikhailova
target: amenable-base-makes-mikhailova-edge-co-amenable
requires:
  - mikhailova-coset-action-is-two-sided-q-action
---

Write `H = F x F`, `M = M_Q`, `X = H/M`.

## Co-amenable

By [[mikhailova-coset-action-is-two-sided-q-action]], `X ~= Q` as an `H`-set,
with `H` acting through `phi x phi : H -> Q x Q` by the two-sided translation
action of `Q x Q` on `Q`.  `Q` amenable implies `Q x Q` amenable, so there is a
`(Q x Q)`-invariant mean `m` on `ell^infinity(Q)` (a left-and-right invariant
mean on `Q`, which exists exactly because `Q` is amenable).  Pulling back along
`phi x phi`, `m` is `H`-invariant on `ell^infinity(X)`.  An `H`-invariant mean
on `ell^infinity(H/M)` is precisely co-amenability of `M` in `H`.

## Non-amenable

The diagonal `Delta = {(u,u) : u in F}` satisfies `phi(u) =_Q phi(u)`, so
`Delta <= M`.  `Delta ~= F` is a nonabelian free group (once `|X| >= 2`), hence
non-amenable, so `M` is non-amenable.

## Non-separable

Mikhailova: if `Q = <X | R>` has unsolvable word problem then membership in
`M = {(u,v) : u =_Q v}` is undecidable, so `M` is not separable in `H` (a
separable finitely generated subgroup of a finitely presented group has
decidable membership: non-membership is certified by a finite quotient and
membership is recursively enumerable, so both sides would be r.e.).  Finitely
presented amenable groups with unsolvable word problem exist (Kharlampovich,
1981), so this case is nonempty.  `∎`

## Remark

Co-amenable and non-amenable are compatible because `H = F x F` is itself
non-amenable; co-amenability of `M` says only that `H/M` carries an invariant
mean, which the two-sided action of the amenable `Q` supplies.  The three
properties pull in different directions: co-amenability is what makes the lamp
index space carry Følner sets (good for approximation), while non-separability
is what makes the centralizing HNN fail to be residually finite (the reason the
compiler needs it).
