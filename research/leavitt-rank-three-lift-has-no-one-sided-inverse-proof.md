---
rg: 2
id: leavitt-rank-three-lift-has-no-one-sided-inverse-proof
kind: route
title: The support generates a virtually free group, so the partner collapses into it
target: leavitt-rank-three-lift-has-no-one-sided-inverse
requires:
  - leavitt-rank-three-support-group-is-virtually-free
  - subgroup-supported-one-sided-inverse-rigidity
  - binary-leavitt-algebra-not-directly-finite
artifacts:
  - research/artifacts/leavitt-rank-three-no-inverse-2026-08-18.md
---

## Why sufficient

**`t_0` and `s_0` are not units of `R`.**  The third prerequisite gives
`t_0s_0 = 1 != s_0t_0`.  If `c` were a two-sided inverse of `t_0`, then
`c = c(t_0s_0) = (ct_0)s_0 = s_0` and hence `s_0t_0 = 1`; if `c` were a
two-sided inverse of `s_0`, then `c = (t_0s_0)c = t_0(s_0c) = t_0` and again
`s_0t_0 = 1`.  Either way `s_1t_1 = 1 + s_0t_0 = 0` in characteristic two, so
`1 = (t_1s_1)^2 = t_1(s_1t_1)s_1 = 0` — impossible.

**Item 1.**  The first prerequisite gives `K = <u_1,u_2,u_3> = (C_2 x C_2)*C_3`,
residually finite; and `t~ in F_2[K]` by construction.  Apply the second
prerequisite with `H = K`, `f = 1`, `alpha = t~`: a right inverse or a left
inverse of `t~` anywhere in `A` would make `pi(t~) = t_0` a unit of `R`.  It
is not.

**Item 2.**  Identical with `H = K_s = <v_1,v_2,v_3>`, `alpha = s~`,
`pi(s~) = s_0`.

**Item 3.**  The first prerequisite also gives `g = u_3`, so `e = [g]+[g^2]`
is an idempotent of `F_2[K]`, and `a = e t~ e` lies in `e F_2[K] e` with
`ea = ae = a`.  Since `g` has order three and `1+g+g^2 = 0` in `R`,
`pi(e) = g+g^2 = 1_R`, so `pi(a) = pi(e)pi(t~)pi(e) = t_0`.  Apply the second
prerequisite with `H = K`, `f = e`, `alpha = a`: a one-sided inverse in `eAe`
would give `b in e F_2[K] e` with `ab = ba = e`, hence
`t_0 pi(b) = pi(b) t_0 = pi(e) = 1` and `t_0` a unit of `R`.  It is not.

## What each prerequisite does

None is decorative.  The structure claim locates the support and is the only
place the Leavitt algebra's own arithmetic enters the group theory; the
rigidity lemma is what stops the partner from living outside that subgroup,
and is the step a support bound cannot supply; and the Leavitt defect is what
makes two-sided invertibility of the image absurd.  Drop the first and the
partner has room; drop the second and only the diagonal of the coset
decomposition is controlled; drop the third and `t_0` might simply have been
a unit, in which case there was never anything to prove.
