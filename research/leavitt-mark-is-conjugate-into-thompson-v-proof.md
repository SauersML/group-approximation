---
rg: 2
id: leavitt-mark-is-conjugate-into-thompson-v-proof
kind: route
title: Split the mark transvection as a complemented rank-one idempotent pair and match complements
target: leavitt-mark-is-conjugate-into-thompson-v
requires:
  - leavitt-steinberg-map-iso-from-rank-three
  - leavitt-cylinder-swaps-generate-thompson-in-el
artifacts:
  - experiments/leavitt-mark-thompson-conjugacy-2026-09-17/check_conjugacy.py
---

Conventions: `s_w=s_(w_1)...s_(w_k)`, `t_w=t_(w_k)...t_(w_1)`, so
`t_w s_w=1`, `t_w s_x=0` for incomparable `w,x`, and `sum_(w in C) s_w t_w=1`
for every complete prefix code `C`.  Characteristic is two throughout.

**1. Transport.**  KH2 identifies `Delta` with `GL_20(R)`.  The code `c`
gives a unital ring isomorphism `M_20(R) -> R`, hence `GL_20(R) = R^x`.
The root element `x_13(r)` goes to `1+s_(c_1) r t_(c_3)`, so `z` goes to
`Z = 1 + s_(c_1) s_1 t_1 t_(c_3) = 1 + s_a t_b` with `a=c_1 1`, `b=c_3 1`.

**2. Shape of `Z` and of `v`.**  Write `Z = 1 + e f` with `e=s_a`, `f=t_b`;
then `fe=t_b s_a=0` since `a,b` are incomparable.  Also
`v = 1 + e'f'` with `e'=s_00+s_01`, `f'=t_00+t_01`: expanding,
`1+e'f' = 1+s_00t_00+s_01t_01+s_00t_01+s_01t_00 = s_1t_1+s_00t_01+s_01t_00`,
and `f'e' = 1+0+0+1 = 0`.  Choose the splittings
`h=t_a, g=s_b` and `h'=t_00, g'=s_01`.  Then
`he=fg=1`, `hg=fe=0`, and likewise `h'e'=f'g'=1`, `h'g'=f'e'=0`.

**3. The conjugator.**  Put `W={c_1 0, c_3 0} u {c_i : i /= 1,3}`, so
`{a,b} u W` is a complete prefix code with `|W|=20`, and let `d` be any
complete 20-word code.  Define

```text
u    = g' f + e' h + sum_i s_(1 d_i) t_(W_i),
u'   = g f' + e h' + sum_i s_(W_i) t_(1 d_i).
```

Using the relations of step 2 and incomparability of `W_i` with `a,b`:

- `u u' = g'f' + e'h' + s_1t_1`.  In characteristic two
  `g'f'+e'h' = s_01t_00+s_01t_01+s_00t_00+s_01t_00 = s_00t_00+s_01t_01`, so
  `u u' = 1`.
- `u' u = g f'g' f + e h'e' h + g f'e' h + e h'g' f + sum_i s_(W_i)t_(W_i)
  = s_b t_b + s_a t_a + 0 + 0 + sum_i s_(W_i) t_(W_i) = 1`.

So `u` is a unit with inverse `u'`.

**4. Conjugation.**  `u e = e' h e = e'` and `f u' = f g f' = f'` (all other
terms vanish because `fe=hg=0` and `t_b s_(W_i)=t_a s_(W_i)=0`).  Hence

```text
u Z u^-1 = 1 + (u e)(f u^-1) = 1 + e'f' = v.                      (MC1)
```

**5. `v` lies in `V`.**  `v = S[01]T[00] + S[00]T[01] + S[1]T[1]` is the
image of the prefix replacement `(00,01,1) -> (01,00,1)` under the embedding
`V <= R^x` of `leavitt-cylinder-swaps-generate-thompson-in-el`.

**Why it works (and why characteristic two is essential).**  Step 3 is the
module statement that two rank-one "transvections" `1+ef` with `fe=0` and
split `e,f` are conjugate once their complements `ker f ∩ ker h` are both
nonzero, since every nonzero finitely generated projective `L_2`-module is
free of rank one (here realized explicitly by the codes `W` and `1d`).  The
Thompson involution `v` has this shape only because `f'e'=1+1=0`.

**Computer check.**  `check_conjugacy.py` verifies `Z^2=v^2=1`,
`u u^-1 = u^-1 u = 1` and `(MC1)` exactly, with negative controls.  Its
equality test is complete: every element is refined to
`sum_(|w|=N) x_w t_w` with `x_w` in the span of the `s_alpha`, and these
coefficients determine the element (faithful action on `w.Y`, `Y` aperiodic).
