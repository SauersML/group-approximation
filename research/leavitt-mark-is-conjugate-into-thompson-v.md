---
rg: 2
id: leavitt-mark-is-conjugate-into-thompson-v
kind: claim
title: The binary-Leavitt Steinberg mark is conjugate to a Thompson cylinder swap
distinct_from:
  leavitt-cylinder-swaps-generate-thompson-in-el: that places Thompson's V inside the elementary prefix group as a subgroup; this says the specific root mark z=x_13(s_1t_1), a transvection that is not a permutation unit, is conjugate in Delta to one element of that copy of V.
  leavitt-st20-t-free-holes-hold-via-kazhdan: that identifies St20 with the simple Leavitt unit group and settles the literal holes through property (T); this is a Kazhdan-free conjugacy computation that moves the mark into a Haagerup subgroup.
  leavitt-mf-quotients-see-thompson-vd-through-parity: that pushes Higman--Thompson subgroups into the MF radical through K_1 parity and the maximal MF quotient, which uses (T); this is a pure ring-theoretic identity and says nothing about radicals by itself.
artifacts:
  - research/leavitt-mark-is-conjugate-into-thompson-v-proof.md
  - experiments/leavitt-mark-thompson-conjugacy-2026-09-17/check_conjugacy.py
---

**ESTABLISHED (written proof and an exact, complete computer check of the
identity; not Lean-verified).**  Let `R=L_(F_2)(1,2)`, `Delta=St_20(R)` and
`z=x_13(s_1t_1)`.  Identify `Delta` with `R^x` through the Khanh isomorphism
`St_20(R) -> GL_20(R)` (`leavitt-steinberg-map-iso-from-rank-three`, KH2)
followed by the ring isomorphism `M_20(R) -> R`, `E_ij r -> s_(c_i) r t_(c_j)`,
of a complete 20-word prefix code `c_1,...,c_20`.  Put `a=c_1 1`, `b=c_3 1`.
Then `z` becomes

```text
Z = 1 + s_a t_b ,
```

and there is an explicit unit `u in R^x` with

```text
u Z u^-1 = v := s_00 t_01 + s_01 t_00 + s_1 t_1 ,                   (MC1)
```

the cylinder swap of `[00]` and `[01]`, an involution of Thompson's group
`V <= R^x` (`leavitt-cylinder-swaps-generate-thompson-in-el`).  So **the mark of
the goal is conjugate in `Delta` into `V`**.  Explicitly, with `W` the
complementary code `{c_1 0, c_3 0} u {c_i : i /= 1,3}` (20 words) and
`d_1,...,d_20` any complete 20-word code,

```text
u    = s_01 t_b + (s_00+s_01) t_a + sum_i s_(1 d_i) t_(W_i),
u^-1 = s_b (t_00+t_01) + s_a t_00 + sum_i s_(W_i) t_(1 d_i).
```

**Kazhdan hygiene.**  Only the Leavitt relations in characteristic two, and
KH2 (proved from Steinberg-group criteria and simple connectivity, with no
spectral input), are used.

DERIVATION
leavitt-mark-is-conjugate-into-thompson-v-proof
