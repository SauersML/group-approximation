---
rg: 2
id: leavitt-24k-generators-as-explicit-units-of-the-ring
kind: claim
title: The four frozen generators are explicit units of the binary Leavitt algebra itself
distinct_from:
  binary-leavitt-units-generated-by-c3-and-c2-cubed: that exhibits the generating pair as elementary matrices in EL_3(R) and proves they generate; this transports the same four elements across a prefix-code matrix isomorphism and writes them as words in the four Leavitt generators, adding no group theory.
  binary-leavitt-unit-group-four-generated: that certifies four units by exact enumeration in GL_4(F_2) and pairs them two per A_8 chart; this writes down the units corresponding to the C_3 and C_2^3 pair used by the 24k criterion, with no enumeration.
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies the unit group with GL_3 = EL_3 and proves perfectness; this makes one direction of that identification explicit on four named elements.
artifacts:
  - research/artifacts/leavitt-tracial-moment-relaxation-no-go-2026-09-08.md
---

**ESTABLISHED.**  In `R = L_(F_2)(1,2)` put

```text
(p_1,p_2,p_3) = (s_0, s_1s_0, s_1s_1),
(r_1,r_2,r_3) = (t_0, t_0t_1, t_1t_1).                            (PU1)
```

Then `r_i p_j = delta_(ij)` and `sum_i p_i r_i = 1`, so

```text
Theta : M_3(R) --> R,   Theta((a_(ij))) = sum_(i,j) p_i a_(ij) r_j (PU2)
```
is a unital ring isomorphism with inverse `z |-> (r_i z p_j)`.

Under `(PU2)` the four frozen generators of
`binary-leavitt-units-generated-by-c3-and-c2-cubed` become the units

```text
Theta(c)   = p_2 r_1 + p_3 r_2 + p_1 r_3,
Theta(b_1) = 1 + p_1 s_0 r_2,
Theta(b_2) = 1 + p_1 t_0 r_2,
Theta(b_3) = 1 + p_1 v r_2,       v = s_0t_1 + s_1t_0.            (PU3)
```

So the `24k` feasibility problem of
`binary-leavitt-hyperlinear-iff-24k-feasible` can be posed directly
against four written-out elements of `R`, with no matrix layer: `(PU3)`
generates a copy of `C_3` and a copy of `C_2^3` inside `R^x` whose join is
all of `R^x`.

This is a transport of an existing statement across an explicit
isomorphism.  It proves nothing new about generation, adds no analysis,
and does not bear on which branch of the feasibility problem holds.

DERIVATION
leavitt-24k-generator-unit-translation-proof
