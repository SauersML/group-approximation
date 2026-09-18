---
rg: 2
id: fpbs-critical-sphere-rate-vanishes-on-tree-products
kind: claim
title: On a finite product of regular trees the sphere two-point rate is left-continuous and vanishes at p_c
distinct_from:
  fpbs-sphere-two-point-rate-right-continuous-universal: that node asks for EG0 and EG1 on every nonamenable Cayley graph; this node proves EG0, and left-continuity of g everywhere, on products of regular trees only, without any pointwise decay input
  fpbs-pointwise-critical-growth-decay-fails: that node refutes pointwise gr-decay on these graphs; this node shows EG0 survives there anyway
---

**ESTABLISHED.** Proof in `fpbs-critical-sphere-rate-vanishes-on-tree-products-proof`.

**Setting.** `G = T_(a_1) □ ... □ T_(a_n)` with `n >= 1`, every `a_i >= 2`
(`T_2 = Z`), and at least one `a_i >= 3`. So `G` is nonamenable. It is the
Cayley graph of a direct product of free products of copies of `Z/2`, or of
free groups and `Z`, with the union of the factor generating sets. Let

```text
g(p) = limsup_r (1/r) log M_r(p),    M_r(p) = E_p|K_o ∩ S_r|.
```

**Claim.**

1. **Type formula.** For `v in N^n \ {0}`, put `|v| = sum v_i` and
   `W(v) = prod (a_i - 1)^(v_i)`. Let `tau_p(v)` be `tau_p(o,z)` for any `z`
   whose factor distances from `o` are `v`; it does not depend on `z`. Then

   ```text
   g(p) = sup_(v != 0) (1/|v|) log( W(v) tau_p(v) )    for every p in (0,1].
   ```

2. **Left-continuity.** `g` is nondecreasing and left-continuous on `(0,1]`.
3. **EG0.** `g(p_c) = 0`.

**Why it matters.** EG0 holds on graphs where pointwise gr-decay fails
(`fpbs-pointwise-critical-growth-decay-fails`, for example `T_3 □ T_10` and
`Z x F_3`). So the upper half of EG0 comes from a mechanism other than
pointwise decay.

The mechanism: `g` is a supremum of left-continuous functions of `p`, one for
each finite distance type, and every such function is `<= 0` below `p_c`.

The universal EG0 therefore reduces to one question. Can the spheres of a
general Cayley graph be covered by subexponentially many types, with the
two-point function supermultiplicative along each type? See the Attempts of
`fpbs-sphere-two-point-rate-right-continuous-universal`.

This does not bear on EG1. The type formula exhibits `g` as a supremum, and a
supremum gives left-continuity only, not right-continuity.
