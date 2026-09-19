---
rg: 2
id: first-endpoint-m1-actor-preserves-missing-r-sign
kind: claim
title: The first endpoint M1 actor returns p2 only without changing the missing r sign
artifacts:
  - research/first-endpoint-m1-support-fence-proof.md
  - experiments/first_selector_endpoint_m1_support_audit.py
distinct_from:
  endpoint-order-five-actor-has-half-gram: that uses the second endpoint Whitehead and M2 to force a positive fine-sheet Gram; this applies the exact first-scale analogue and shows that its full signed-p2 return group preserves the missing first-selector sign.
  native-j1-extension-gives-gl5-but-only-second-whitehead-gram: that adjoins J1 to the second endpoint actor and analyzes signed-source returns inside the resulting GL5; this instead adjoins a fresh first endpoint Whitehead directly to the first order-seven head M1.
  endpoint-whitehead-star-braid-synchronizes-native-gauges: that synchronizes the three Whitehead reservoir gauges and fences signed-source normalizers in its GL5 actor; this computes the most direct extra actor proposed to pay the surviving r support.
---

**ESTABLISHED LITERAL ACTOR AND SUPPORT FENCE.**  Put

```text
W_0=What_(7,2;1),                 M_1=J_1B_2A_1,
D_0=qE_44+e_1E_77+e_2E_88+e_2E_22.                    (FEM1)
```

On the four equivalent projective summands

```text
q@4,                    e_1@7, e_2@8, e_2@2,
```

`M_1` is the native Singer order-seven actor on the first three and fixes
the fourth, while `W_0` swaps the second and fourth.  Hence

```text
<W_0,M_1>|_(D_0)=GL_4(F_2),                           (FEM2)
```

faithfully, and both actors are the identity on `1-D_0`.

On the commuting first-row root space

```text
V_5=<C_2,v,r,v'>,
C_2=x_54(q),       v=x_57(a_1),
r=x_58(a_2),       v'=x_52(a_2),                      (FEM3)
```

the literal conjugation table is

```text
M_1:(C_2,v,r,v') |-> (C_2r,r,C_2v,v'),
W_0:(C_2,v,r,v') |-> (C_2,v',r,v).                    (FEM4)
```

Let `K_2=<C_1,C_2,C_3,v,w,s>` with its signed character negative on the
three `C_i` and positive on `v,w,s`, and let `p_2` be its character
projection.  Exactly `16` elements of the actor `(FEM2)` normalize this
signed source.  Every one satisfies

```text
g r g^(-1) in {r,rv}.                                 (FEM5)
```

Since `v=+1` on `p_2`, every signed-source return preserves the `r` sign.
In particular the exact local profile

```text
p_2!=0,                  rp_2=-p_2                    (FEM6)
```

is compatible with every returned covariance row of this actor and has

```text
p_2(J_1p_2J_1)p_2=p_2 1_(r=+1)=0.                    (FEM7)
```

Thus the first-scale endpoint Whitehead and the complete odd head `M_1`
do not by themselves force positive first-selector support on the coarse
source `p_2`.  They provide another literal Property-`(T)`-free finite
actor, but its return parabolic sees `r` only modulo the already-positive
root `v`.

This fence does not apply after refinement to the full Hecke source `Q`.
The literal factor `B_2` is outside the coarse return group because it
sends `C_1` to `C_1d`, but `d` is a positive generator of the full signed
source.  Hence `b2-pairs-full-hecke-first-support` uses the same `B_2` as
a genuine full-source normalizer and its commutator `[r,B_2]=C_2` to
exchange the two `r` signs.  The present computation explains why that
finer source, rather than the bare endpoint return parabolic, is essential.

This is a scoped exact return-interface fence, not a representation of the
whole moving Leavitt packet.  No Property `(T)`, canonical trace,
literature theorem, local computation, or Lean compilation is used.

DERIVATION
first-endpoint-m1-support-fence-proof
