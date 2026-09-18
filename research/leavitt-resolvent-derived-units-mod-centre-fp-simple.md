---
rg: 2
id: leavitt-resolvent-derived-units-mod-centre-fp-simple
kind: claim
title: For the Leavitt resolvent ring R_L, the derived unit group [R_L^x, R_L^x] modulo its centre is finitely presented and simple
distinct_from:
  leavitt-resolvent-ring-is-fp-simple-of-char-zero: that is the ring statement (finitely presented, simple, contains Q); this is the group statement needed to reach the root.
  leavitt-unit-group-finitely-presented: that is Khanh's finite presentation of L_(F_2)(1,2)^x in characteristic two; this is the characteristic-zero analogue for R_L, whose unit group has the non-finitely-generated centre Q^x.
  binary-leavitt-unit-group-is-simple: that is simplicity of L_(F_2)(1,2)^x = EL_3; this asks for simplicity modulo the centre in characteristic zero.
---

**OPEN.** Let `R_L` be the ring of `leavitt-resolvent-ring-is-fp-simple-of-char-zero`,
`D = [R_L^x, R_L^x]`, and `Z(D)` its centre. Then `D/Z(D)` is finitely presented and
simple.

**Why.** `GL_n(Q)` embeds in `D` and meets `Z(D)` trivially, for every `n`
(`leavitt-resolvent-ring-is-fp-simple-of-char-zero`, part 3). So this claim gives
`gl-n-q-embeds-in-fp-simple-group` through `gl-n-q-bh-via-leavitt-resolvent-units`.

## Attempts

1. **Characteristic-two model.** For `L = L_(F_2)(1,2)`:
   - `L^x = GL_3(L) = EL_3(L)` is simple (`binary-leavitt-unit-group-is-simple`);
   - `L^x` is finitely presented by Khanh, arXiv:2609.08428v1, Thm 6.1, through a
     Steinberg comparison and Krstić--McCool (`leavitt-unit-group-finitely-presented`).

   The same two steps are the natural attack here, with two differences, as expected
   (lane `gq-ring-fp-simple`, 2026-09-17):
   - the centre `Q^x` of `R_L^x` must be divided out;
   - the base ring `B = Q[N][(N+c)^(-1)]` is not finitely generated, although `R_L` is
     finitely presented.

   Neither step has been attempted yet. Lanes `gq-en-ring`, `gq-leavitt-units` and
   `gq-k2-q` own the `St`/`K_2` side.
2. **A caution.** `D` need not be finitely generated. The claim asks only for the
   quotient `D/Z(D)`. A weaker sufficient target is any finitely presented simple
   subquotient of `R_L^x` that still contains a copy of `SL_(n+2)(Q)` meeting the
   centre trivially.
