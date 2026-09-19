---
rg: 2
id: agent-free-compressor-hnn-product-split-proof
kind: route
title: Put the payload in one product factor and a marked finite mapping-torus quotient in the other
target: agent-free-compressor-hnn-letter-preserves-product-split
requires: []
---

The subgroup `F<=T_alpha` is embedded, so `r` has infinite order.  By
`single-free-endomorphism-has-marked-finite-quotients`, `T_alpha` is
residually finite.  The orders of the images of `r` in its finite quotients
are therefore unbounded: otherwise a fixed positive power of `r` would die
in every finite quotient.  Choose

```text
q_n:T_alpha->Q_n,             ell_n=ord(q_n(r))->infinity. (HPP1)
```

Define the finite product rings

```text
R_n=F_p times F_p[Q_n],       P_n=(1,0),
u_g=(1,q_n(g))                (g in T_alpha).           (HPP2)
```

Every equation in `(HPS2)` is then a literal ring identity.  In particular,
the stable unit `u_t` belongs to the second factor, commutes with `P_n`, and
satisfies

```text
u_t u_f u_t^(-1)=u_(alpha(f)).                          (HPP3)
```

Take the left regular representation of the finite elementary group

```text
E_5(R_n)=E_5(F_p) times E_5(F_p[Q_n]).                 (HPP4)
```

The payload root `x_13(P_n)` lies in the first factor and has order `p`, so
its nonidentity spectral density is `1-1/p`.  Every diagonal unit coming from
`T_alpha`, including the actual stable letter, lies in the second factor and
therefore commutes with that root.

The diagonal unit of `q_n(r)` has order `ell_n`.  Its left-regular spectral
measure is uniform on the `ell_n`-th roots of unity.  For every projection
`e_n` and `delta>0`,

```text
tr(e_n)
 <= #{z^ell_n=1:|z-1|<=delta}/ell_n
    +delta^(-2)||(D_(r,n)-1)e_n||_2^2.                 (HPP5)
```

Letting `n->infinity` and then `delta->0` proves the asserted vanishing of
`tr(e_n)`.  Since `(HPP3)` and all rank-five root identities are exact, this
is an exact countermodel to localization from the HNN letter and conditional
rows alone.
