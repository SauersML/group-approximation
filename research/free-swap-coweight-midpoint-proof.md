---
rg: 2
id: free-swap-coweight-midpoint-proof
kind: route
title: Evaluate the two-letter free overlap in each coweight direction
target: free-swap-is-midpoint-not-coweight-flip
requires:
  - coweight-triangle-charges-every-common-sheet-flip
---

Fix one of the three coweight directions and write `u=pi(d_r)` and
`s_r=usu^*`.  Since `d_r notin C`, both `u` and `u^*` are centered over
`B`.  Amalgamated freeness and `E_B(s)=0` give

```text
tau(s)=tau(s_r)=tau(ss_r)=0.                            (CFP1)
```

Consequently

```text
tau(PP_r)
 =1/4 tau((1+s)(1+s_r))
 =1/4.                                                  (CFP2)
```

Both projections have trace `1/2`, so

```text
tau(P_r(1-P))=tau(P_r)-tau(P_rP)=1/4.                  (CFP3)
```

The projection identity

```text
||E-F||_2^2=tau(E)+tau(F)-2 Re tau(EF)
```

applied to `E=P_r` and `F=1-P` now gives

```text
||P_r-(1-P)||_2^2=1/2+1/2-2(1/4)=1/2.                 (CFP4)
```

This calculation is identical for all three directions.  Substitution in
`(CTA7)` with the exact coweight triangle (`eta=0`) gives
`3/sqrt(2)>=1`, so the claimed obstruction has positive slack rather than
a contradiction.  The same finite set of moments passes to any canonical
matrix approximation.
