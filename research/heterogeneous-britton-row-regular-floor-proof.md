---
rg: 2
id: heterogeneous-britton-row-regular-floor-proof
kind: route
title: Separate the two compressed row supports by Britton normal form
target: heterogeneous-britton-row-has-regular-energy-floor
requires: []
---

Write `p=sum_(g in B)c_g g`.  Every group word occurring in the canonical
trace of the cross term has the form

```text
g^(-1) t^(-1) a^(-1) t h b,          g,h in B.        (HBP1)
```

The only possible Britton pinch between its two stable letters is
`t^(-1)a^(-1)t`.  It would require `a^(-1) in C`, contrary to `a notin C`.
Thus `(HBP1)` is a reduced HNN word containing stable letters, so it is
nonidentity.  Linear extension gives

```text
tau_Gamma(p t^(-1)a^(-1)t p b)=0.                     (HBP2)
```

Using `p=p^*=p^2` and `[b,p]=0`, the two diagonal terms are both
`tau_Gamma(p)`.  Expanding the square of `(HBR1)` and applying `(HBP2)` gives

```text
||a t p-t p b||_2^2
 =tau(p)+tau(p)-2 Re tau(p t^(-1)a^(-1)t p b)
 =2 tau(p).                                           (HBP3)
```

The canonical trace is faithful on the group algebra, so `p!=0` implies
`tau(p)>0`.

Finally, the squared norm of the evaluated row is a fixed finite linear
combination of traces of group words.  Approximate satisfaction of a fixed
finite presentation transports the finitely many fixed group equalities
used in this expansion with `o(1)` loss, and the canonical moment condition
converges to the corresponding regular traces.  Hence `(HBP3)` gives
`(HBR3)` first with `p(U_n)`.  Replacing it by a packet exactification `p_n`
changes the row by at most

```text
||a t(p_n-p(U_n))||_2+||t(p_n-p(U_n))b||_2
 <=2||p_n-p(U_n)||_2=o(1),
```

so the same limit holds for the exactified carrier used in `(FHC1)`.
