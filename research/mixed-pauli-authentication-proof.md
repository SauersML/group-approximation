---
rg: 2
id: mixed-pauli-authentication-proof
kind: route
title: Expand the capacity commutator into the Pauli word
target: mixed-pauli-commutator-authenticates-one-capacity-cut
requires: []
---

Since `X=X^*=X^-1` and `Z=Z^*=Z^-1`,

```text
ZQ-QZ=(ZX-XZ)/2.
```

Writing `c=XZXZ`, direct multiplication followed by tracial cyclicity gives

```text
4||ZQ-QZ||_2^2=2-2 Re tau(c)=||c-I||_2^2.
```

This proves the exact identity.  If `Y=c`, it becomes
`||ZQ-QZ||_2^2=||Y-I||_2^2/4`.  Without exact coupling,

```text
||c-I||_2<=||c-Y||_2+||Y-I||_2,
```

and `(a+b)^2<=2a^2+2b^2` yields

```text
||ZQ-QZ||_2^2
 <=1/2||Y-I||_2^2+1/2||Y^-1c-I||_2^2.
```

The extraspecial Pauli representation with `[X,Z]=J` realizes `Y=J`
nontrivially, proving that the mixed cell authenticates rather than
universally kills the leakage.  Conversely, when `Q=0`, `X=-I` and the cell
extends with `Y=I`, giving the exact completeness firewall.
