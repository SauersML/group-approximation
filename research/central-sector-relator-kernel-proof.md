---
rg: 2
id: central-sector-relator-kernel-proof
kind: route
title: Read a quotient representation's scalar kernel from the unique central-regular trace
target: central-character-rigid-sector-forbids-relator-quotients
requires: []
---

Choose a trace `sigma` on `B`.  Uniqueness on the source gives

```text
sigma Phi=tau_eta.                                     (1)
```

If `u_g=lambda 1_B` is scalar, then `(1)` and `(UCR1)` give

```text
1=|lambda|=|sigma(u_g)|=|tau_eta(p_eta g)|.
```

The last absolute value is zero for `g notin C`, so `g in C`.  Conversely
every `c in C` acts as the scalar `eta(c)` in the `eta`-corner.  Therefore
the projective kernel is exactly `C`.

If `u_g=1_B`, the same argument gives `g in C` and then
`1=tau_eta(p_eta g)=eta(g)`.  Faithfulness of `eta` gives `g=1`.  Thus the
ordinary kernel is trivial.  If a normal subgroup `N` is killed by added
group relators, every `n in N` lies in this kernel, hence `N={1}`.

Finally, if `I=ker Phi`, then for `a in I`,

```text
tau_eta(a* a)=sigma(Phi(a* a))=0.
```

Thus `I` lies in the GNS kernel.  Surjectivity and `(1)` identify the two
tracial GNS completions, exactly as in
`unique-trace-signed-corner-quotient-forces-nonhyperlinear`.

