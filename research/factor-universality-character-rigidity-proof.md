---
rg: 2
id: factor-universality-character-rigidity-proof
kind: route
title: Force a universal non-CE factor representation to carry the regular character
target: factor-universality-character-rigidity-implies-nonhyperlinear
requires:
  - mipstar-equals-re
---

Choose a separable non-Connes-embeddable tracial von Neumann algebra `M`.
Universality embeds it trace-preservingly into a finite factor
`Q=pi(H)''`.  Then `Q` is non-CE.  The character

```text
chi(h)=tau_Q(pi(h))                                     (FCR1)
```

is extremal because its GNS algebra is the factor `Q`.  It cannot come from
a finite-dimensional factor representation, since that would make `Q`
finite dimensional while `Q` contains the non-CE algebra `M`.  Character
rigidity therefore gives `chi=delta_e`.  The GNS representation of
`delta_e` identifies `Q` trace-preservingly with `L(H)`.  Hence `L(H)` is
non-CE and `H` is nonhyperlinear.
