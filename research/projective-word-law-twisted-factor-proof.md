---
rg: 2
id: projective-word-law-twisted-factor-proof
kind: route
title: Apply the scalar-kernel character criterion to the free group on the generators
target: projective-word-law-characterizes-twisted-group-factors
requires:
  - projective-basis-character-criterion
---

Assume `(PWL1)` and let `F` be the free group on the indices `j`.  The map
from its free generators to `u_j` gives a character

```text
chi(g)=tau(pi(g))
```

whose GNS algebra is `M`.  Equality in Cauchy--Schwarz for the unitary
`pi(g)` says

```text
|chi(g)|=1  iff  pi(g) is scalar.
```

Thus `(PWL1)` says exactly that `chi` vanishes off its scalar kernel.
`projective-basis-character-criterion` now identifies `M` with the twisted
group factor of the quotient of `F` by that scalar kernel, proving `(PWL2)`.

Conversely enumerate the canonical projective unitaries `(lambda_g)` of
`L_omega(Gamma)`.  They generate the factor and multiply by

```text
lambda_g lambda_h=omega(g,h) lambda_(gh).
```

Every word is therefore a scalar multiple of one canonical basis unitary.
Its trace is zero unless its index is the identity, in which case it has
modulus one.  This proves `(PWL1)` and the orthonormal-basis formulation.

