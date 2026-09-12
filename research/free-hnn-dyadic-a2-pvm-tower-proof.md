---
rg: 2
id: free-hnn-dyadic-a2-pvm-tower-proof
kind: route
title: Spectrally refine the Haar lamp and conjugate every atom around A over C
target: free-hnn-outlier-has-dyadic-a2-pvm-tower
requires:
  - hnn-stable-letter-rounds-to-finite-order
  - centralizer-hnn-is-free-generalized-wreath
  - sl3-amalgamated-free-enemies-are-ambient-extension-outliers
---

The spectral measure of the Haar unitary `k` is Lebesgue measure.  Its
dyadic spectral projections therefore satisfy `(DPT2)`.  Since `k`
commutes with `pi(B)`, all its spectral projections do as well.

If `aC=a'C`, write `a'=ac` with `c in C`.  Every `q_(r,j)` commutes with
`pi(c)`, so `(DPT3)` is independent of the representative.  Conjugation by
`pi(g)` sends the atom indexed by `aC` to the atom indexed by `gaC`, proving
covariance.

By `centralizer-hnn-is-free-generalized-wreath`, the conjugates

```text
k_x=pi(a)kpi(a)^*       (x=aC)
```

are the canonical generators of the free product of copies of `Z` indexed
by `A/C`.  Hence their diffuse abelian spectral algebras `D_x` are freely
independent.  For completeness, the pair overlap can also be read directly
from amalgamated freeness.  Put `alpha=2^(-r)`, `beta=2^(-s)` and write
`q_(r,i)=alpha 1+q_0`, `q_(s,j)=beta 1+q_1`, with both `q_0,q_1`
`E_B`-centered.  If `x=aC!=bC=y`, then `g=a^(-1)b notin C`; expansion of

```text
tau(q_(r,i) pi(g) q_(s,j) pi(g)^*)
```

leaves only the scalar term `alpha beta`.  Every other term is an
alternating centered word for the free pair.  This proves `(DPT4)`.

Finally the elementary Steinberg identity

```text
[x_23(1),x_31(-1)]=x_21(-1)                            (DPP1)
```

holds in `SL_3(Z)`.  Covariance of `(DPT3)` sends equal actor words to the
same conjugated projection, proving `(DPT5)` exactly.  The ambient-outlier
assertion is precisely the conclusion of the third required claim.
