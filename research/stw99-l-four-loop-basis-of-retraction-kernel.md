---
rg: 2
id: stw99-l-four-loop-basis-of-retraction-kernel
kind: claim
title: Four explicit loops are an integral basis of the kernel of the Bott-evaluation retraction on A theta tensor O infinity
artifacts:
  - research/artifacts/stw99-l-six-kirchberg-loops-2026-09-05.md
---

Keep the marking of `stw99-l-six-circle-actions-basis-of-pi1-aut` and
form the pointwise compositions

```text
kappa_1 = sigma_2,   kappa_2 = sigma_4,
kappa_3 = rho_1 sigma_1^{-1},   kappa_4 = rho_2 sigma_3^{-1}.
```

These are based continuous automorphism loops (the last two need not be
circle actions), with columns

```text
(0,1,0,0,0,0),  (0,0,0,1,0,0),  (0,0,0,0,0,1),  (0,0,0,0,-1,0).
```

Let `D = A_theta (x) O_infinity`, fix a unital classification isomorphism
`chi : A -> D` carrying `e |-> [1_D]`, `beta |-> q`, `x |-> [U (x) 1]`,
`y |-> [V (x) 1]`, and let

```text
r : pi_1(Aut(D)) -> Z^2,    r(alpha) = ( (Delta_alpha [U (x) 1])_{[1_D]},
                                        (Delta_alpha [V (x) 1])_{[1_D]} )
```

be the two-coordinate Bott-evaluation retraction.  Then `r` is a split
surjection and the four transported loops

```text
z |-> chi kappa_j(z) chi^{-1},    j = 1,2,3,4,
```

are an integral basis of `ker r = Z^4`.  Together with any section of `r`
-- for instance the transported `sigma_1, sigma_3` -- they are a basis of
`pi_1(Aut(D)) = Z^6`.
