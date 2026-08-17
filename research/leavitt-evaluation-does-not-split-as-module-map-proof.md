---
rg: 2
id: leavitt-evaluation-does-not-split-as-module-map-proof
kind: route
title: A section would annihilate the kernel against a nonzero ideal
target: leavitt-evaluation-does-not-split-as-module-map
requires: [leavitt-unit-group-algebra-is-prime, leavitt-evaluation-kernel-hits-augmentation-one]
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

## Direct proof

Write `S = F_2[G]`, `pi : S ->> R`, `K = ker(pi)`, and give `R` the left
`S`-module structure `s . r = pi(s) r`.  Suppose `sigma : R -> S` is left
`S`-linear with `pi . sigma = id_R`, and set `p = sigma(1_R)`.

**`sigma(pi(s)) = s p`.**  `pi(s) = pi(s) . 1_R = s . 1_R`, so
`sigma(pi(s)) = sigma(s . 1_R) = s sigma(1_R) = s p`.

**`p != 0` and `p^2 = p`.**  `pi(p) = pi(sigma(1_R)) = 1_R != 0`, so `p != 0`;
and `p^2 = sigma(pi(p)) = sigma(1_R) = p`.

**`K p = 0`.**  For `k in K`, `k p = sigma(pi(k)) = sigma(0) = 0`.

**Two nonzero ideals with zero product.**  `K` is a two-sided ideal, so
`K S = K`, hence

    K (S p S) = (K S) p S = K p S = 0.

`K != 0` by the second prerequisite (which supplies the explicit witness
`[u] + [v] + [w]`), and `S p S != 0` because `p != 0` and `S` is unital.  This
contradicts primality of `S`, the first prerequisite.  So no `sigma` exists.

**Projectivity.**  `R` is generated over `S` by `1_R`, so `pi` is a surjection
from a free left `S`-module onto `R`; if `R` were projective that surjection
would split, and it does not.  Hence `R` is not projective, and in particular
not a direct summand of a finite free left `S`-module.  Equivalently `K` is
not a direct summand of `S`.

## Two remarks that are not needed but are worth recording

**The hypothetical `p` is not visibly absurd, which is the point.**  Applying
the augmentation to `k p = 0` with the witness `z = [1] + [g] + [g^2]` of
`eps(z) = 1` forces `eps(p) = 0`; applying `pi` gives `pi(p) = 1_R`.  Both are
satisfiable by elements of `S`, and `S p` would be a unital subring with
identity `p` carried isomorphically onto `R` by `pi`.  No count, parity, or
augmentation argument closes this; only primality does.

**One-sidedness is real.**  The argument uses only a *left* module section,
which is what `leavitt-direct-finiteness-failure-from-module-splitting`
consumes.  A right-module section is excluded by the mirror argument, with
`p K = 0` and `(S p S) K = 0`.
