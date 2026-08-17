---
rg: 2
id: leavitt-recursive-kernel-idempotents-proof
kind: route
title: Iterate the corner embedding on the complementary idempotent
target: leavitt-recursive-kernel-idempotents
requires: [leavitt-primitive-corner-recursive-extension]
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

## Direct proof

Write `lambda(a) = delta_*(a) f` for the embedding of the prerequisite, read
as an injective nonunital ring endomorphism of `S` with image in `f S f`, and
`z = [1] + [g] + [g^2] = 1 + e`.  Set `q_0 = z` and `q_n = lambda^n(z)`.

**Idempotent.**  `z^2 = z` because `e^2 = e` and the characteristic is two;
`lambda` is multiplicative, so `q_n^2 = lambda^n(z^2) = q_n`.

**Nonzero.**  `z != 0` since `1, g, g^2` are distinct group elements, and
`lambda` is injective.

**In the kernel.**  `rho . lambda = pi` and `pi(a) = s_0 rho(a) t_0` for
`a in fSf` together give `pi(lambda(a)) = s_0 pi(a) t_0`, so
`lambda(K) <= K`.  Since `pi(z) = 1 + g + g^2 = 0`, induction gives
`q_n in K` for every `n`.

**Orthogonal.**  `f <= e` means `e f = f e = f`, so
`z f = (1 + e) f = f + f = 0` and symmetrically `f z = 0`.  For `m >= 1`, `q_m = lambda(lambda^(m-1)(z)) in f S f`, so
`z q_m = q_m z = 0`.  Now take `0 <= i < j` and apply `lambda^i`, which is a
ring homomorphism:

    q_i q_j = lambda^i(z) lambda^i(lambda^(j-i)(z))
            = lambda^i( z . lambda^(j-i)(z) ) = lambda^i(0) = 0,

and the same on the other side.

**Augmentation.**  `eps(f) = 0` because `f = [1]+[u]+[v]+[g]` has four basis
terms, and `eps(delta_*(a)) = eps(a)` because `delta` is a group
homomorphism.  Hence `eps(lambda(a)) = eps(a) eps(f) = 0` for every `a`, so
`eps(q_n) = 0` for `n >= 1`, while `eps(q_0) = eps(z) = 1`.

**Location.**  `q_n in f S f` for `n >= 1` by construction, and `q_n in K`, so
the family from index one on lies in `f K f = ker(rho)`, the primitive-corner
kernel.
