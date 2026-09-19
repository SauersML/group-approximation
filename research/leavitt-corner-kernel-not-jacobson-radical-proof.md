---
rg: 2
id: leavitt-corner-kernel-not-jacobson-radical-proof
kind: route
title: Push the complementary idempotent down the recursive embedding
target: leavitt-corner-kernel-not-jacobson-radical
requires: [leavitt-primitive-corner-recursive-extension, leavitt-evaluation-kernel-hits-augmentation-one]
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
  - research/artifacts/verify-s3-corner-2026-08-17.py
---

## Direct proof

Notation from the first prerequisite: `f = [1]+[u]+[v]+[g]`, `T = f S f`,
`rho : T ->> R`, `lambda : S -> T` injective with `rho . lambda = pi`,
`ker(rho) = f K f` where `K = ker(pi)`.

**Step 1 — `z` is a nonzero idempotent of `K` with `eps(z) = 1`.**  Put
`z = [1] + [g] + [g^2] = 1 + e`.  Since `g^3 = 1` and the characteristic is
two, `e^2 = e` gives `z^2 = 1 + 2e + e^2 = 1 + e = z`.  It is nonzero because
`1, g, g^2` are three distinct elements of `G`.  Its evaluation is
`pi(z) = 1 + g + g^2 = 0`, since `g^2 + g + 1 = 0` holds in `R` — that is the
order-three relation of `leavitt-corner-idempotent-unital-surjection`.  So
`z in K`, and `eps(z) = 3 mod 2 = 1`.

(The second prerequisite is what guarantees the graph already knew `K != 0`;
`z` is a second, independent witness for that, and unlike `[u]+[v]+[w]` it is
idempotent.)

**Step 2 — `q = lambda(z)` is a nonzero idempotent.**  `lambda` is a ring
homomorphism, so `q^2 = lambda(z^2) = lambda(z) = q`; it is injective, so
`q != 0`.

**Step 3 — `q in ker(pi_e)`.**  `rho(q) = rho(lambda(z)) = pi(z) = 0`, so
`q in ker(rho) = f K f <= K`.  Also `q in fSf <= eSe`, since `f <= e` gives
`e q e = e f q f e = f q f = q`.  Hence `pi_e(q) = pi(q) = 0`.

**Step 4 — `eps(q) = 0`.**  `eps` is a ring homomorphism and
`eps(delta_*(a)) = eps(a)` because `delta` is a map of groups, so
`eps(q) = eps(z) eps(f) = 1 . 0 = 0`, `f` having four basis terms.

**Step 5 — no nonzero idempotent lies in a Jacobson radical.**  If
`r^2 = r in J(A)` for a unital ring `A`, then `1 - r` is a unit; multiplying
`r(1 - r) = 0` by its inverse gives `r = 0`.  Applying this in `A = eSe`,
whose identity is `e`, with `r = q`: `q` is a nonzero idempotent of `eSe`, so
`q` is not in `J(eSe)`, so `ker(pi_e)` is not contained in `J(eSe)`, so in
particular `ker(pi_e) != J(eSe)`.

## The explicit element, and the finite certificate

Expanded over the group basis, `q` has exactly twelve terms:

    q = sum_(a in {1, g, g^2}) sum_(h in {1, u, v, g}) [delta(a) h],

with `delta(a) = s_0 a t_0 + s_1 a t_1`.  The twelve products `delta(a)h` are
pairwise distinct because `delta(G) x H` embeds in `G`, and each is a unit
with `(delta(a)h)^-1 = delta(a^-1) h^-1`, the two factors commuting;
`1^-1 = 1`, `u^-1 = u`, `v^-1 = v`, `g^-1 = g^2`.

`research/artifacts/verify-s3-corner-2026-08-17.py` certifies the finite half
of this exactly, in `F_2[S_3 x S_3]`: the twelve support pairs are distinct
with the stated componentwise inverses, and the twelve-term element is a
nonzero idempotent lying under the constant primitive corner.  Run on MSI
2026-08-17; all assertions pass.  The same script certifies `e k = k e = 0`
for the old three-term kernel witness, which is why that element could not
have been used here.
