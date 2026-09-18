---
rg: 2
id: odometer-generators-carry-no-nonsolvable-baumslag-solitar
kind: claim
title: If a is an odometer times the identity and t a^m t^-1 = a^n with n invertible on the odometer group, then t a t^-1 commutes with a, so a non-solvable BS(m,n) is never generated faithfully this way
distinct_from:
  odometer-2v-is-fp-simple-and-contains-bs12: that realizes the solvable BS(1,2) with the odometer generator s = tau x id; this shows that the same kind of generator cannot carry any BS(m,n) with |m|, |n| >= 2 unless both m and n are non-invertible on the odometer group.
  affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q: that bounds which divisible subgroups affine 2V-hosts reach; this bounds which Baumslag-Solitar relations an odometer generator can satisfy faithfully, in any homeomorphism group.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports BH for every BS(m,n) (Bux-Llosa Isenrich-Wu); this is only an obstruction to one explicit construction shape and says nothing against BH.
artifacts:
  - research/artifacts/gq-bh-bh-cool-targets-and-odometer-rigidity.md
---

**ESTABLISHED** through `odometer-generators-carry-no-nonsolvable-baumslag-solitar-proof`. Lane proof (bh-cool),
elementary, not independently reviewed. No novelty is claimed.

## Statement

Let `K` be a compact monothetic group with topological generator `1`, let `Y` be a compact Hausdorff space, and let
`a` be a homeomorphism of a space `X` that is conjugate to `(+1) x id_Y` on `K x Y`. Let `m, n` be nonzero integers
and let `t` be a homeomorphism of `X` with `t a^m t^-1 = a^n`.

1. If `nK = K` (that is, `+n` is minimal on `K`), then `t a t^-1` commutes with `a`.
2. If `mK = K`, then `t^-1 a t` commutes with `a`.
3. Suppose `|m|, |n| >= 2`. If `mK = K` or `nK = K`, the homomorphism `BS(m,n) -> <a, t>`, `a -> a`, `t -> t`, is
   not injective: its kernel contains `[t a t^-1, a]` (case `nK = K`) or `[t^-1 a t, a]` (case `mK = K`), and both
   are nontrivial in `BS(m,n)` by Britton's lemma.

So an odometer-type generator can carry a faithful non-solvable `BS(m,n)` only if **both** `m` and `n` are
non-invertible on `K`. For `K = Z_S` (the `S`-adic integers) this means that both `m` and `n` have a prime factor in
`S`.

## Consequences for the swarm's hosts

- In `2V_tau` and in the affine hosts `2V_H` of `affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q`, the natural
  generator `s = tau x id` lives over `K = Z_2`. So no `BS(m,n)` with `|m|, |n| >= 2` and `m` or `n` odd (for example
  `BS(2,3)`, the example in BBMZ Problem 5.3(4)) is generated faithfully by `s` and any `t` in any homeomorphism
  group. A faithful `BS(2,3)` with an odometer generator needs an odometer group divisible-sensitive at both 2 and 3,
  such as `Z_6` or `Z-hat`.
- The explicit attempt recorded in the artifact (`t = mu rho c` with `mu(x) = 3x` on `Z_2`, the baker map `rho` and
  any twist `c` in the centralizer of `a^2`) satisfies `t a^2 t^-1 = a^3`, and item 1 shows it can never be faithful.
  *Remark (sketch in the route, not part of items 1-3):* iterating item 1 through the non-Hopfian self-map
  `phi: a -> a^2, t -> t` of `BS(2,3)` shows that its kernel contains every `ker(phi^k)`.
- BH for `BS(m,n)` is already known (Bux-Llosa Isenrich-Wu). This node only says which *explicit Thompson-like hosts*
  can carry which Baumslag-Solitar groups through their odometers.
