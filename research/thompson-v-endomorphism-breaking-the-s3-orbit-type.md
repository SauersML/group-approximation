---
rg: 2
id: thompson-v-endomorphism-breaking-the-s3-orbit-type
kind: claim
title: Some injective endomorphism of Thompson's group V gives the census S_3 = <a,c> an orbit of size two or six on Cantor space
refuted_by:
  - higman-thompson-roots-miss-a-kl-word-over-thompson-v
distinct_from:
  cone-diagonal-roots-miss-a-kl-word-over-thompson-v: that proves cone-diagonal endomorphisms keep <a,c> of orbit type {1,3} and so never give internal roots of ctataT; this asks whether any injective endomorphism of V at all breaks that orbit type, which is the gate for every internal-root proof over V.
  cantor-homeomorphisms-miss-a-unimodular-root: that is the Sym(Omega) obstruction for a fixed S_3-action; this asks which S_3-actions the endomorphism monoid of V can reach from the rigid one.
  kl-holds-over-thompson-v: that is the positive statement over V; this is a necessary condition only for proofs of it by internal roots after an endomorphism.
---

**REFUTED (2026-09-17).**
- `higman-thompson-roots-miss-a-kl-word-over-thompson-v`, item 1, shows
  that every non-trivial homomorphism `V -> V_{n,1}`, and so every
  endomorphism of `V`, keeps `<a,c>` of orbit type `{1,3}`.
- The route: Matte Bon's classification (arXiv:1801.10133v2, Theorem 11.12)
  gives a `V`-equivariant coding map `q`. A transposition that is the
  identity on a cone acts as the identity on the preimage of that cone.
- So internal roots after endomorphisms cannot prove
  `kl-holds-over-thompson-v`: the method is dead over `V` and over every
  Higman--Thompson target.

The original statement and attempts are kept below as history.

Let `a = (00 01)` and `c = (1 00)` in `V`, so `<a,c> ≅ S_3`, and
every `<a,c>`-orbit on `C` has size `3`
(`cone-diagonal-roots-miss-a-kl-word-over-thompson-v-proof`, Step 2). The
claim is that some injective endomorphism `phi : V -> V` has a point `y in C`
whose `phi(<a,c>)`-orbit has size `2` or `6`.

## Why it gates internal-root proofs over V

**The certificate.** Take the certificate "`w^phi(t0) = 1` with
`t0 in V` and `phi` injective". It proves injectivity of `V -> V_w`, and it
is the only certificate that has closed census words at scale: RETRACT, and
the internal roots of 2026-09-17.

**The gate.** Suppose every injective `phi` kept `phi(<a,c>)` of orbit type
`{1,3}`. Then `cantor-homeomorphisms-miss-a-unimodular-root`, item 2, would
forbid a root of `ctataT^phi` in `Sym(C)`, while Kervaire--Laudenbach holds
for `ctataT`. So:
- **If this claim is false,** no proof of `kl-holds-over-thompson-v` by
  internal roots after endomorphisms exists, and the method is dead over V.
- **If it is true,** the witnessing endomorphisms are the only ones worth
  searching for the census frontier.

## Attempts

1. **Cocycle skew products do not break the type.** Status: sketch, not
   established.
   - **The family.** Let `theta : V x C -> S_k` be a locally constant
     cocycle for the action. Let `V` act on `C x {1..k}`, identified with
     `k` cones, by `(x, i) g = (x g, theta(g, x)(i))`. These are prefix
     replacements, so they give endomorphisms of V, and the family contains
     the cone-diagonal ones.
   - **Trivial holonomy on rigid stabilizers.** Take `x` in the interior of
     a clopen set `U` fixed pointwise by the elements supported off `U`. That
     subgroup is isomorphic to V, hence simple, so `theta(., x)` is a
     homomorphism from it to `S_k` and is trivial. In particular
     `theta(a, x) = 1` for `x` in cone `1`, and similarly for `c` on cone `01`
     and `aca` on cone `00`.
   - **Consequence.** Each point `(x, i)` is fixed by the transposition that
     fixes the cone of `x`. So orbits keep size `1` or `3`.
   - **What is missing.** A proof that every injective endomorphism is of
     this form.
2. **What a counterexample must look like.**
   - **The stabilizer.** Let `K_y` be the stabilizer of `y` under the
     `phi`-action. It must contain none of `a`, `c`, `aca`, and all three are
     rigid stabilizer elements of cones.
   - **Where to look.** For confined `K_y`, results of Le Boudec--Matte Bon
     type (confined subgroups of groups with micro-supported actions contain
     rigid stabilizers of finite sets) would put `K_y` above the rigid
     stabilizer of a finite set. This is recalled from memory, not pinned by
     a citation.
   - **Finite sets of two or more points.** Points in different cones allow
     `<a,c> ∩ K_y = 1`, as for `V` acting on ordered pairs of points. That
     action is not by prefix replacements.
   - **The sharp version.** Does some V-orbit of pairs, or some other
     confined V-set with two or more points and no one-point rigid
     stabilizer, arise as an orbit of `phi(V) <= V` on `C`? No example and no
     obstruction is known here.
