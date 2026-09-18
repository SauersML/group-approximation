---
rg: 2
id: higman-thompson-roots-miss-a-kl-word-over-thompson-v
kind: claim
title: No homomorphism from V_w to a Higman-Thompson group is non-trivial on V for w = c t a t a t^-1, although Kervaire--Laudenbach holds for w; every endomorphism of V keeps the census S_3 of orbit type {1,3}
distinct_from:
  cone-diagonal-roots-miss-a-kl-word-over-thompson-v: that is the elementary special case of cone-diagonal endomorphisms and roots in Sym(C); this covers every homomorphism V -> V_{n,1}, so all endomorphisms of V, and it closes the gate that claim left open.
  thompson-v-endomorphism-breaking-the-s3-orbit-type: that is the gate question (does some injective endomorphism of V break the orbit type?); this proves the answer is no and so refutes it.
  cantor-homeomorphisms-miss-a-unimodular-root: that is the Sym(Omega) obstruction for a fixed S_3-action; this shows every S_3-action on Cantor space reachable from V by a homomorphism into V_{n,1} has the obstructed orbit type.
  kl-holds-over-thompson-v: that is the positive statement over V; this kills its proofs by internal roots in Higman-Thompson groups and does not decide it.
artifacts:
  - research/artifacts/kl-thompson-v-internal-roots-2026-09-17.md
---

**Setting.** `V` acts on `C = {0,1}^N` with the census generators
`a = (00 01)` and `c = (1 00)`, so `F = <a, c> ≅ S_3`. For `n >= 2`,
`V_{n,1}` is the Higman--Thompson group acting on `X_n = {1..n}^N`. The word
is `w0 = c t a t a t^(-1)`, census form `ctataT`, and
`V_{w0} = (V * <t>)/<<w0>>`.

1. **Orbit type.** For every non-trivial homomorphism `rho : V -> V_{n,1}`,
   every `rho(F)`-orbit on `X_n` has size `1` or `3`, and at least one has
   size `3`. In particular this holds for every non-trivial endomorphism of
   `V`, and every non-trivial endomorphism of `V` is injective.
2. **No Higman--Thompson root.** No homomorphism `psi : V_{w0} -> V_{n,1}` is
   non-trivial on `V`. Equivalently, no non-trivial `rho : V -> V_{n,1}` and
   `x in V_{n,1}` give `rho(c) x rho(a) x rho(a) x^(-1) = 1`. Even with `x`
   allowed to range over `Sym(X_n)`, there is no such pair.
3. **Kervaire--Laudenbach holds for `w0` over `V`.** This is item 1 of
   `cone-diagonal-roots-miss-a-kl-word-over-thompson-v`.

## What it kills

**The method.** It is the internal-root certificate for
`kl-holds-over-thompson-v`: `V -> V_w` is injective because some
homomorphism `V_w -> H` is injective on `V`, with `H` a Higman--Thompson group
and `V` re-embedded by any homomorphism. The certificate includes the census
RETRACT certificates, the 2026-09-17 internal-root search, every
`Omega_2`-system endomorphism of `V`, and any target `V_{n,1}`. It already
fails at `w0`, a degree-one word where the conjecture is true.

**Where it dies.** Step 3 of the proof. Matte Bon's classification gives a
`V`-equivariant coding map `q : Z -> C`. Each `rho(g)` is the identity on
`q^(-1)(U)` whenever `g` is the identity on the cone `U`. Every point of `C`
lies in a cone fixed pointwise by one of the three transpositions of `F`, so
the orbit type stays `{1,3}`. Then
`cantor-homeomorphisms-miss-a-unimodular-root`, item 2, forbids the root.

**What survives.**
- Proofs that combine internal roots with localization to the coefficient
  subgroup (`kl-failure-localizes-to-the-coefficient-subgroup`). Such a proof
  handles `w0` through finite `F`.
- Internal roots in ambients whose homomorphisms from `V` are not spatial in
  Matte Bon's sense. Case (i) of his Extension Theorem 1.3, and targets that
  need symmetric powers `X^[r]` with `r >= 2`, are not covered here.

**What it does not say.**
- Nothing about individual census frontier words, whose coefficients generate
  `V`.
- Nothing about whether a violation exists.

**ESTABLISHED** through `higman-thompson-roots-miss-a-kl-word-over-thompson-v-proof`.
- It imports `thompson-v-homomorphisms-into-higman-thompson-are-coded`
  (Matte Bon) and `cantor-homeomorphisms-miss-a-unimodular-root`.
- It uses item 1 of `cone-diagonal-roots-miss-a-kl-word-over-thompson-v`,
  together with Steps 1, 2 and 4 of its proof.
