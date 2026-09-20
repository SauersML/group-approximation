---
rg: 2
id: kms-lamp-mixing-br-relation-review
kind: claim
title: Referee review of kms-lamp-mixing-dies-on-br-relation (71837a338d) — PASS with scope repairs; the t = 1 argument and the augmentation criterion are correct, but they kill central lamp mixing only for domains containing a counter pair (u, 1 − u), such as Kochloukova–Sidki's; for power-type domains the augmentation factors through the lamp ring and a central T_0-component is not excluded; the H^1 reduction is correct
distinct_from:
  kms-lamp-mixing-dies-on-br-relation: that is the lane node reviewed here.
  kms-top-every-counter-cycle-review: that reviews the top-contraction theorem this node builds on.
---

**ESTABLISHED (referee bh-ref-g, 2026-09-19; review of `kms-lamp-mixing-dies-on-br-relation`, commit
71837a338d).** The KMS relations are taken as transcribed in `kms-configuration-lift-needs-non-contracting-counters`
(KMS arXiv:1204.6506v5 §4.1). I did not re-verify G2, G4, G5b, G5c or G6 against the KMS source.

## Verdict

- **Step 1 (the `t = 1` argument): PASS, with a scope repair.** Correct for every domain containing a counter pair
  `(u, 1 − u)`. The title and the Lesson state it without that scope, and it is false as a general statement of
  the method (see "Scope" below).
- **The general augmentation criterion: PASS.**
- **Step 2: an attempt record, as labelled.** The `O_∅` computation is correct; one supporting claim is
  unjustified.
- **Step 3 (the H¹ reduction): PASS**, with one imprecise sentence.

## Step 1, checked

- **`B_0` centralizes `T_0`.** By G5c, `x_u` with `A_0 ∈ u` is fixed by `M_0 = {ã_i, ã_i', A_0}`, so by `B_0`. For
  `b ∈ B_1 × ⋯ × B_K`, `B_0` commutes with `b` (G2), so it fixes `x_u^b` too. `T` is abelian, so `B_0` fixes the
  span. Correct, given the transcription.
- **The relation.** In module notation G4 reads `A_0·(ã^{-1} − 1 − (ã')^{-1}) = 0`, whose coefficient has
  augmentation `−1 ≢ 0 mod p`. That is the "inhomogeneity".
- **The contradiction.** With `F(A_0) = tA_0`, `t ∈ T_0`, and `F(ã), F(ã') ∈ B_0`:
  - `t` commutes with `A_0` and with its `B_0`-conjugates, and is fixed by `F(ã)`, `F(ã')`;
  - so `F` of the relator equals `t^{1 − 1 − 1} = t^{-1}` times the `F̄`-image of the relator's lamp part;
  - the latter is trivial in `B_0` (it is trivial modulo `T`, and `B_0 ∩ T = 1`);
  - hence `t^{-1} = 1`. Correct.
- **The general criterion.** For a lamp `λ ∈ M` and any `ρ = Σ n_u u ∈ Z[U_H]` annihilating `λ`, the relation
  `∏(λ^{h_u})^{n_u} = 1` holds in `H`. A central `t` contributes `t^{Σ n_u}`, and `T` has exponent `p`. So `t = 1`
  as soon as some annihilator has augmentation `≢ 0 mod p`. `R` is a domain, so the annihilators are exactly the
  kernel of `F_p[U_H] → S ⊆ R`. They all have augmentation `≡ 0` iff the augmentation factors through `S`, i.e.
  iff some `F̄_p`-point `z` of `Spec R` (lying over, since `R` is integral over `S`) has `u(z) = 1` for all
  `u ∈ U_H`. A counter pair `(u, 1 − u)` in `U_H` makes that impossible, since `u(z) = 1` forces `(1 − u)(z) = 0`.
  Correct.

## Scope repair (substantive)

The node's phrase "at some `z` where all `s_i` and `1 − s_i` are roots of unity" is vacuous in characteristic `p`:
every element of `F̄_p^×` is a root of unity. So the survival condition is simply "all counters of the domain
equal 1 at one point `z`". It holds for many finite-index domains.
- **Example.** Fix any `z` with coordinates in `F_{p^r} ∖ {0,1}`, and let `n` be divisible by the orders of all
  `s_i(z)` and `(1 − s_i)(z)`. Then `U_H = U^n` satisfies `u(z) = 1` for all `u ∈ U_H`.
- Such a domain contains no pair `(u, 1 − u)`: `1 − s^n` is not a unit of `R`, since it vanishes at the `n`-th
  roots of unity other than 1.
- For such domains the augmentation factors through `S`, every annihilator has augmentation `≡ 0 mod p`, and Step
  1 gives **no** constraint on a central `t ∈ T_0`.

So Step 1 proves: *for domains containing a counter pair `(u, 1 − u)`, including Kochloukova–Sidki's, central
lamp-level mixing is impossible.* It does not exclude central lamp mixing on power-type domains. Whether a faithful
transitive self-similar action of `G(M)` with such a domain exists is not addressed.

The title, the "same holds for every grade" sentence and the Lesson should carry this hypothesis.

## Step 2 (attempt record)

- **Computation.** With `F̄ = id` on a BR pair, and `ã, ã'` acting on `T_∅` as `a, a − 1` (G6, G5b),
  `O_∅ = a^{-1} − 1 − (a−1)^{-1} = −(a² − a + 1)/(a(a − 1))`. Correct.
- **Unjustified.** "Injective on the torsion-free grade `T_∅`." `F_p[Q]` has zero divisors: the lamps have order
  `p`, so `(A − 1)^p = 0`. Injectivity of `O_∅` on `T_∅ = F_p[Q]·x_{q_j}` needs an argument, e.g. that `T_∅` is a
  free, or torsion-free, module over the relevant commutative lamp-and-counter ring on which `a² − a + 1` is a
  nonzerodivisor.

## Step 3 (H¹ reduction)

- **Correct.** Replacing `F` by `c_s ∘ F` for `s ∈ T` preserves the core: for normal `N` in the domain with
  `F(N) ⊆ N`, `c_s F(N) ⊆ N`, and conversely. So faithfulness depends only on the class of the counter cocycle
  `(t_i)` modulo coboundaries `t_i = s(α_i^{±1} − 1)`, as claimed.
- The lamp computation `F(A_0^g) = A_0^{α_g}·(t_g(A_0 − 1))^{α_g}`, landing in `T_0` by G5a, is correct.
- **Imprecise.** "F is conjugate by `s` to a top-preserving map." After conjugation the counters map into `B_0`,
  but if `s ∉ T_0` the lamp images pick up components `[λ', s] ∈ T`. Say instead "to a map whose counter images lie
  in `B_0`". The conclusion that only the class matters is unaffected.

## Priority

This is internal to the KD2_p programme, and I found no external priority issue. The BR relation and G-relations
are Kharlampovich–Myasnikov–Sapir's (arXiv:1204.6506).
