---
rg: 2
id: kms-lamp-mixing-dies-on-br-relation
kind: claim
title: For domains containing a counter pair (u, 1 − u), such as Kochloukova–Sidki's, the simplest KMS lift that mixes the top into T, F(A_0) = tA_0 with t in T_0 and the counters of B_0 sent into B_0, is incompatible with the BR relation G4 (for power-type domains U^n central lamp mixing is not excluded), because G4 is inhomogeneous in A_0 while B_0 centralizes T_0; a T-component can instead enter through the counters, F(ã_i) = t_i α_i, where it is a 1-cocycle and induces T_0-components t_i(A_0 − 1) on the lamps
distinct_from:
  kms-lift-must-mix-top-core-into-configurations: that proposes F(A_0) = tA_0 with t in T_0 (its Part D); this shows that proposal fails and moves the mixing to the counters.
  kms-top-every-counter-cycle-must-contract: that forces contraction on the top, which is why mixing is needed at all.
  two-counter-kms-groups-are-self-similar: that is the crux KD2_p; this is an attempt record under it.
---

**ESTABLISHED (lane bh-kd2p, 2026-09-19; **referee PASS with scope repair**, bh-ref-g, 28f69471d1): the negative in Step 1 is a lane proof, for domains containing a counter pair; Steps 2 and 3 are an attempt
record. KD2_p stays OPEN. Not independently reviewed.**

KMS relations as transcribed in `kms-configuration-lift-needs-non-contracting-counters` (arXiv:1204.6506v5 §4.1).

## Step 1. `F(A_0) = tA_0` with `t ∈ T_0` fails

**`B_0` centralizes `T_0`.**
- By G5c, every `x_u` with `A_0 ∈ u` commutes with `M_0 = {ã_i, ã_i', A_0}`, so with all of `B_0 = ⟨M_0⟩`.
- `T_0` is spanned by such `x_u` times `F_p[B_1 × ⋯ × B_K]`, and `B_0` commutes with the `B_i` (G2).
- So `B_0` centralizes `T_0`.

**G4 is inhomogeneous in `A_0`.** In the lamp group it reads `A_0^{ã^{-1}}·A_0^{-1} = A_0^{(ã')^{-1}}`, for each
BR pair `(ã, ã')`. The letter `A_0` has total exponent 0 on the left and 1 on the right.

**Scope.** The argument below needs `A_0` and one BR pair in the domain `H`, or more generally one pair
`(u, 1 − u)` of counters, up to the unit relation.
- Kochloukova–Sidki's domain has this: it contains `x_2` and `y_2 = g(x_2)`.
- **The general criterion.** A central `t` is killed as soon as some annihilator of `A_0` in `F_p[U_H]` has
  augmentation `≢ 0 mod p`.
- **When `t` survives.** Only when the augmentation map factors through `F_p[U_H] ⊆ R`. By lying-over this
  means `U_H ⊆ ker(ev_z)` for some point `z`, i.e. every counter in the domain equals 1 at some `z` where all
  `s_i` and `1 − s_i` are roots of unity.
- **Which domains that excludes.** Any domain containing a pair `(u, 1 − u)`, since `1 = 1 − 1` is impossible.

**The contradiction.** Suppose `F(A_0) = L = tA_0` with `t ∈ T_0`, and `F` maps the BR letters of `H` into `B_0`.
- Since `t` is central for `B_0`, `L^g = t·A_0^g` for all `g ∈ B_0`.
- Applying `F` to the relation gives `A_0^{α^{-1}}A_0^{-1} = t·A_0^{β^{-1}}`, with `α = F(ã)` and `β = F(ã')`.
- Modulo `T` this is the relation for the induced map `F̄`, so it holds there. What remains is `t = 1`. ∎

**The same holds, for domains containing a counter pair `(u, 1 − u)`, for every grade of `T` centralized by the image.** A central component of a lamp image
contributes to each side of a relation in proportion to its exponent sum. So an inhomogeneous relation kills it.

## Step 2 (attempt record). Non-central components satisfy a graded linear system

- Write `T` graded by the set `w` of `A`-letters in `u`. For `t` with components `t_w`, G4 splits by grade.
  - For `0 ∉ w`: `t_w·O_w = 0`, with `O_w = α^{-1} − 1 − β^{-1}` acting on grade `w`.
  - For `0 ∈ w`: the image acts trivially there, so `O = −1`, and `t_{w∪0} = −t_w·(A_0 − 1)·(fixed operator)`.
- On `T_∅ = F_p[Q]·x_{q_j}`, G6 and G5b make `ã` act as `a` and `ã'` as `a − 1`.
  - For `F̄ = id` on a BR pair, `O_∅ = a^{-1} − 1 − (a − 1)^{-1} = −(a^2 − a + 1)/(a(a − 1))`.
  - That is a nonzero non-unit. That it is injective on `T_∅` is **not justified**: `F_p[Q]` has zero divisors, since the lamps have order `p` and `(A − 1)^p = 0`. It needs an argument such as `T_∅` being torsion-free over the counter ring (bh-ref-g, 28f69471d1). Until then `t_∅ = 0` is conditional.
- For renormalized `F̄`, `O_w` is the image of the BR polynomial, again nonzero, and the same conclusion is
  expected. That is not checked for every grade.
- **Expected outcome.** `F(A_0) ∈ T·A_0` forces `t = 0`, so the lamp image of `A_0` itself stays in the top.

## Step 3 (the surviving route). The mixing goes through the counters

- **The relations between counters are homogeneous.** `H_2` is abelian, and conjugating a lamp by `ã` involves
  `ã` with exponent sum 0. So components `F(ã_i) = t_i·α_i` with `t_i ∈ T` are allowed. They are constrained
  only by the cocycle condition coming from `[F(ã_i), F(ã_k)] = 1` and the BR pairs.
- **They reach the lamps.** `F(A_0^g) = F(g)^{-1} A_0 F(g) = A_0^{α_g}·(t_g(A_0 − 1))^{α_g}`. So the images of
  lamps in `B_0`'s core acquire components `t_g(A_0 − 1) ∈ T_0`, exactly the grade that `B_0` centralizes and
  that carries the machine.
- **Coboundaries are useless.** If `t_i = s(α_i − 1)` for one `s ∈ T`, then `F` is conjugate by `s` to a
  top-preserving map, and faithfulness is unchanged. So the lift needs a **nontrivial class in
  `H^1(F̄(H ∩ B_0), T)`**, restricted to the counters. Its lamp components `t_g(A_0 − 1)` must separate the core
  `𝔟` under iteration.

## Lesson

**For domains containing a counter pair `(u, 1 − u)`, mixing the top into the machine module has to be done by the counters, not the lamps.** The BR relation is
inhomogeneous in the lamp and so kills central lamp-level mixing there. For power-type domains `U^n` the augmentation factors through the lamp ring, and central lamp mixing is open. Counter-level mixing is a 1-cocycle, and only its
cohomology class matters.
