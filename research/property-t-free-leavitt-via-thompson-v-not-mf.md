---
rg: 2
id: property-t-free-leavitt-via-thompson-v-not-mf
kind: route
title: Push the MF radical of the Kazhdan-blind Thompson subgroup into the simple Leavitt Steinberg group
target: property-t-free-leavitt-full-mf-radical
requires:
  - thompson-v-is-not-mf
  - thompson-v-lifts-through-binary-leavitt-steinberg-cover
  - leavitt-corner-host-is-the-simple-leavitt-unit-group
  - thompson-v-has-haagerup-property
---

**Chain.**
1. `thompson-v-lifts-through-binary-leavitt-steinberg-cover` gives an
   injective homomorphism `iota : V -> St_20(R) = Delta`, with
   `R = L_(F_2)(1,2)`.
2. `thompson-v-is-not-mf` gives `Rad_MF(V) = V`, since `V` is simple.
3. Push forward along `iota`. Any homomorphism `psi : Delta -> M` to an MF
   group restricts to `psi o iota : V -> M`, which kills `Rad_MF(V) = V`. So
   `iota(V) <= Rad_MF(Delta)`.
4. `Rad_MF(Delta)` is normal and nontrivial. By item 1 of
   `leavitt-corner-host-is-the-simple-leavitt-unit-group`, `Delta` is simple.
   So `Rad_MF(Delta) = Delta`, and in particular `z = x_13(s_1t_1)` lies in it.

**Kazhdan hygiene.**
- Steps 1 and 4 are ring theory. They use Khanh's Steinberg comparison,
  simplicity of `EL_3` of the Leavitt algebra, and the splitting of central
  extensions of `V`. None of these uses (T) or spectral gaps.
- Step 3 is the definition of the radical.
- The hole's own group is Kazhdan-blind by `thompson-v-has-haagerup-property`:
  - every Kazhdan subgroup of `V` is finite;
  - every finite presentation cover of `V` is non-Kazhdan;
  - the rigid-defect engine is vacuous inside `V`, by
    `thompson-v-has-no-rigid-compression-defect`.
- So neither `kazhdan-asymptotic-commutant-transport` nor any compression
  defect can feed the hole with an infinite Kazhdan source.
- This is the image-typed sense of "Kazhdan-free" isolated by
  `kazhdan-free-leavitt-collapse-typing-dichotomy`. That node shows that the
  certificate-typed sense is already met through (T), so it is not a real
  restriction.

**Why this is the economical Kazhdan-blind witness.** By
`kazhdan-free-leavitt-collapse-typing-dichotomy` (d), any image-typed proof
exhibits a non-MF Kazhdan-blind group `Gamma` with a homomorphism
`Gamma -> Delta` whose radical image is nontrivial.
- For a Haagerup subgroup `K` with `V <= K <= Delta`, the statement
  "`K` is not MF" is implied by this hole. It is a weaker hole, with the
  same closing chain.
- `V` is the canonical finitely presented simple one, since
  `leavitt-mf-quotients-see-thompson-vd-through-parity` already puts it
  inside `Rad_MF(Delta)` through (T).
- Any subgroup `K <= V` with `Rad_MF(K) != 1` also closes the route, because
  step 3 applies with `K` in place of `V`. Examples of candidates are `F`,
  `T`, or the Houghton groups.

**Status.** OPEN, with one hole: `thompson-v-is-not-mf`. The other three
requirements are ESTABLISHED.

**Direction of belief.** The hole implies that a Haagerup group can fail to
be MF. That would be the first such example recorded here.

By the dichotomy (d), the image-typed goal implies that some Kazhdan-blind
group is not MF. So anyone who believes every Kazhdan-blind group is MF must
believe that the image-typed goal is false. Anyone who believes only that
Haagerup groups are MF must look for a Kazhdan-blind witness without the
Haagerup property. Such a witness is not inside `V`, since every subgroup of
`V` is Haagerup.
