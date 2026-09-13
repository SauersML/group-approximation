---
rg: 2
id: finite-simple-groups-converge-to-simple-kazhdan-group
kind: claim
title: Finite simple groups PSL_N(F_q) with bounded generating sets converge in marked-group space to an infinite simple Kazhdan group
distinct_from:
  torsion-free-kazhdan-alternating-mother-limit-gate: that asks for a torsion-free simple Kazhdan marked limit of alternating quotients of a torsion-free Kazhdan mother; this gives a simple Kazhdan marked limit of projective special linear quotients of a Kazhdan mother, with torsion.
  simple-kazhdan-lef-group-from-minimal-subshift: that is the group and its approximation properties; this is the marked-group limit statement, with explicit finite simple approximants and an explicit Kazhdan mother.
artifacts:
  - research/artifacts/simple-kazhdan-lef-consequences-and-sources-2026-09-12.md
---

Let `q` be a prime power and `X` an infinite minimal subshift over an alphabet `A`. Put
`R = LC(X,F_q) ⋊ Z` and `S = EL_3(R)/Z`, marked by the images of `e_ij(1)`, `e_ij(c_0)` for a fixed
generator `c_0` of `F_q^x`, `e_ij(u^(±1))` and `e_ij(chi_[x_0=a])`. The scalar generator is needed only
when `q` is not prime. There are integers `N_k -> infinity` and markings of the finite simple groups
`PSL_(3N_k)(F_q)` such that

```text
(PSL_(3N_k)(F_q), S_k)  ->  (S, S_bar)     in the space of marked groups.
```

Moreover every approximant, and `S`, is a marked quotient of the Kazhdan group
`EL_3(F_q<t_1, ..., t_(|A|+2)>)`. That group is marked by `e_ij(1)`, `e_ij(c_0)` and `e_ij(t_s)`, with the
`t_s` sent to `u`, `u^(-1)` and the letter indicators. So the approximants form a family of uniform
expanders, and a Kazhdan mother can have finite simple quotients whose marked limit is an infinite
simple Kazhdan group.

For `q = p^e` with `e > 1` the scalar markings `e_ij(c_0)` are necessary, not optional. Without them
the markings generate only `EL_3(LC(X,F_p) ⋊ Z)`, because products of elementary matrices over a
subring keep their entries in that subring. Any `λ` with `F_p[λ] = F_q` can replace `c_0`.

The markings come from primitive periodic return words `z_k` of `X`: `u` is sent to the cyclic
shift, `chi_[x_0=a]` to the indicator of the positions of `a` in `z_k`, and `c_0` to `c_0 I`.

## Attempts

- **Periodic models plus simplicity (2026-09-12).** Artifact Part 2, §8.1. The partial maps of
  `minimal-subshift-algebra-is-simple-lef-ring` are injective and multiplicative on balls. For
  primitive `z_k` the images generate `M_(N_k)(F_q)`, hence `SL_(3N_k)(F_q)`. Scalars outside the
  finite centre of `EL_3(R)` are eventually not ratios of ball elements, so the projective
  quotients converge to `S`.

  Simplicity comes from `simple-kazhdan-lef-group-from-minimal-subshift` (reviewed PASS 0efeac410).
  The route is `finite-simple-groups-converge-to-simple-kazhdan-group-proof`. The primitive-root
  step of §8.1 was not part of that review's scope.

  **Update 2026-09-13.** The second review (`ex-pestov91-harden`, badc66e2d7, note N5) checked that step:
  - Morse--Hedlund gives `N_k >= 2k+2`;
  - the rotations of a primitive `z_k` separate positions, so the images generate `M_(N_k)(F_q)`;
  - if a word's image is scalar for infinitely many `k`, the word is central in `EL_3(R)`.

  Full proof: write-up Part 2 §5.4 (`research/artifacts/pestov-9-1-writeup-2026-09-13-part2.md`).
