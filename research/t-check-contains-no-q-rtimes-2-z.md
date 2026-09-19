---
rg: 2
id: t-check-contains-no-q-rtimes-2-z
kind: claim
title: T-check contains no copy of Q x|_2 Z; a doubled rank-one rational group A x|_2 Z lies in T-check only when A is Z[1/2], because the doubling semiconjugacy pulls dyadic boundary data back to bounded odd denominators
distinct_from:
  t-check-contains-q-rtimes-2-z: that is the open existence question; this answers it negatively, in the minimal and in the blown-up case at once.
  q-x2-z-in-t-check-has-a-doubling-semiconjugacy: that constructs the semiconjugacy h and constrains every copy; this uses h to show that no copy exists.
  q-x2-z-in-t-check-blows-up-the-doubling-fixed-point: that excludes the copies whose fibre h^-1(0) is a point, by one-dimensional dynamics; this excludes all copies by boundary arithmetic, with no minimality, entropy or measure theory.
  rational-rotations-and-doubling-have-no-common-tree-coding: that needs a coding in which the rotations are exact (the collapse map is injective off the rationals); this drops injectivity, since only cells of positive h-mass are used, so Denjoy blow-ups do not escape it.
  fg-pl-quasi-similarity-groups-contain-no-gl-2-q: that excludes Aff(Q), B_2(Q), SL_n(Q), GL_n(Q) from periodic PL quasi-similarity groups through the scaling lemma; this excludes the smaller stepping stone Q x|_2 Z, which the scaling lemma allows.
---

**ESTABLISHED** by `t-check-contains-no-q-rtimes-2-z-proof` (lane bh-free-16, 2026-09-18; elementary;
not reviewed; no priority claimed). It settles `t-check-contains-q-rtimes-2-z` in the negative.

## Setting

As in `q-x2-z-in-t-check-has-a-doubling-semiconjugacy`:
- `T-bar` is the group of lifts to `R` of Thompson's circle group `T`;
- `δ(x) = 2x`, and `T-check = <T-bar, δ>` is the finitely presented ascending HNN extension of `T-bar`;
- for a nonzero subgroup `A <= (Q,+)` that is 2-divisible (`a/2 ∈ A` for all `a ∈ A`), put
  `G_A = A x|_2 Z = <A, t | t a t^-1 = 2a>`. So `G_(Z[1/2]) = BS(1,2)` and `G_Q = Q x|_2 Z`.

A *dyadic interval* is `[j 2^-n, (j+1) 2^-n]` with `j, n ∈ Z`.

## Theorem

1. **Rigidity.** `G_A` embeds in `T-check` if and only if `A ≅ Z[1/2]`, that is, iff `G_A ≅ BS(1,2)`.
2. **In particular** none of `Q x|_2 Z`, `Z[1/6] x|_2 Z`, `Z[1/2, 1/p] x|_2 Z` (`p` odd) embeds in `T-check`.
   Nor does any group containing one of them: `Aff(Q)`, `B_2(Q)`, `GL_n(Q)` (already excluded by
   `fg-pl-quasi-similarity-groups-contain-no-gl-2-q`), and also the finitely presented metabelian group
   `Z[1/6] x| Z^2`, which contains `Z[1/6] x|_2 Z`.

The "if" direction is `BS(1,2) = <τ_1, δ>`, with `δ τ_1 δ^-1 = τ_2 = τ_1^2`.

## General form (the tool)

The proof uses only the following, which holds well beyond `T-check`.

**Tame dyadic semiconjugacy lemma.** Call a homeomorphism `f` of `R` *tame dyadic* if there is `N` such that
`f` is affine on every dyadic interval of length `<= 2^-N` and maps it onto a dyadic interval. (Every
element of `T-check` is tame dyadic.) Let `t` be tame dyadic and let `h : R → R` be continuous,
non-decreasing, onto, with `h(x+1) = h(x) + 1` and `h ∘ t = δ ∘ h`. Then there is an odd integer
`M = M(t, h)` with the following property. If `q` is tame dyadic and `h ∘ q = h + s` with `s ∈ Q`, then the
odd part of the denominator of `s` divides `M`.

The mechanism has three parts.
- **Boundary data.** The data are the `h`-values of the endpoints of dyadic intervals `I` with
  `h`-mass `μ(I) = |h(I)| > 0`.
- **Pull-back.** `t` doubles `μ`, so iterating `t` carries every such interval to a large dyadic interval
  in boundedly many steps. So every boundary value `x` satisfies `2^k x ∈ E (mod 1)` for one finite set `E`.
- **Arithmetic.** For a finite `E ⊆ R/Z`, even with irrational points, the rational points of the difference
  set of `{x : 2^k x ∈ E for some k}` have bounded odd denominators.

Cells of `h`-mass zero, which are the blown-up intervals, are never used. So the lemma holds for
semiconjugacies, not only for conjugacies. The same proof works for any radix `d >= 2`, with `d`-adic intervals,
`x ↦ dx`, and the `d`-free part of denominators. It also works on the circle and on Cantor codings `π` that send cells to arcs,
which extends `rational-rotations-and-doubling-have-no-common-tree-coding` from exact register codings to
arbitrary monotone collapses.

## What this closes

- `t-check-contains-q-rtimes-2-z` is false. The whole blown-up case left open by
  `q-x2-z-in-t-check-blows-up-the-doubling-fixed-point` (the family `F_s` and the closed set `K'`) is excluded
  as well.
- `T-check` is the natural "Belk–Hyde–Matucci plus dilation" host. It contains `Q` and `BS(1,2)`, yet no
  rational Baumslag–Solitar group beyond `BS(1,2)`. So the divisible part and the dilation part of `Aff(Q)`
  cannot be joined inside one single-radix PL real coordinate, even through a singular semiconjugacy.
- Together with `rational-rotations-and-doubling-have-no-common-tree-coding`,
  `v-element-invariant-measures-live-on-the-periodic-part` and
  `no-free-q-odd-action-by-v-has-a-doubling-intertwiner`, every host in which `Q x| <d>` would act on one
  real or circle coordinate through single-radix germs is now excluded. This holds for exact codings,
  semiconjugate codings, homeomorphic dilations and covering dilations alike.

## Lesson for general BH

**Blow-ups do not evade boundary arithmetic.** Almost-automorphic dynamics carries arithmetic in the
boundary points of its cells.
- An expanding map pulls finitely many boundary classes back along the positive-mass cells.
- So everything the expanding map normalizes can shift boundaries only by rationals whose denominators are bounded up to
  powers of the radix.
- The obstruction reads only cells of positive mass, so it survives every monotone semiconjugacy (Denjoy
  blow-ups, collapsed gaps) and needs no minimality, entropy or invariant measure.

For `Aff(Q)` and `GL_n(Q)` hosts the design rule sharpens. The copy of `Q` must not have a circle or line
factor on which the dilation acts through one radix. The prime arithmetic must sit elsewhere:
- in germs whose cells are not single-radix intervals (Stein slopes, where "large cells have bounded
  denominators" fails);
- in several coordinates mixed by the dilation;
- or in the acting group of a crossed product (the master route).

A finite boundary set seen by an expanding map buys only one bounded denominator (up to the radix) per
coordinate, whatever the dynamics.
