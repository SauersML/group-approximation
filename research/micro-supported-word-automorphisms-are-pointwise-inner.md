---
rg: 2
id: micro-supported-word-automorphisms-are-pointwise-inner
kind: claim
title: A spatial automorphism of a micro-supported group that is given by a one-variable word map agrees at every point with one of finitely many group elements, and for Higman--Thompson circle kernels it is conjugation by an element of T_{n,r}
distinct_from:
  outer-extensions-of-fp-simple-mif-groups-satisfy-pbh: that proves one-variable word automorphisms of an MIF group are inner, by normal forms in S * <y>; this needs no MIF hypothesis and proves a pointwise statement from supports, which is what reaches the non-MIF Thompson circle kernels.
  thompson-t-mixed-identity-problem-is-decidable: that decides which words in S * <y> are mixed identities of F and T; this is about words whose evaluation map is an automorphism, and uses no decision procedure.
  fg-simple-line-groups-have-no-one-sided-supports: that forbids micro-supported actions of finitely generated simple groups on the line; this uses micro-supported actions on Hausdorff spaces such as the circle, where they exist.
---

**ESTABLISHED** by `micro-supported-word-automorphisms-pointwise-inner-proof`.
Not independently reviewed. No priority is claimed.

## Statement

Let `S` act faithfully on a Hausdorff space `Y`, and assume the action is
micro-supported: `rist_S(U) != 1` for every nonempty open `U`. Call `β ∈ Aut(S)`
a *word automorphism* if there is `u ∈ S * <y>` with `β(t) = u(t)` for all `t ∈ S`.

**(1) Pointwise innerness.** Let `r ∈ Homeo(Y)` normalize `S` and induce a word
automorphism `β = c_r|_S` with word `u`. Write `u = g_0 y^{e_1} g_1 ... y^{e_k} g_k`
and `h_j = g_0 g_1 ... g_{j-1}` for `1 <= j <= k`. Then

    Y = F_1 ∪ ... ∪ F_k ,      F_j = { p : r(p) = h_j(p) } .

Each `F_j` is closed.

**(2) Uniqueness.** The centralizer of `S` in `Homeo(Y)` is trivial. So `r` is
determined by `β`, and `β` is inner iff `r ∈ S`.

**(3) Higman--Thompson circle kernels.** Let `n >= 2` and `r_0 >= 1`. Let `T_{n,r_0}`
be the group of orientation-preserving PL homeomorphisms of `R/r_0 Z` with finitely
many breakpoints, all in `Z[1/n]`, slopes in `n^Z`, and mapping `Z[1/n]/r_0 Z` to
itself. Let `[T_{n,r_0}, T_{n,r_0}] <= S <= T_{n,r_0}`. Then:
- every word automorphism of `S` is conjugation by a unique element of `T_{n,r_0}`;
- if `W` is a subgroup of `Aut(S)` with `Inn(S) <= W` and every element a word
  automorphism, then `W/Inn(S)` embeds in the abelian group `T_{n,r_0}/S`. That group
  is finitely generated because `T_{n,r_0}` is (Brown, imported). So `W/Inn(S)` is
  finitely generated.

In (3), all automorphisms are assumed spatial. This is Rubin's theorem for the
locally dense action on the circle (M. Rubin, Trans. AMS 312 (1989), imported, not
re-read). The same import underlies Brin's computation `Out(T) = Z/2` and Olukoya's
description of `Aut(T_{n,r})` (arXiv:1908.03816, abstract read 2026-09-17: `Out(T_{n,r})`
is infinite for `n > 2` and contains a copy of `F`).

## Why it matters

Proposition 9 of `research/artifacts/outer-extensions-mif-pbh-2026-09-16.md` splits
the non-MIF residue of `decidable-groups-embed-in-outer-extensions-of-fp-simple-groups`
into two conditions:
- (a) BFFHZ Question 3.2 for `S`;
- (b) finite normal generation of `W/Inn(S)`, where `W = ρ(K)` is a group of word
  automorphisms.

Item (3) discharges (b) for every Higman--Thompson circle kernel and every `B`.
These kernels are the ones BFFHZ single out as the hard non-MIF case ("even for
example for Thompson's group T"). See
`thompson-circle-kernel-outer-extensions-reduce-to-bffhz-q32`.

## Not claimed

- **General micro-supported kernels.** For those, (1) places `W` inside the group
  `L(S)` of normalizing homeomorphisms that are finitely closed-piecewise in `S`.
  Whether `L(S)/S` is always finitely generated is not examined. The circle argument
  uses PL structure: connected pieces and breakpoint bookkeeping.
- **Actions that are not micro-supported.** Nothing is said about them.
