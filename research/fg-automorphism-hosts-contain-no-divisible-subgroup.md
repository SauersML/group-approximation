---
rg: 2
id: fg-automorphism-hosts-contain-no-divisible-subgroup
kind: claim
title: Automorphism groups of finitely generated residually finite groups, and finitely generated groups of automorphisms of schemes of finite type, contain no copy of (Q,+), hence no GL_n(Q) for n >= 2
distinct_from:
  kazhdan-subgroups-of-cremona-groups-are-residually-finite: that proves residual finiteness of finitely generated Kazhdan subgroups of Bir(P^n) through partial actions on reductions; this proves residual finiteness of every finitely generated group of regular automorphisms of a separated scheme of finite type over a field, with no Kazhdan hypothesis, and of Aut of every finitely generated residually finite group.
  fg-cremona-subgroups-have-arithmetic-linear-part: that treats birational maps, for which residual finiteness of finitely generated subgroups is open, and controls only their linear elements; this treats regular automorphisms, where every finitely generated subgroup is residually finite.
  piecewise-commutative-linear-hosts-miss-linear-gl-n-q: that excludes finitely-piecewise hosts with commutative-linear pieces; this excludes automorphism-type hosts, whatever the embedding.
  gl-n-q-explicit-natural-fp-overgroup: that is the open construction problem (Problem 2.7); this closes the automorphism-group rows of its host table except automorphism groups of non-residually-finite groups.
artifacts:
  - research/artifacts/gq-gq-explicit-2-aut-comm-hosts.md
---

**ESTABLISHED** through `fg-automorphism-hosts-contain-no-divisible-subgroup-proof`.
Lane proof, not independently reviewed. The two residual-finiteness statements are
classical (Baumslag 1963 for (a); Bass--Lubotzky, Israel J. Math. 44 (1983) 1--22,
for automorphism groups of schemes, whose exact hypotheses were not read at the
source). Both are reproved in the route, so nothing rests on those texts. No
priority is claimed.

## Statement

(a) If `Γ` is a finitely generated residually finite group, then `Aut(Γ)` is
residually finite.

(b) Let `K` be a field and `X` a separated scheme of finite type over `K`. Every
finitely generated subgroup of `Aut_K(X)` is residually finite.

(c) Consequently none of the following contains a subgroup isomorphic to `(Q,+)`:
- `Aut(Γ)`, or any subgroup of it, for `Γ` as in (a);
- any finitely generated subgroup of `Aut_K(X)`, for `X` as in (b).

In particular, for every `n >= 2`, none of them contains `GL_n(Q)`, `SL_n(Q)`,
`PSL_n(Q)`, `Aff(Q)`, `U_3(Q)` or the Borel subgroup `B_n(Q)`, since each contains
the divisible unipotent `(Q,+)`.

## Host classes this closes for Problem 2.7 and for the root

A finitely presented host `Γ_n` for `gl-n-q-explicit-natural-fp-overgroup` cannot
be any of the following, under any embedding of `GL_n(Q)` (not only the natural
one):
- `Aut(F_k)`, `Aut(π_1 Σ_g)`, automorphism groups of right-angled Artin groups, of
  finitely generated linear groups, of polycyclic groups, and of every other
  finitely generated residually finite group, together with all their subgroups;
- a finitely generated group of polynomial automorphisms of `A^k_K` (tame or not),
  or of automorphisms of any affine, quasi-projective or projective variety, over
  any field `K`.

The same applies to the root `gl-n-q-embeds-in-fp-simple-group`: an automorphism
group of this kind can contain no intermediate overgroup of `GL_n(Q)`.

## What this leaves open in the automorphism family

- `Aut(Γ)` for finitely generated `Γ` that is **not** residually finite. The
  natural cases are the Thompson-type groups. Brin's `A <= Aut(F)` is excluded for
  `Aff(Q)` by Attempt 1 of `gl-n-q-explicit-natural-fp-overgroup`. `Aut(V)`,
  `Aut(nV)` and `Aut(SV_G)` are, by Rubin's theorem, the normalizers of these
  simple groups in the homeomorphism groups of their Cantor spaces. Whether one of
  them, or a finitely presented subgroup, contains `GL_n(Q)` is not settled here.
- Birational maps: see `fg-cremona-subgroups-have-arithmetic-linear-part`.
- Abstract commensurators: see `comm-of-z-n-times-torsion-group-splits` and the
  artifact.
