---
rg: 2
id: rational-iwahori-group-lies-in-fp-self-similar-group
kind: claim
title: For some prime p the rational Iwahori group Gamma_p lies in a finitely presented self-similar group whose Rover--Nekrashevych group has finite abelianization
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that embeds finitely presented self-similar groups in finitely presented simple groups; this asks for a finitely presented self-similar overgroup of one specific countable, non-finitely-generated self-similar group, with its given action on the p-ary tree.
  pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori: that defines Gamma_p and shows PGL_2(Q) <= V_p(Gamma_p); this asks to replace Gamma_p by a finitely presented self-similar overgroup.
---

**OPEN.** For some prime `p` there is a self-similar group `Λ <= Aut(T_p)` with
the following properties:
- `Γ_p <= Λ` inside `Aut(T_p)`, where `Γ_p` is the rational Iwahori group of
  `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori`, acting on
  `∂T_p = Z_p` by Möbius maps;
- `Λ` is finitely presented;
- the Röver–Nekrashevych group `V_p(Λ)` has finite abelianization.

By `psl2-q-fp-simple-via-rational-iwahori-rn-host`, this implies
`psl2-q-embeds-in-fp-simple-group`.

## Constraints any Λ must meet

- **Not contracting.** `Γ_p` contains an element that is not finite-state (item 4
  of `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori`). So only Scott's
  finite-presentation theorem (FP1), not Nekrashevych's (FP2), can apply.
- **Not a Möbius group.** `Λ ⊄ PGL_2(Q)`. A finitely generated subgroup of
  `PGL_2(Q)` has entries in some `Z[1/N]`, and `Γ_p` does not (item 4).
  - Further, by `piecewise-commutative-linear-hosts-miss-linear-gl-n-q`(a), a
    finitely generated group of homeomorphisms whose pieces all lie in a
    finitely generated subgroup of `PGL_2(Q_p)` cannot contain all of `PGL_2(Q)`
    acting by Möbius maps.
  - So `Λ` must contain tree automorphisms of `T_p` that are not Möbius maps.
- **Not residually-finite-blocked.** `Γ_p` is residually finite, since it lies in
  `Aut(T_p)`. It contains `Z_(p)` but no nontrivial divisible subgroup, so
  obstruction O1 of the root says nothing about `Λ`. The `p`-divisibility of
  `(Q,+) <= PGL_2(Q)` comes from the level shifts of `V_p`, not from `Λ`.

## Attempts

None recorded beyond the constraints above (2026-09-17, lane gq-rn-varying-degree).
