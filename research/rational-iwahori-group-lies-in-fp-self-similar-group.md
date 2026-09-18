---
rg: 2
id: rational-iwahori-group-lies-in-fp-self-similar-group
kind: claim
title: For some prime p the rational Iwahori group Gamma_p lies in a finitely presented self-similar group whose Rover--Nekrashevych group has finite abelianization
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that embeds finitely presented self-similar groups in finitely presented simple groups; this asks for a finitely presented self-similar overgroup of one specific countable, non-finitely-generated self-similar group, with its given action on the p-ary tree.
  pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori: that defines Gamma_p and shows PGL_2(Q) <= V_p(Gamma_p); this asks to replace Gamma_p by a finitely presented self-similar overgroup.
  aff-n-z-localized-lies-in-fp-self-similar-group: that asks, for some prime l and every n, for a finitely presented self-similar overgroup of Aff_n(Z_(l)) on any regular tree; this needs, for one p, an overgroup of Gamma_p, which contains Aff_1(Z_(p)), on the p-ary tree with the given action. It implies the n = 1, l = p case of that claim.
  decidable-fg-self-similar-groups-embed-in-fp-self-similar: that is a Higman-type embedding of finitely generated decidable self-similar groups into finitely presented self-similar ones, with no control of the tree action; this needs the embedding to preserve the action of Gamma_p on T_p.
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

## Equivalent generator form

By `rational-iwahori-group-is-union-of-fp-self-similar-groups`, item 5,
`Γ_p = ⟨Γ_p(1), d_q : q prime ≠ p⟩`, with `d_q(z) = qz`. So the first clause
says: `Λ` contains
- the virtually free, finitely presented, self-similar group `Γ_p(1)`, the
  Iwahori image in `PGL_2(Z)`, and
- the dilations `d_q` for all primes `q ≠ p`.

Equivalently, `Λ ⊇ Γ_p(1) ∪ Aff_1(Z_(p))`. Each finite stage
`Γ_p(m) = ⟨Γ_p(1), d_q : q | m⟩` is already finitely presented and self-similar.
The whole difficulty is absorbing infinitely many primes.

## Constraints any Λ must meet

The first two constraints are from
`iwahori-overgroups-not-automaton-linear-or-metabelian`.
- **Not an automaton group.** `Λ` has a generator that is not finite-state,
  since `Γ_p` contains a non-finite-state element.
- **Not linear, not metabelian.** `Λ` is not linear over any field and not
  metabelian. In particular it is not an affine or Möbius group over any ring,
  commutative or not, whose adic tree is `T_p`, and not a group of continuous
  affine maps of `Z_p`.
- **Not contracting.** Only Scott's finite-presentation theorem (FP1), not
  Nekrashevych's (FP2), can apply.
- **Not a Möbius group.** A finitely generated subgroup of `PGL_2(Q)` has
  entries in some `Z[1/N]`, and `Γ_p` does not. More generally, by
  `piecewise-commutative-linear-hosts-miss-linear-gl-n-q`(a), a finitely
  generated group of homeomorphisms whose pieces all lie in a finitely generated
  subgroup of `PGL_2(Q_p)` cannot contain `PGL_2(Q)` acting by Möbius maps.
- **Not blocked by residual finiteness.** `Γ_p` is residually finite, since it
  lies in `Aut(T_p)`. It contains `Z_(p)` but no nontrivial divisible subgroup,
  so obstruction O1 of the root says nothing about `Λ`. The `p`-divisibility of
  `(Q,+) <= PGL_2(Q)` comes from the level shifts of `V_p`, not from `Λ`.

## Attempts

1. **Natural candidates (2026-09-17, lane gq-rn-varying-degree): all dead.**
   These are:
   - automaton groups;
   - affine or Möbius groups over finitely generated rings, commutative or not,
     acting on a `p`-ary adic tree;
   - Zaremsky's affine hosts in rank one;
   - the `S`-arithmetic Iwahori groups `Γ_p(m)` themselves, which cover only
     finitely many primes.

   See `iwahori-overgroups-not-automaton-linear-or-metabelian` and
   `rational-iwahori-group-is-union-of-fp-self-similar-groups`.
2. **The Higman-type claims do not apply directly.**
   `decidable-fg-self-similar-groups-embed-in-fp-self-similar` and
   `computable-tree-groups-embed-in-fp-self-similar-groups` (both OPEN) produce
   abstract embeddings. The route here needs `Γ_p` inside `Λ` with the Möbius
   action on `T_p` unchanged, because the level shifts of `V_p` must match the
   `p`-adic cones.

   A usable form would be *tree-compatible*: every finitely generated
   self-similar `S <= Aut(T_p)` with solvable word problem lies in a finitely
   presented self-similar `Λ <= Aut(T_p)` whose action restricts to that of `S`.
   Even that needs a finitely generated self-similar overgroup of `Γ_p` first.
   None is known; the non-finite-state element rules out taking the
   self-similar closure of finitely many finite-state maps.
3. **The resolvent ring gives no tree-compatible host (2026-09-17, lane
   gq-rn-varying-degree).** `rf-resolvent-ring-has-z-localized-corner` gives
   finitely generated residually finite groups, such as `E_N(R̄_p)`, that
   contain `Z_(p)` and `SL_n(Z_(p))` as abstract subgroups.
   - The corner `eR̄_pe` acts on the line `Z/p^r f_0` of each `M_r`. Through
     this action, matrix groups over the corner act on `Z_p` by Möbius maps with
     coefficients in `Z_p`, so the acting group lies in `PGL_2(Q_p)`.
   - The image of a finitely generated group in `PGL_2(Q_p)` is a finitely
     generated linear group. It cannot contain the translations by `Z_(p)`
     (`fg-linear-groups-have-roots-at-finitely-many-primes`).
   - So this action cannot supply `Λ`; this is items (c) and (d) of
     `iwahori-overgroups-not-automaton-linear-or-metabelian`. A usable
     action of such a group on `T_p` would have to be non-linear.
4. **Prime-shift spinal extensions of `Γ_p(1)`: dead when Möbius on shells
   (2026-09-18, lane gq-rn-varying-degree).** Take `Λ = ⟨Γ_p(1), g_1, ..., g_r⟩`,
   where each `g_i`:
   - fixes 0;
   - is locally in `PGL_2(Q)` off 0;
   - acts on every small shell `S_j` by some `M^{(i)}_j ∈ PGL_2(Q)`. The
     prime-shift element `z ↦ u_{v(z)} z` is the model case.

   By `shell-mobius-extensions-see-finitely-many-primes`, if the sections at
   vertex 0 lie in `Λ`, then `Λ ∩ PGL_2(Q) <= PGL_2(Z[1/N])` for some `N`. The
   reason is that the section condition becomes a recursion
   `M_{j+1} = ρ F(M_j) ρ^{-1}` inside one finitely generated subgroup of
   `PGL_2(Q)`. So the spine must be non-Möbius on infinitely many shells, or
   the singular sets must be infinite.
