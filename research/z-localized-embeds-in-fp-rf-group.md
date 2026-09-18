---
rg: 2
id: z-localized-embeds-in-fp-rf-group
kind: claim
title: For some prime l, the additive group Z_(l) embeds in a finitely presented residually finite group
distinct_from:
  rf-higman-embedding-for-decidable-groups: that refuted statement asks for finitely presented residually finite overgroups of all finitely generated residually finite groups with solvable word problem; this asks for one specific countable, not finitely generated, residually finite abelian group.
  every-fp-rf-group-embeds-in-fp-self-similar-group: that asks for self-similar overgroups of finitely presented residually finite groups; this asks whether a finitely presented residually finite group can contain Z_(l) at all.
  sl-n-z-localized-embeds-in-fg-rf-elementary-group: that establishes the finitely generated level, with the explicit hosts E_N(R̄_l); this is the finitely presented level.
---

**OPEN.** There are a prime `l`, a finitely presented residually finite group `Λ` and
an injective homomorphism `(Z_(l), +) -> Λ`. Here `Z_(l)` is the ring of rationals
with denominators prime to `l`.

**Why it matters: a common bottleneck.** Three open host hypotheses of the gq program
each imply this claim, so each is at least as hard:
- `sl-2-z-localized-has-fp-hecke-overgroup` (for `SL_2(Q)` via Ihara and Bux--Llosa
  Isenrich--Wu), by `z-localized-fp-rf-from-hecke-overgroup`;
- `aff-n-z-localized-lies-in-fp-self-similar-group` (for `GL_n(Z_(l))` via Zaremsky),
  by `z-localized-fp-rf-from-affine-self-similar-host`;
- `rational-iwahori-group-lies-in-fp-self-similar-group` (for `PSL_2(Q)` via
  Röver--Nekrashevych groups), by `z-localized-fp-rf-from-rational-iwahori-host`.

A counterexample, meaning a proof that no finitely presented residually finite group
contains `Z_(l)` for any `l`, would kill all three routes at once.

**Constraints on a witness Λ.**
- *Not linear, not metabelian.* `Λ` is not linear over any field
  (`fg-linear-groups-have-roots-at-finitely-many-primes`), and not metabelian
  (`fg-metabelian-groups-have-roots-at-finitely-many-primes`).
- *Finite quotients.* Every finite quotient of `Z_(l)` is a cyclic `l`-group, since
  a finite-index subgroup contains some `m Z_(l) = l^(v_l(m)) Z_(l)`. So in every
  finite quotient of `Λ` the image of `1 in Z_(l)` has `l`-power order, and its
  closure in the profinite completion of `Λ` is a quotient of `Z_l`.
- *Word problem.* Every finitely generated subgroup of `Λ` has solvable word problem
  (`fp-residually-finite-groups-have-solvable-word-problem`) and is effectively
  residually finite.
- *No divisibility.* `Λ` contains no `(Q,+)` (O1), so the `l`-divisibility that the
  gq routes need must come from outside `Λ`: from a tree, an HNN letter or the level
  shifts of a Röver--Nekrashevych group.

**The finitely generated level is solved.** `Z_(l) <= E_3(R̄_l)`, a finitely generated
residually finite group (`sl-n-z-localized-embeds-in-fg-rf-elementary-group`). So the
open part is finite presentation. One concrete route is
`z-localized-fp-rf-via-fp-resolvent-elementary-group`.

## Attempts

1. **Verdict, second pass (2026-09-17, lane gq-infinite-primes): still OPEN, reduced to residual finiteness of
   one explicit finitely presented group.**
   - *The finitely presented half is done.* `Z_(l)` embeds in the finitely presented Kazhdan group
     `St_N(R_l)`, `N >= 4` (`z-localized-embeds-in-fp-kazhdan-steinberg-group`, via Krstić--McCool). The claim now
     follows from `resolvent-steinberg-group-is-residually-finite` (route
     `z-localized-fp-rf-via-rf-resolvent-steinberg-group`).
   - *A necessary condition.* That needs `R_l` to be residually finite (`steinberg-rf-forces-ring-rf`,
     `resolvent-presentation-ring-is-residually-finite`), and then the kernel of `St_N(R_l) -> E_N(R_l)` to be
     detected in finite `St_N(F)`.
   - *Sub-question 1 of `rf-resolvent-elementary-group-is-fp` fails.* `R_l` does not present `R̄_l`
     (`resolvent-ring-presentation-is-not-faithful-on-r-bar`).
   - *No known obstruction applies.* Rauzy (arXiv:2002.02540v2) and Kharlampovich--Myasnikov--Sapir
     (arXiv:1204.6506) state nothing about divisible or infinitely generated abelian subgroups. The obstructions
     found for finitely generated subgroups are solvable word problem and effective residual finiteness,
     and the explicit host `G_l` of `z-localized-embeds-in-fg-rf-soluble-group` satisfies both. So an affirmative
     answer to the Kharlampovich--Myasnikov--Sapir question for effectively residually finite groups would give
     this claim. The Kharlampovich--Myasnikov--Sapir groups themselves are soluble of class 3, as is `G_l`.
