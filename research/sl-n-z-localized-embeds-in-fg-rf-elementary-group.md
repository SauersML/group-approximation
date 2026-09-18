---
rg: 2
id: sl-n-z-localized-embeds-in-fg-rf-elementary-group
kind: claim
title: SL_n(Z_(l)) and GL_n(Z_(l)) — hence Z_(l) and every GL_n(Z[1/P]) with l not in P — embed in the finitely generated residually finite groups E_N(R̄_l)
distinct_from:
  aff-n-over-z-localized-at-ell-is-rf-and-self-similar: that shows GL_n(Z_(l)) is itself residually finite and self-similar but not finitely generated; this puts it in an explicit finitely generated residually finite group, necessarily non-linear.
  z-localized-embeds-in-fp-rf-group: that asks for a finitely presented residually finite overgroup of Z_(l); this is the finitely generated level, which it establishes explicitly.
  leavitt-pairs-embed-sl-n-q-in-steinberg-groups: that embeds SL_n(Q) in Steinberg groups over rings with a Leavitt pair, which are never residually finite; this embeds SL_n(Z_(l)) in elementary groups over a residually finite ring.
---

**ESTABLISHED** through `sl-n-z-localized-embeds-in-fg-rf-elementary-group-proof`.
Lane proof, not independently reviewed. No priority is claimed: that countable
residually finite groups embed in finitely generated residually finite groups is
expected from general embedding theorems (not re-read here). The point here is an
explicit, algebraic host.

**Statement.** Let `l` be a prime and `R̄_l` the five-generated residually finite ring
of `rf-resolvent-ring-has-z-localized-corner`, with idempotent `e` and injective
unital `θ : Z_(l) -> e R̄_l e`. For `A in M_n(Z_(l))` put
`Θ(A) = θ(A) + (1 - e) I_n in M_n(R̄_l)`.
1. `Θ` restricts to injective homomorphisms `SL_n(Z_(l)) -> E_n(R̄_l)` for `n >= 2`,
   and `GL_n(Z_(l)) -> GL_n(R̄_l)`.
2. `g -> diag(Θ(g), Θ(g)^(-1))` embeds `GL_n(Z_(l))` in `E_(2n)(R̄_l)`.
3. For `N >= 3`, `E_N(R̄_l)` is finitely generated, by the elementary matrices whose
   entry is `1` or one of the five generators.
4. `GL_N(R̄_l)`, hence `E_N(R̄_l)`, is residually finite.

So Z_(l) (as `e_12(θ(Z_(l)))`), `SL_2(Z_(l))` (inside `E_3(R̄_l)`) and `GL_n(Z_(l))`
(inside `E_(2n)(R̄_l)`) lie in explicit finitely generated residually finite groups.
So does every `GL_n(Z[1/P])` with `l ∉ P`.

**Consistency with the obstructions.** These hosts are necessarily
- not linear over any field (`infinite-prime-localizations-embed-in-no-fg-linear-group`,
  `fg-linear-groups-have-roots-at-finitely-many-primes`);
- not metabelian (`fg-metabelian-groups-have-roots-at-finitely-many-primes`).
None of them contains `(Q,+)`, since they are residually finite (O1 of
`gl-n-q-embeds-in-fp-simple-group`).

**What is still missing for the Hecke route.**
`sl-2-z-localized-has-fp-hecke-overgroup` asks for more:
- *finite presentation:* it would follow from `rf-resolvent-elementary-group-is-fp`;
- *the Hecke extension:* an isomorphism between finite-index subgroups extending
  conjugation by `diag(1,l)`. The naive congruence version fails here:
  `R̄_l / l R̄_l` is infinite, so the Iwahori-type subgroup of `E_2(R̄_l)`, with
  `(1,2)`-entry in `l R̄_l`, has infinite index.
