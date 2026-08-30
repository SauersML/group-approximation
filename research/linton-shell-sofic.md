---
rg: 2
id: linton-shell-sofic
kind: claim
title: The finite rational-derived shell of a one-relator group is sofic
distinct_from:
  one-relator-groups-sofic: that is Pestov's Question 4.10 as stated, over all one-relator groups; this is the single object that question reduces to, and establishing it establishes the question but not conversely in any usable way — the reduction runs one direction as a proof obligation.
  linton-radical-sofic: that asks for soficity of the radical `R` alone; this asks for soficity of `R ⋊ F₀`, which does not follow from it, because semidirect closure fails in general.
  one-relator-soficity-localizes-at-rational-derived-stage: that is the established reduction producing this shell and is closed; this is the open statement about the shell it produces.
  residually-rationally-solvable-one-relator-sofic: that closes the case `R = 1`, where the shell is free and soficity is immediate; this is the statement in the remaining case, where the shell is a genuine semidirect product and nothing is immediate.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that proves the quotient shell `E/R'` residually finite and embeds `G/R'` in a finite-lamp wreath product; this asks for the full shell, including the nonabelian derived core.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

OPEN.  Let `G = F/<<w>>` be a one-relator group, `R = G_Q^(ω)` its Linton
radical, and `E = G_Q^(n)` the finite rational-derived shell of
[[one-relator-soficity-localizes-at-rational-derived-stage]], so `n <= |w|` and

    E ≅ R ⋊_α F₀ ,   F₀ free .

Claim: `E` is sofic, for every one-relator `G`.

By the reduction this is **equivalent** to [[one-relator-groups-sofic]] — the
quotient `G/E` is solvable, so nothing is lost or gained in either direction.
The point of stating it separately is that it names the object rather than the
class: the target is one very particular semidirect product, free acting on
normally-one-generated rationally perfect, and not "an arbitrary one-relator
group".

## What makes the shell special, and therefore attackable

- `F₀` is **free**, so the acting side is as far from the Kazhdan groups that
  drive every known nonsoficity as it is possible to be.
- `R` is normally generated in `G` by a single element `r` with `|r| <= |w|`,
  and its abelianization is known exactly:
  [[linton-radical-abelianization-is-truncated-group-ring]] gives
  `R_ab ≅ (Z/kZ)[G/R]`, splitting the problem into a perfect regime (`k = 1`)
  and a bounded-exponent regime (`k > 1`).
- The entire first-order quotient is now controlled:
  [[one-relator-fox-magnus-descent-to-derived-linton-radical]] proves
  `E/R'` residually finite and embeds `G/R'` in
  `((Z/kZ)^d) wr (G/R)`.  Thus the open shell problem begins exactly at the
  derived core `R'`.
- The splitting `α` comes from the rational derived series, not from an
  arbitrary choice, so it carries whatever coherence the one-relator origin
  imposes on the conjugates of `r`.

## Attempts

1. **Alekseev--Bradford sofic actions.**  *Live*, recorded as
   `linton-shell-sofic-via-sofic-action`: if `R` is sofic
   ([[linton-radical-sofic]]) and `α` is a sofic action by automorphisms
   ([[linton-radical-free-action-sofic]]), their semidirect-product theorem
   gives `E` sofic.  Both hypotheses are open, and their automatic criterion is
   unavailable here — it wants a **finitely generated residually finite**
   normal group, and a nontrivial Linton radical in the torsion-free case is
   infinitely generated, which is precisely the unresolved regime.
2. **Assume semidirect closure.**  *Dead*, recorded as
   `linton-shell-sofic-via-generic-semidirect-closure` and killed by
   [[sofic-semidirect-product-closure-fails]].  Kun--Thom's counterexamples have
   an amenable normal factor and a residually finite acting factor, so no
   strengthening of the hypotheses on the *factors* rescues the shortcut; only a
   hypothesis on the **action** can.
3. **Free-group actions on graphs are sofic.**  *Dies on a notion mismatch.*
   The recent results in that family (Gao--Kunnawalkam Elayavalli--Patchell and
   relatives) make free-group actions on sets/graphs sofic, but soficity of an
   action on a *set* is not soficity of an action by *automorphisms of a group*
   in the sense a semidirect-product theorem consumes.  No bridge between the
   two notions was found for Linton radicals, and inventing one is a research
   problem rather than a translation.
4. **Realize `R` as a lamp group and use halo permanence.**  *Closed modulo
   `R'`, and blocked beyond it.*  `R = <<r>>_G` invites reading it as a
   restricted direct sum of
   conjugate copies indexed by `H = G/R`, with `H` permuting coordinates — the
   exact shape halo-product theorems want.  But the relator orbit couples the
   coordinates nonabelianly.  Modulo `R'`, purity of the Magnus relation module
   removes that coupling and gives the explicit finite-lamp embedding above.
   No analogous second-order decomposition of `R'` is known, so applying the
   lamp analogy to the whole radical still repackages
   [[magnus-staggered-chain-sofic]] rather than avoiding it.
5. **A local structure theorem on `R`.**  *Deferred.*  It would suffice that
   every finitely generated subgroup of `R` lie in a sofic subgroup drawn from a
   class closed under directed unions.  No such theorem is known, and the
   obvious candidate classes (free, residually finite) are not obviously
   available for a rationally perfect infinitely generated radical.

The new quotient does not license an extension shortcut.  Even if `R'` were
shown sofic abstractly, `E/R'` is residually finite rather than amenable, and
sofic-by-sofic extension closure is false.  A completion must preserve the
`F0`-action while approximating the nonabelian core.
