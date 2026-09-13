---
rg: 2
id: labbe-substitution-is-primitive-and-recognizable
kind: claim
title: Labbé's 19-tile Wang shift is the substitutive shift of an expansive, primitive, recognizable 2-dimensional morphism ω = αβγ whose letter images have shape at most (2,2)
distinct_from:
  minimal-aperiodic-wang-shift-exists: that imports only Theorem 1 (self-similar, aperiodic, minimal); this imports the substitution structure behind it, with primitivity, recognizability, image shapes and the (2,2)-cover step.
  labbe-shift-is-a-toral-rotation-coding: that imports the 2019 Markov partition and rotation coding; this imports the 2018 substitution ω from the original paper.
artifacts:
  - research/artifacts/un-labbe-ring-substitution-complexity-2026-09-13.md
---

**ESTABLISHED (import).** Source: S. Labbé, arXiv:1802.03265. The TeX source was read on MSI; quotes and line
numbers are in the artifact, §1.

For Labbé's tile set `U` (19 tiles) and Wang shift `Ω_U`, the morphism `ω = α∘β∘γ : Ω_U -> Ω_U` has these
properties:
1. **Expansive, recognizable, onto up to a shift** (`prop:pre-main`): "expansive, recognizable in $\Omega_\U$ and
   satisfies $\Omega_\U = \omega(\Omega_\U) \cup\sigma^{\be_1}\omega(\Omega_\U) \cup\sigma^{\be_2}\omega(\Omega_\U)
   \cup\sigma^{\be_1+\be_2}\omega(\Omega_\U)$." Its proof says "sends at least one letter to a $2$-dimensional word
   of shape $(2,2)$".
2. **Primitive** (`lem:omega-is-primitive`): "The morphism $\omega$ is primitive", with "$M^7$ is positive".
3. **Image shapes.**
   - `α` is given by Theorem `thm:exist-homeo` with markers in direction `e_2`, so letters go to letters or dominoes
     in direction `e_2`.
   - `β` is given by the same theorem in direction `e_1`, so letters go to letters or dominoes in direction `e_1`.
   - `γ` is a letter bijection (`lem:homeoUtoW`).
4. **Substitutive** (`prop:OmegaU-is-self-similar`): "$\Omega_\U$ is minimal. More precisely, $\Omega_\U=\X_\omega$".
   Also `\overline{ω(Ω_U)}^σ = Ω_U` (`cor:OmegaU-is-aperiodic`).
5. **Legal 2×2 words** (`lem:50tiles-2x2-in-OmegaU`): `L(Ω_U) ∩ U^((2,2)) = S`, a displayed set of 50 words.
6. **Cover step** (proof of `lem:substitutive-equivalent-conditions`): if `L = \overline{ω(L)}^{Fact}` and
   `shape(ω^m(a)) >= shape(z)` for all letters, then "there exists a word $u\in L$ of shape $(2,\dots,2)$ such that
   $z$ is a subword of $\omega^m(u)$."

Route: `labbe-substitution-is-primitive-and-recognizable-citation`.
