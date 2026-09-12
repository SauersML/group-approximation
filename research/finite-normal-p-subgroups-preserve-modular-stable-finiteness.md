---
rg: 2
id: finite-normal-p-subgroups-preserve-modular-stable-finiteness
kind: claim
title: A finite normal p-subgroup does not affect stable finiteness of group algebras in characteristic p
distinct_from:
  separated-finite-normal-subgroups-preserve-surjunctivity: that transfers surjunctivity across a finite normal subgroup which some finite-index subgroup avoids; this transfers stable finiteness of characteristic-p group algebras across any finite normal p-subgroup, including one inside the finite residual.
artifacts:
  - research/artifacts/deligne-triple-cover-surjunctivity-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Section 1; independent verification requested from
`w3-vf-positive`). Let `N` be a finite normal `p`-subgroup of a group `E`, and `k` a field of
characteristic `p`. Then `k[E]` is stably finite iff `k[E/N]` is stably finite.

**Why.** The kernel of `k[E] -> k[E/N]` is `omega k[E] = k[E] omega`, where `omega` is the augmentation
ideal of `k[N]`. For a `p`-group in characteristic `p`, `omega^|N| = 0`. Direct finiteness passes in both
directions across a nilpotent two-sided ideal, at every matrix size.

**Consequences.**
- **Linear automata.** If `k` is finite and `k[E/N]` is stably finite, `E` carries no strict `k`-linear
  automaton on any `(k^n)^E`. A strict one would have a linear left inverse
  (`certificate-linear-automata-have-local-linear-decoders`) and so a one-sided inverse pair in
  `M_n(k[E])`.
- **Inside the finite residual.** No finite quotient of `E` is used, so this covers finite normal
  `p`-subgroups contained in `Res_fin(E)`. That is the open residue of
  `finite-normal-subgroups-do-not-affect-surjunctivity`, at the linear level and in characteristic `p`.
- **Deligne's triple cover** at `p = 3`: `deligne-triple-cover-ternary-group-algebras-are-stably-finite`
  (artifact Section 2).

**Scope.** For `p` not dividing `|N|` the kernel is not nilpotent. The group algebra then splits over the
characters of `N` when `N` is central, and the nontrivial-character factors are twisted group algebras of
`E/N` that this claim says nothing about.
