---
rg: 2
id: finite-commutator-wachter-weiss-groups-are-not-fp
kind: claim
title: The Wächter–Weiß PSPACE-complete automaton groups built with a finite commutator group are locally-finite-by-Z and hence not finitely presented
distinct_from:
  automaton-tail-full-groups-have-conp-relative-word-problem: that bounds hosts over automaton groups by coNP relative to the coefficient groups and names a finitely presented PSPACE-hard automaton group as the missing input; this shows that the known PSPACE-hard automaton groups, in their finite-commutator form, are not such an input.
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that asks for hard finitely presented self-similar groups in general; this removes one explicit family of candidates.
artifacts:
  - research/artifacts/gq-bh-bh-free-02-wachter-weiss-reading.md
---

**ESTABLISHED** by `finite-commutator-wachter-weiss-groups-are-not-fp-proof`
(lane proof, not independently reviewed). It uses the construction of Wächter--Weiß,
arXiv:1906.03424v3, read from the TeX (`gq/src/ww/pspace.tex`; notes in the
artifact), and the Bieri--Strebel HNN theorem for finitely presented groups mapping
onto `Z`, cited and not read at source here. No priority is claimed.

## Setting

Wächter--Weiß (Theorem `thm:nonuniformPSPACE` and its proof) build, for any
automaton `R` over an alphabet `Σ ⊇ {■0, ■1}` with nontrivial balanced iterated
commutators (their commutator-mode hypothesis, §"The Commutator Mode"), an automaton
group `G_R = G(T_R)` with a PSPACE-complete word problem. The automaton `T_R` has:
- a **TM mode**: the binary encoding `T_2` of the automaton `T'` of their
  Proposition `prop:TMmode`, reading Turing-machine computations over `{■0, ■1}`;
- a **commutator mode**: `R`, together with delayed copies of it, entered after the
  encoded end symbol `$`.

Their Example `ex:commutatorInA5` records that `R = A_5` satisfies the hypothesis, and
their §"Encoding over Two Letters" keeps `Σ` general for this purpose. Their
headline binary group instead uses Aleshin's automaton for `F_3`.

## Statement

Let `R` be a finite group acting on letters of `Σ̃ = Σ \ {■0, ■1}` and fixing `■0`,
`■1`, viewed as an automaton with trivial sections. For example `A_5` on five letters
`e_1, …, e_5`, with `Σ = {■0, ■1, e_1, …, e_5}`, which satisfies Wächter--Weiß's
commutator-mode hypothesis. Then:

1. `G_R` maps onto `Z`, by its action on the invariant subtree `{■0, ■1}^*`, which
   factors through the generalized check-mark adder. The kernel `K` embeds in the
   unrestricted power `R^{{■0,■1}^*}`, so `K` is locally finite, and `G_R` is
   amenable.
2. `K` is infinite, so `G_R` is not virtually cyclic.
3. Hence **`G_R` is not finitely presented**. More generally, a finitely generated
   group with a homomorphism onto `Z` whose kernel is locally finite is finitely
   presented only if it is virtually cyclic.

`G_R` has a PSPACE-complete word problem. Wächter--Weiß state the theorem for a binary alphabet, but their proof is written for general `Σ ⊇ {■0, ■1}` and any `R` meeting the commutator-mode hypothesis (§"Encoding over Two Letters"). Its two directions use nothing else about `R`: the accepting direction needs a letter moved by the commutator, and the rejecting direction uses Fact `fct:malformedWords`. So
this finite-commutator form of the known PSPACE-hard automaton groups cannot feed
Zaremsky's Theorem 1.1 directly.

## What is left

- **`R` moving the encoding letters**, for example `A_5` on five letters including `■0, ■1`, is not covered. Then `W^*` is not invariant.
- **The binary headline group** (`R` = Aleshin's `F_3` on `{■0, ■1}`) is not
  covered. There the `R`-states act on `{■0, ■1}` themselves, so the reduction to
  the check-mark adder in step 1 of the proof does not apply. Whether it is finitely
  presented is open. The paper says nothing about finite
  presentation.
- **Finitely presented self-similar overgroups.** Any finitely presented
  self-similar group containing some `G_R` would have a PSPACE-hard word problem
  automatically. By `fp-self-similar-groups-embed-in-fp-simple-groups` it would give a
  finitely presented simple group beyond Birget's coNP. Whether one exists is exactly
  `decidable-fg-self-similar-groups-embed-in-fp-self-similar` for this input.
- **Design constraint.** A finitely presented PSPACE-hard automaton group cannot have
  the Barrington shape here: a finite conjunction group read off below a
  virtually cyclic "TM-part" group. By item 3, one of the two has to be larger.

DERIVATION
finite-commutator-wachter-weiss-groups-are-not-fp-proof
