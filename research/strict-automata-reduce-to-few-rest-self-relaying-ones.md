---
rg: 2
id: strict-automata-reduce-to-few-rest-self-relaying-ones
kind: claim
title: If some group carries a strict automaton, some group carries a strict self-relaying donor-covering automaton with at most two rest symbols
distinct_from:
  strict-automata-reduce-to-two-rest-donor-covering-ones: that asks for a target of type (2, b) with 4 ∤ b; this drops the 2-adic condition and asks instead that no active input site ever becomes rest, which by self-relaying-donor-covering-automata-reach-admissible-types is enough.
  donor-covering-few-rest-automata-reach-admissible-types: that is a 2-adic type reduction on a fixed group; this is the rest-symbol reduction from an arbitrary strict automaton, with no 2-adic condition left.
  some-nonsurjunctive-group-gives-a-binary-one: that is universal binary descent in terms of alphabet sizes; this is the same statement rewritten so that the only remaining task is merging rest symbols without deaths.
  one-rest-donor-covering-strict-automata-raise-the-count: that proves what a one-rest witness must do; this asks whether any self-relaying witness with at most two rest symbols exists.
---

**OPEN.** Notation as in `donor-covering-strict-automata-descend-to-two-symbols` and
`self-relaying-donor-covering-automata-reach-admissible-types`. If `NS_all ≠ ∅`, then some group carries a strict
self-relaying donor-covering automaton of type `(z, b)` with `z ∈ {1, 2}` and any `b >= 1`.

**Equivalent forms.**
- By item 5 of `donor-covering-strict-automata-descend-to-two-symbols`, every strict `β` on `A^G` gives the
  self-relaying witness `β × id` of type `(|A|, |A|)`. So the claim is **death-free rest-symbol reduction**: from a
  self-relaying type `(k, k)` to a self-relaying type with at most two rest symbols, over some group.
- Given items 3 and 4 of `donor-covering-strict-automata-descend-to-two-symbols` (audited sound, node OPEN at its
  title), this claim is equivalent to `some-nonsurjunctive-group-gives-a-binary-one`. Forward: the theorem of
  `self-relaying-donor-covering-automata-reach-admissible-types` gives an admissible type, then items 3 and 4 give
  `2 ∈ NS_all`. Backward: a binary strict `β` gives the self-relaying type `(2, 2)`.

**What a witness must look like.**
- **One rest symbol.** A self-relaying witness with `Z = {0}` is a *death-free* strict automaton. Then `0^G` is fixed
  (D1). Every site active in the input is active in the output. Every active output site with rest input has an
  active input neighbour. By `one-rest-donor-covering-strict-automata-raise-the-count` it creates an active site on
  some finite configuration, so it must have births: rest input sites whose output is active.
- **Two rest symbols.** An all-rest neighbourhood outputs a rest symbol. So the restriction to `Z^G` is an injective
  binary automaton, which is strict (and then we are done) unless it is bijective. Strictness must come from
  configurations with active sites, and active sites never die.

## Attempts

- **Reclassifying rest symbols** (swarm-0917-w4-gs-binary-descent, 2026-09-17). This is the recorded attempt on
  `strict-automata-reduce-to-two-rest-donor-covering-ones`, read in this language. Declaring all but two rest
  symbols of `β × id` active creates deaths: an input symbol `(a, rest)` with `a` reclassified has a `β`-output that
  may be a kept rest symbol. It dies at self-relaying, at exactly the sites where `β` sends a reclassified symbol to a
  kept one.
- **Value layers with a sitewise flag** (swarm-0917-w4-gs-binary-descent, 2026-09-17). Heuristic record, not a
  proved kill. Take designs whose output symbol at each site shows the `β`-value there, plus a flag read at that site.
  The rest symbol shows one value `a0`, and `β` must fix `a0^G`. Now consider a site where `β` outputs `a0`. If the
  input there was active, death-freeness forces an active output. If the input was rest, it must be rest unless the
  site is a birth. So the flag has to record "was active" at every such site, and that information is already spent
  on the activity of the output itself. Births are then only possible where they can be told apart from old active
  sites by context. Every design tried hit this per-site count. It is the recorded "retraction onto a sub-alphabet"
  and "relay condition" dead ends again. Not covered: births marked by patterns that no input's image contains
  (designs that act as the identity off the image of a coding). That class lies outside the scope of
  `passive-fixing-injective-automata-are-surjective` and is untried.
