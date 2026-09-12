---
rg: 2
id: bernoulli-rokhlin-entropy-maximal-for-every-group
kind: claim
title: Every uniform Bernoulli shift over every countable group has Rokhlin entropy equal to its base entropy
distinct_from:
  gottschalk-surjunctivity-conjecture: that is surjunctivity of every group; this is a measurable entropy statement that implies it through strict-automaton-lowers-bernoulli-rokhlin-entropy, and no converse is known.
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

**OPEN.** For every countably infinite group `G` and every finite alphabet `A`
with `|A| >= 2`,

    h^Rok_G(A^G, uniform product measure) = log |A|.

By `bernoulli-rokhlin-deficit-has-a-finitary-witness`, this is the finite
information inequality

    H(psi(x|_E)) + H( x(1) | (psi((x(fe))_e))_(f in F) ) >= log |A|

over all finite sets `E, F` in all groups and all functions `psi`, with `x` iid
uniform. Every alphabet `A^k` is again an alphabet, so amplified bases are
included. The claim implies Gottschalk's conjecture
(`gottschalk-via-maximal-bernoulli-rokhlin-entropy`) and Kaplansky's direct
finiteness conjecture over finite fields.

## Attempts

* **Sofic groups.** Sofic entropy of a Bernoulli shift equals its base entropy and
  bounds from below the Shannon entropy of every generating partition. This is
  recorded as context only. It uses the finite models of Gromov--Weiss and says
  nothing about nonsofic groups.
* **Model-free lower bounds.** Every lower bound for Bernoulli Rokhlin entropy known
  to this lane uses finite models or Folner sets. The per-site window entropy that
  works over amenable groups is not an invariant over nonamenable ones
  (`window-entropy-deficits-are-not-isomorphism-invariant`).
* **Restriction to an amenable subgroup.** For infinite amenable `Lambda <= G`,
  `bernoulli-rokhlin-maximality-passes-to-subgroups` gives only
  `h^Rok_G(L^G) <= h^Rok_Lambda(L^Lambda)`. The reverse inequality would settle
  every group containing an element of infinite order. Information about the
  coordinates of one coset can spread over the other cosets, and no density along
  `G/Lambda` is available. Dead as stated.
* **Linear witnesses.** For `k = 1` and prime `q`, a nonzero linear `psi` is
  uniform, so any deficit witness is nonlinear. This narrows the search and proves
  nothing.
* **Earlier record.** A 2026-09-07 repository audit records Seward,
  arXiv:1501.03367, Corollaries 4.1 and 7.8: positivity of Bernoulli Rokhlin entropy
  over all countably infinite groups implies these equalities. Not re-read, and no
  proof of positivity is known here.
* **One group suffices.** `rokhlin-maximality-on-tester-covers-every-group` shows
  that the fixed tester host decides this claim.
