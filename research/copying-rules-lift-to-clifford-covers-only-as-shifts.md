---
rg: 2
id: copying-rules-lift-to-clifford-covers-only-as-shifts
kind: claim
title: The Kun--Thom copying rule lifts to groups only as a bijective shift, and every site-level lift lands where injective automata on a Clifford cover are bijective
distinct_from:
  end-fixing-tree-symmetries-carry-strict-automata: that exhibits the copying rule as a strict automaton on a non-unimodular tree; this shows that over any group mapping onto the Kun--Thom base the same rule lifts only as a bijective right shift, and that copy automata over groups are shifts.
  clifford-cover-cofinite-lamp-subgroups-contain-the-center: that shows cofinite-lamp subgroups contain eps, so peeling transplants see only eps-invariant configurations; this uses it to show every equivariant lift of site data, the copying rule included, lands in configurations where an injective automaton is bijective.
  injective-automata-restrict-to-schreier-graph-automata: that is the restriction theorem for configurations fixed by a subgroup; this applies it with W surjunctive to every subgroup containing eps, and adds the lift and the copy-automaton rigidity.
artifacts:
  - research/artifacts/clifford-copying-rule-lift-2026-09-12.md
---

**ESTABLISHED** by `copying-rules-lift-only-as-shifts-proof` (artifact Section 1; verification requested from
`w3-vf-nonlinear`).

**Setting.** `t Gamma t^(-1) <= Gamma < G`, `X = G/Gamma`, `p(g Gamma) = g t^(-1) Gamma`, and the copying rule
`rho(x) = x o p` on `A^X`, injective and not surjective when `[Gamma : t Gamma t^(-1)] >= 2`.

**Theorem.** Let `pi : E -> G` be an epimorphism.
1. `iota(x)(e) = x(pi(e) Gamma)` is an equivariant continuous injection `A^X -> A^E`, and the right shift by any
   `s` with `pi(s) = t^(-1)` is a bijective automaton `R` with `R o iota = iota o rho`.
2. Every `E`-equivariant map `A^X -> A'^E` has image in `Fix_(ker pi)`.
3. An automaton over a group that copies one cell, `tau(x)(e) = x(P(e))`, has `P(e) = e m` for a fixed memory
   element `m`, so it is a bijective shift.
4. For `E = E_S` with `W = E_S/<eps>` surjunctive, every injective automaton maps `Fix_H` onto `Fix_H` for each
   subgroup `H` containing `eps`. That includes `Fix_(Vtilde_S)`, and on the complete graph over an infinite set every
   `H` with cofinite lamp part.

**Payoff.** The question "does the Clifford twist let the copying rule lift to a strict automaton" has a negative
answer in every site-level sense, and the relation responsible is independent of the twist: right cancellation in the
group, `eps in ker pi`, and surjunctivity of `W`. The tree Garden of Eden (siblings disagreeing while reading one parent
cell) is not an automaton over any group. A strict automaton on `E_S` must show its non-surjectivity off every
configuration fixed by a subgroup containing `eps`; for self-dual rules that sector is the frustrated flux shift of
`clifford-cover-self-dual-sectors-are-frustrated-flux-shifts`.
