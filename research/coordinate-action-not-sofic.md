---
rg: 2
id: coordinate-action-not-sofic
kind: claim
title: The coordinate action G ↷ G/Γ is not a sofic action
invalidates: [sofic-action-permanence]
distinct_from:
  wreath-not-sofic: that is nonsoficity of the group W; this is nonsoficity of the coset ACTION on the index set, which is what every permanence theorem takes as its hypothesis
  sofic-radical-linear-action-criterion: that is a general displacement-inequality criterion for sofic-radical membership in a finitely presented group; this is a specific negative fact about one coset action of one group
  finite-quotient-blindness: that says finite quotients normalize Γ's image; this says no finite permutation approximation of the coset action exists at all, sofic or otherwise
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

The coordinate action `α : G ↷ G/Γ` of the wreath candidate is **not a sofic
action**, in the finitary sense of Gao–Kunnawalkam Elayavalli–Patchell
Definition 2.1(5) (a unital, `(F,ε)`-multiplicative `φ : G → Sym(A)` that is an
`(F,E,ε)`-orbit approximation). Relatedly, and independently (the two
statements concern different objects -- the `G`-set `G/Γ` and the p.m.p.
action on `(K,κ)^{G/Γ}` -- and no equivalence between them is proved
here), the generalized Bernoulli action `G ↷ (K,κ)^{G/Γ}` is not sofic in Păunescu's
sense (Kun–Thom Corollary D).

This is the hypothesis that *every* known permanence theorem for generalized
wreath products takes as input, so it closes that whole toolkit at once
(`sofic-action-permanence`). It is a strictly sharper statement than
`wreath-not-sofic`: nonsoficity of the group `W` is about approximating `W`,
whereas this is about approximating the `G`-set `G/Γ`, and it is the latter
that the permanence machinery consumes.

## Consequence for the flexible side

The two theorems that would otherwise deliver hyperlinearity of `W` outright —
GKP Theorem 3.8 (`M` Connes-embeddable, `H` hyperlinear, `α` sofic ⟹ `M ≀_α H`
Connes-embeddable) and Alekseev–Bradford Corollary 5.2/5.5 — are exactly the
theorems whose hypothesis this refutes. Both have the shape
"*the coordinate action is sofic ⟹ the tracial model exists*", and both are
therefore unavailable for `W`, permanently and not for want of effort.

What survives is precise: any hyperlinear model of `W` must embed the Bernoulli
lamp algebra **non-Cartanly**. It cannot come from orbit charts, from finite
quotient coordinates, or from any automorphic chart system, because all of
those produce permutation normalizers and Corollary D forbids those. That is
the exact content of the open quadrant in `hyperlinear-wreath-model`, and it is
now a derived boundary rather than an impression.

## A published question this closes

This node is not only an internal obstruction. Fed through the diagonal-coset
construction (`nonsofic-orbit-forces-commuting-counterexample`, instantiated
by `commuting-counterexample-from-kun-thom-pair`), it answers **Question 4.2**
of Gao–Kunnawalkam Elayavalli–Patchell in the negative:
`commuting-sofic-actions-need-not-combine` — two commuting free sofic actions
of the sofic group `G` on `(G × G)/ΔΓ` whose combined `G × G`-action is not
sofic. That is the first published consequence of this fact outside the
wreath-product program it was built for.

## Note on the escape hatch that does not exist

The one known sufficient condition for an action to be sofic is amenable point
stabilizers (Alekseev–Bradford Theorem 4.18, attributed by them to the
companion GKP graph paper: *"any action of a sofic group on a set, with all
point-stabilisers being amenable subgroups, is a sofic action"*). The point
stabilizers of `G ↷ G/Γ` are the conjugates of `Γ`, which is infinite and has
property (T), hence is not amenable — an amenable discrete group with (T) is
finite. So the candidate sits on the far side of the only known sufficient
condition, and the failure is caused by the same property (T) that drives the
nonsoficity. The two sides of the problem meet at the stabilizer.
