---
rg: 2
id: thompson-v-not-sofic
kind: claim
title: Thompson's group V is not sofic
distinct_from:
  thompson-v-not-hyperlinear: that is the stronger normalized-HS statement, which implies this one; this is the Hamming statement, which a hyperlinear V could still satisfy.
  thompson-v-not-lef: that excludes exact finite local embeddings, classically; this excludes approximate permutation models, which is open.
  openai-leavitt-unit-nonsofic: that is the first nonsofic group, produced by the Kazhdan compression mechanism; this would be a nonsofic group containing no infinite Kazhdan subgroup.
---

**OPEN.** Thompson's group `V = G_(2,1)` admits no injective homomorphism into
the universal sofic group.

## One-word Hamming form

Let `sigma_n` be permutation models of one finite presentation of `V` with
normalized Hamming relator defect tending to zero. Along an ultrafilter,
`g -> lim_omega |Fix(sigma_n(g))|/n` is a normalized positive-definite class
function, hence a character. By `thompson-v-character-simplex` it equals
`t tau_reg + (1-t) tau_triv`: every nontrivial word moves the same proportion
`t` of points. If `t > 0` the ultraproduct homomorphism is nontrivial, hence
injective by simplicity, and `V` is sofic. Restricting to the approximately
invariant free part yields models with `t = 1`. Consequently this claim holds
exactly when, for one fixed word `w != 1`, there is `epsilon > 0` such that
`w` moves at most a `1 - epsilon` proportion of points in every model of small
enough defect, and then the proportion tends to `0`.

## Scope

This claim would give a nonsofic group with no infinite Kazhdan subgroup
(Farley's Haagerup property for `V`). No mechanism in this graph produces
that. The OpenAI criterion, Kun--Thom Theorem A and Fournier-Facio's
torsion-free example all rest on property (T). A proof would therefore be a
second nonsoficity mechanism, the other open lane for which is
`nonsofic-hyperbolic-group`.

## Attempts

- **Kazhdan compression criterion.** It dies at the hypothesis: there is no
  infinite Kazhdan subgroup inside `V`.
- **Loeb-space support calculus.** Take the ultraproduct action of a sofic
  model and, for a proper cylinder `C`, let `E_C` be the set of points moved
  by the rigid stabilizer `V_C`. Conjugation makes all `lambda(E_C)` equal,
  and nesting `C' < C` gives `E_(C') < E_C`, so every `E_C` is one set a.e.
  By the one-word form it is the free part. Commuting subgroups with disjoint
  supports then both act freely on the same set, which is allowed. So the
  measure-level cylinder structure carries no contradiction, and the Cantor
  compressibility of `V` does not survive into sofic limits.
- **Surjunctivity.** A non-surjunctive `V` would be nonsofic (Gromov--Weiss),
  and surjunctivity passes to subgroups, so it would also refute Gottschalk
  over the Leavitt unit group. But the compressibility of `V` acts on the
  Cantor set, not on configurations `A^V`, and no candidate automaton over
  `V` is recorded. The negative Leavitt lane is
  `leavitt-unit-group-nonsurjunctive`.
