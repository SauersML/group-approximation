---
rg: 2
id: free-binary-systems-carry-no-idempotent-mean
kind: claim
title: No free binary system carries an idempotent mean, so Moore's nonassociative Ellis lemma is false and his idempotent-measure route to the amenability of Thompson's F is dead
distinct_from:
  free-magma-carries-an-idempotent-finitely-additive-measure: that is the existence statement (Moore's withdrawn Theorem 1.2); this is its negation, published by the same author, and it refutes that claim.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that uses idempotent state measures on finite automata, which exist by Brouwer; this shows the infinite free magma itself has none.
  thompson-f-is-not-amenable: that is the opposite root; this refutes one route to the amenable root and says nothing about either answer.
artifacts:
  - experiments/free-magma-idempotent-2026-09-17/check_moore_z_set.py
---

**Statement.** Let `(S,*)` be a free binary system (free magma) on a nonempty set `I` of generators, for example the
free magma `T` on one generator. A *mean* on `S` is a finitely additive probability measure on all subsets of `S`.
For means `μ, ν` put

`μ*ν(X) = ∫ ( ∫ χ_X(s*t) dν(t) ) dμ(s)`,

the same convention as `μ^ν` in `free-magma-carries-an-idempotent-finitely-additive-measure`. Then no mean `μ`
satisfies `μ*μ = μ`.

**Source.** J. T. Moore, *Idempotent means on free binary systems do not exist*, arXiv:1807.05469v1 (15 Jul 2018);
published as *Nonexistence of idempotent means on free binary systems*, Canad. Math. Bull. (Cambridge Core
PII S0008439518000577; the journal volume was not checked). The LaTeX source
`no_idempotent.tex` was read in full on 2026-09-18. Verbatim, from the abstract:

> Free binary systems are shown to not admit idempotent means. This refutes a conjecture of the author. It is also
> shown that the extension of Hindman's theorem to nonassociative binary systems formulated and conjectured by the
> author is false.

and from Section 1:

> I previously (and incorrectly) claimed to have proved the existence of an idempotent mean on a free binary system
> \cite{amen_F}. [...] The question of \(F\)'s amenability remains open.

Here `amen_F` is arXiv:1209.2063, the source of the refuted claim. The product in the paper is, verbatim,
`\mu * \nu (f) = \int \left( \int f(s * t)\ d \nu (t) \right) d\mu (s)`, which is the convention above.

**Proof.** Re-proved in full in `free-binary-systems-carry-no-idempotent-mean-proof`, which does not rely on the
citation. The script `experiments/free-magma-idempotent-2026-09-17/check_moore_z_set.py` checks the two
combinatorial identities of the proof on all trees with at most 11 leaves (exit 0).

**Consequences in this graph.**
- It refutes `free-magma-carries-an-idempotent-finitely-additive-measure`. That disables the route
  `thompson-f-amenable-via-idempotent-magma-measure`, one of the two routes that
  `bin/cairn frontier --goal thompson-f-is-amenable` listed as one hole from complete.
- *Class kill.* Every approach to `thompson-f-is-amenable` through Moore's Theorem 3.3 (idempotent ⇒ `F`-invariant)
  applied to an idempotent mean on a free magma dies. The invariant is Moore's self-referential set `Z` below, with
  `μ(Z) = r`. Every member dies at the dichotomy: `r > 0` forces `r ≤ (1−r)^n` for all `n`, and `r = 0` forces
  `μ*μ(Z) = 1`.
- It is consistent with the finite-quotient class kill recorded on the refuted claim. That entry predicted that a
  refutation must use infinitely many nested sets. `Z` is built from the whole decreasing chain `T_0 ⊇ T_1 ⊇ ⋯`.
- Moore's Conjecture 1.3 of arXiv:1106.4735 (a nonassociative Hindman theorem) is also refuted in Section 3 of the
  same paper, by the coloring `c(μ) = μ(Z)`. That half is imported and not re-verified here. No node of this graph
  depends on it. The finitary Ramsey equivalence of `moore-ramsey-criterion-for-amenability` is untouched.

## Attempts

- **2026-09-18 (swarm-0917-w7-w7-f-last1, minimal-counterexample).** Found while attacking the last missing hole of
  the magma route. The published refutation already existed and was cited elsewhere in the graph
  (`research/artifacts/thompson-f-monomial-doubling-2026-09-13.md`), but it had not been attached to the hole. The
  proof was re-checked line by line, and the finite identities were checked by computer. Nothing is open here.
