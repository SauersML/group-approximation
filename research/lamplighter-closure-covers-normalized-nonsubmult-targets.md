---
rg: 2
id: lamplighter-closure-covers-normalized-nonsubmult-targets
kind: claim
title: Uniform stability for normalized non-submultiplicative finite-dimensional targets, namely normalized Hilbert--Schmidt and normalized Hamming, also satisfies the lamplighter, amenable-quotient and coamenable-overgroup axioms
distinct_from:
  lamplighter-closure-invariants-cannot-decide-f-amenability: that is the barrier statement itself, whose imports cover only bi-invariant submultiplicative norms; this is the one remaining finite-dimensional family the barrier does not yet reach, and it is what the barrier's completeness claim needs.
  thompson-f-relator-system-stable-in-permutations: that is pointwise stability of a finite relator system, a defect measured relator by relator; this is the uniform defect, the supremum over all pairs, for normalized targets.
  hs-stability-plus-fd-residual-forces-nonhyperlinearity: that uses normalized-HS stability as a hypothesis about a single group; this asks whether the uniform version is closed under the three lamplighter axioms.
  thompson-f-is-not-hyperlinear: that is a statement about F alone in a tracial ultraproduct; this is a closure property of a class of groups.
---

**OPEN.** Let `U_f` range over the unitary groups `U(k)` with the *normalized* Hilbert--Schmidt
norm `‖x‖ = (tr_k x*x)^{1/2}`, or over the symmetric groups `S_k` with the normalized Hamming
distance. Say `Γ` is *uniformly stable* for this family if every uniform asymptotic homomorphism
`Γ → U_f` — defect measured as the supremum over all pairs `(g, h) ∈ Γ × Γ` — is uniformly close
to a homomorphism, with a linear estimate. Does this class satisfy

- **(L)** `G ≀ Z` is uniformly stable for every countable `G`;
- **(Q)** stability passes to quotients by amenable normal subgroups;
- **(C)** stability passes to coamenable overgroups?

These targets are finite-dimensional and their norms are bi-invariant, but they are **not
submultiplicative**: `‖E_11‖ = k^{-1/2}` while `‖E_11‖^2 = k^{-1}`. Submultiplicativity is a
standing hypothesis of the Fournier-Facio--Rangarajan heredity theorems
(`intro:thm:lamplighters`, `intro:prop:mapping`, `intro:prop:coamenable`), so none of the three
axioms is currently available here.

**Why it matters.** If the answer is yes, this family joins the class `LC` of
`lamplighter-closure-invariants-cannot-decide-f-amenability` and dies there like the others, and
that barrier's survivor list is complete as stated. If the answer is no, uniform normalized-HS or
normalized-Hamming stability is a live fourth survivor: combined with a Kazhdan-type uniform
stability of amenable groups for these targets, it would give a contrapositive certificate for
non-amenability of `F` that the barrier does not block.

## Attempts

- **Rescale the FFR proof (2026-09-18).** The obvious attack is to run FFR's lamplighter argument
  with `‖·‖_2` in place of a submultiplicative norm. It dies at the step where a defect is
  propagated through a product of `n` group elements: without `‖xy‖ ≤ ‖x‖‖y‖` the telescoping
  estimate that turns a pairwise defect into a defect along a word has no bound independent of
  `n`, and the lamplighter argument needs exactly that uniformity across the infinitely many
  lamp coordinates. FFR themselves record (arXiv:2301.03970) that they do not know whether
  Thompson's groups are uniformly approximable in Hilbert--Schmidt norm, so even the single-group
  instance at `F` is open upstream.
- **Import De Chiffre--Ozawa--Thom.** Their result is about the *flexible* Hilbert--Schmidt
  version and about amenable groups, not about `G ≀ Z` for arbitrary countable `G`, so it gives at
  most a hypothesis for the Kazhdan direction, not (L). Not re-verified here.
