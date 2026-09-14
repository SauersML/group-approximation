---
rg: 2
id: bounded-support-char-p-units-force-qbar-units
kind: claim
title: Nontrivial units on a fixed support pair occur in finitely many characteristics or in almost all, and almost all exactly when they occur over Qbar
distinct_from:
  support-pair-unit-scheme-is-finite-over-z: that bounds the number of units on a support pair and needs every field group ring of G to be a domain; this compares the sets of characteristics carrying nontrivial units, for every group.
  unit-conjecture-fails-over-complex-numbers: that exhibits nontrivial complex units on one support pair of the Promislow group; this is a transfer principle between characteristics that applies to every support pair.
  murray-z-only-ansatz-has-no-char0-units: that excludes characteristic-zero solutions of Murray's z-only shape; this explains why a family of units in growing characteristic must have growing support unless Qbar carries a unit on a fixed pair.
  rational-unit-conjecture-torsion-free: that is the unit conjecture over Q for every torsion-free group; this is an elementary transfer principle that decides no instance of it.
---

**ESTABLISHED** (elementary; no novelty claimed). Let `G` be a group and let
`S, T` be finite subsets of `G`. Call a unit `u` of `k[G]` *on (S,T)* if
`supp u in S` and `supp u^(-1) in T`, and *nontrivial* if it is not `lambda g`.
Let `Pi(S,T)` be the set of primes `p` such that some field of characteristic
`p` carries a nontrivial unit on `(S,T)`.

1. **Dichotomy.** Either `Pi(S,T)` is finite, or it contains every prime outside
   a finite set. The second case holds exactly when `Qbar[G]` carries a
   nontrivial unit on `(S,T)`.
2. **Descent to prime fields.** If a number field `K` carries a nontrivial unit
   on `(S,T)`, then for every prime `𝔭` of `K` outside a finite set, the residue
   field `O_K/𝔭` carries one. For `K = Q`, `F_p` carries one for all but finitely
   many `p`.
3. **Uniform-support families.** If for infinitely many primes `p` some field of
   characteristic `p` carries a nontrivial unit on one fixed pair `(S,T)`, then
   `Qbar[G]` carries a nontrivial unit on `(S,T)`, with coefficients in a number
   field. So an "ultraproduct over characteristics" of a bounded-support family
   produces units over `Qbar`, never directly over `Q`.
4. **Certificate over Q.** If infinitely many primes `p` have no nontrivial unit
   of `F_p[G]` on `(S,T)`, then `Q[G]` has no nontrivial unit on `(S,T)`.

**Instances on the Promislow group.**
- Gardam's complex units (coefficients in `Z[zeta_8]`) put the 21-element pair
  in the second case of item 1, which matches his corollary over `F_(p^2)`.
- Murray's units of `F_d[P]` (arXiv:2106.02147, third theorem) have supports of
  sizes 39, 73 and 103 for `d = 3, 5, 7` at `t in {0, 1}`, `w = 0`
  (`research/artifacts/hl-kaplansky-unit-lift-2026-09-13.md`). The factor
  `h = (1 - z^(1-2t))^(d-2)` grows with `d`, so item 3 does not apply to the
  family as a whole.

DERIVATION
[[bounded-support-char-p-units-force-qbar-units-proof]]
