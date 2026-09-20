---
rg: 2
id: fpbs-free-burnside-groups-lie-in-kesten-half
kind: claim
title: Every free Burnside group B(m,n) with m at least 3, or with m = 2 and n having a proper divisor at least 1003, has an infinite normal subgroup with nonamenable quotient, so it lies in case (alpha) of the percolation Kesten split
distinct_from:
  fpbs-burnside-normal-closure-split: that constructs N = <<x_1>> and uses it for cost (bounded-cost normal subgroup); this uses the same N, plus a new divisor quotient for m = 2, to place B(m,n) in case (alpha) of the Kesten split, and adds the finite-centralizer lemma and the consequence for the (beta) core
  fpbs-normally-coamenable-class-nonuniqueness: that is the (beta) premise of the route fpbs-residual-class-via-percolation-kesten-split, which leaves single B(m,n) unplaced; this shows the covered B(m,n) are not normally co-amenable, so for them only fpbs-percolation-kesten-normal-gap is needed
---

**ESTABLISHED (agent-verified, not refereed).** Proof in
`fpbs-free-burnside-groups-lie-in-kesten-half-proof`.

Case (α) of `fpbs-bs-via-percolation-kesten-split` means: some infinite normal
subgroup `N` of `Gamma` has `Gamma/N` nonamenable. Case (β) means `Gamma` is
normally co-amenable.

**Lemma 1 (finite centralizers kill finite normal subgroups).** Let `Gamma` be
infinite, and suppose `C_Gamma(g)` is finite for every `g != e`. Then every
nontrivial normal subgroup of `Gamma` is infinite. Hence `Gamma` lies in (α) iff
it has a nonamenable quotient `Gamma/K` with `K != {e}`.

**Theorem 2 (placement of free Burnside groups).** Let `n` be odd.

- **(a)** If `m >= 3` and `n >= 1003`, then `N = <<x_1>>` is infinite and
  `B(m,n)/N ≅ B(m-1,n)` is nonamenable. So `B(m,n)` lies in (α).
- **(b)** If `m >= 2`, `n` lies in the range of `fpbs-burnside-embedding-input`
  (cyclic centralizers of order `n`), and `n` has a divisor `d` with
  `1003 <= d < n`, then the kernel `K` of the canonical surjection
  `B(m,n) -> B(m,d)` is infinite and `B(m,d)` is nonamenable. So `B(m,n)` lies
  in (α).

A composite odd `n` has a proper divisor `d >= n^(1/2)`, so (b) covers every
composite odd `n >= 1003^2` in the centralizer range. For `m = 2` the only
exponents left unplaced are primes (and composite `n` whose largest proper
divisor is below 1003).

**Corollary 3 (one open premise for single Burnside groups).** For every
`B(m,n)` in (a) or (b), the percolation statement
`fpbs-percolation-kesten-normal-gap` for that `N` (resp. `K`), together with the
established `fpbs-relative-gap-along-any-subgroup-separates`, gives
`p_c < p_u` on every Cayley graph of `B(m,n)`. Premise (β),
`fpbs-normally-coamenable-class-nonuniqueness`, is not needed for these groups.

**Corollary 4 (the (β) core of the residual class).** Among the named
non-product members and candidates of
`fpbs-residual-price-one-non-ah-class-nonuniqueness`:

- single `B(m,n)` in (a) or (b) lie in (α);
- a torsion Tarski monster lies in (β): its proper subgroups are finite, so its
  only infinite normal subgroup is itself;
- a torsion-free Tarski monster with trivial centre is simple, so it lies in (β).
  A proper nontrivial normal subgroup is proper, hence infinite cyclic. The group
  has no proper subgroup of finite index, since such a subgroup would be cyclic
  and the group would be virtually cyclic, hence amenable. So the conjugation map
  to `Aut(Z) = Z/2` is trivial, the subgroup is central, and the centre is
  trivial by assumption.

So the only named groups that need premise (β) are Tarski monsters, together with
`B(2,p)` for primes `p`, which remain unplaced (see Remark 5).

**Remark 5 (prime exponent, conditional, not claimed).** Let `p` be a prime
for which Ol'shanskii's exponent-`p` Tarski monster `T_p` exists (every proper
subgroup of order `p`; `p > 10^75`), is nonamenable, and is 2-generated. Suppose
also that `p` is in the centralizer range. Then `B(2,p)` lies in (α).

- `T_p` has exponent `p`, so there is a surjection `B(2,p) -> T_p`.
- It is not injective. By the embedding theorem, `B(2,p)` contains a copy of
  `B(3,p)`. That copy is infinite, so if it sat inside `T_p` it would be all of
  `T_p`. But `B(3,p)` has abelianization `(Z/p)^3`, which needs 3 generators.
- Lemma 1 then makes the kernel infinite.

This is not claimed, because the existence of `T_p` for each large prime and its
nonamenability are not imported verbatim in the graph. The established monster
node names only the Izv. 1980 group.

**Not claimed.**

- Nothing here proves `fpbs-percolation-kesten-normal-gap`. Corollary 3 is a
  reduction, not a percolation theorem.
- The fixed price of single `B(m,n)` is not decided. They are residual-class
  members only if it is one. The placement in (α) holds either way.
- For (a) the threshold is that of the cited nodes (odd `n >= 1003`, with the
  centralizer theorem as used in `fpbs-burnside-normal-closure-split`). No new
  exponent threshold is asserted.
