---
rg: 2
id: fpbs-soft-collapse-on-wreath-and-split-extensions
kind: claim
title: A coset bypass criterion gives invariant sparse spines, and hence soft collapse families, on every Cayley graph of every nonamenable permutational wreath product with an infinite orbit and of split extensions with a finite-class moving element
distinct_from:
  fpbs-soft-collapse-iff-invariant-sparse-spines: that proves the equivalence of soft collapse families with spines and builds spines only over a surjection onto Z with finitely generated kernel; here the selected objects are cosets of a non-normal subgroup, the coset graph has infinite degree, and connectivity comes from infinitely many disjoint conjugate bypasses rather than a quotient Cayley graph
  fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups: that selects cosets of a normal subgroup (a locally finite quotient Cayley graph) and needs random-walk connectors; here the subgroup is not normal, no connectors are needed, and the class includes Z/2 wr F_2, which that claim lists as a survivor
  fpbs-finite-energy-fkg-collapse-over-central-z2-slabs: that adds deletion tolerance and Harris--FKG over a central Z inside a Z2; here only the soft axioms (S1)--(S4) are produced
---

**ESTABLISHED (class-killing obstruction; agent-verified only, no referee
yet).** Proof in `fpbs-soft-collapse-on-wreath-and-split-extensions-proof`,
which requires only `fpbs-soft-collapse-iff-invariant-sparse-spines`.

Terminology (soft collapse family (S1)--(S4), invariant sparse spines) is that
of `fpbs-soft-collapse-iff-invariant-sparse-spines`. For a subgroup `K` write
`K^p = p K p^{-1}`.

**Theorem 1 (coset bypass criterion).** Let `Gamma` be finitely generated and
`K <= Gamma` an infinite finitely generated subgroup. Suppose there are a
finite set `Sigma_1 ⊆ Gamma` and an infinite set `Y ⊆ Gamma` with

* (B2) for every `x in Gamma`, `x^{-1} y x in K Sigma_1 K` for all but finitely
  many `y in Y`;
* (B3) for all `g, p in Gamma`, the set `Y ∩ g K^p` is finite.

Then every Cayley graph `Cay(Gamma,S)` has invariant sparse spines. If
`Gamma` is nonamenable, every Cayley graph of `Gamma` therefore carries a soft
collapse family (Theorem A). Explicitly, the spine built from iid
Bernoulli(`eps`) selection of left cosets of `K` has density at most
`|B_R| eps`, where `R` is an S-length bound for fixed words of the elements of
`Sigma_1 ∪ Sigma_1^{-1}`, of `S`, and of a finite generating set of `K`.

**Corollary 2 (split extensions).** Let `Gamma = N ⋊ K` be finitely generated
with `K` infinite and finitely generated. Suppose some `sigma in N` has finite
`N`-conjugacy class and infinite `K`-orbit `{k sigma k^{-1} : k in K}`. Then
Theorem 1 applies with `Sigma_1 = sigma^N` and `Y` that orbit. Examples:
`Z^infty`-type lamp groups `(⊕_{F_2} Z) ⋊ F_2 = Z wr F_2`, and every split
extension with abelian `N` in which some element has an infinite `K`-orbit.

**Corollary 3 (permutational wreath products).** Let `A` be a nontrivial
finitely generated group, `Q` an infinite finitely generated group, and `X` a
`Q`-set with finitely many orbits, at least one of them infinite. Then every
Cayley graph of `Gamma = A wr_X Q = (⊕_X A) ⋊ Q` has invariant sparse spines.
If `Gamma` is nonamenable (equivalently `A` or `Q` is nonamenable), every
Cayley graph carries a soft collapse family. This includes `Z/2 wr F_2`,
`Z wr F_2`, `F_2 wr Z`, `F_2 wr F_2`, and `A wr_{Q/H} Q` for every infinite
index subgroup `H` of a nonamenable finitely generated `Q`.

**Corollary 4 (obstruction on these groups).** On every Cayley graph of every
nonamenable group in Corollaries 2--3, no argument can prove `p_c < p_u` if its
inputs are only (a) facts about Bernoulli percolation at `p <= p_c` and (b) the
supercritical properties invariance, ergodicity, insertion tolerance,
monotonicity, uniqueness for `t > p_c` and continuity of `theta` at `p_c`. Such
an argument would also prove nonuniqueness for the family of Theorem A, which
has a unique infinite cluster for every `t > p_c`. **Invariant:** existence of
invariant sparse spines. **Step where every member dies:** the continuation
from `p_c` to `p_c + eps`, exactly as in Theorem A.

**Why this is new ground.** Theorem B of
`fpbs-soft-collapse-iff-invariant-sparse-spines` needs a surjection onto `Z`
with finitely generated kernel. The open claim
`fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups` needs an infinite finitely
generated normal subgroup of infinite index, or property (T). `Z/2 wr F_2` is
listed there, and in `fpbs-fixed-price-one-percolation-kernel`, as a survivor.
Theorem 1 uses a **non-normal, non-commensurated** subgroup: the acting group
`Q`. Its coset graph has infinite degree, and connectivity of the selected
cosets comes from infinitely many pairwise disjoint conjugated bypasses
`K, yK, y d_1, ..., yxK, xK`, not from a locally finite quotient.

**Scope remark (where the criterion cannot apply).** If `K` is commensurated
(for instance normal), every double coset `K sigma K` is a finite union of left
cosets. Then (B2) with `x = e` puts `Y` in finitely many left cosets of `K`, and
(B3) with `p = e` makes `Y` finite, a contradiction. So Theorem 1 never applies
with a commensurated `K`. This is the reason it reaches the wreath products and
is disjoint in mechanism from the normal-subgroup construction. It also shows
why `BS(2,3)` is not covered with `K = <a>`, which is commensurated.

**Calibration (not load-bearing).** `F_2` has fixed price two (Gaboriau), and
spines are expected to force cost one (see the calibration discussion in
`fpbs-soft-collapse-iff-invariant-sparse-spines` and the referee note in
`fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups` on which citation is
correct), so the criterion should fail on `F_2`. It does, by direct check for
`K = <a>`: (B2) with `x = e` gives `y = a^i sigma a^j` with `sigma` from a
finite set, and (B3) forces `|i|` unbounded along `Y`; conjugating by `x = b`
gives the reduced word `b^{-1} a^i sigma a^j b` (for `sigma` not beginning or
ending with `a`), which begins with `b^{-1} a^i` and so lies in no
`<a> sigma' <a>` with `|sigma'|` bounded once `|i|` is large. So (B2) fails for
`x = b` on infinitely many `y`.

**Consistency check.** Corollary 3 gives spines on `Z/2 wr F_2`, which has
fixed price one because it has an infinite amenable normal subgroup,
`⊕_{F_2} Z/2` (Gaboriau). This agrees with its listing in the fixed-price-one
kernel, and there is no conflict with Lyons.

**What remains of the fixed-price-one kernel for soft arguments.** Of the
named survivors:

* `Z/2 wr F_2` is now **killed** (Corollary 3).
* `BS(2,3)` is **open**. `<a>` is commensurated, so the criterion needs
  a different, non-commensurated `K`; none is known to work.
* **Torsion Tarski monsters** are **open**. Every proper subgroup is finite,
  so there is no infinite `K` of infinite index and Theorem 1 cannot apply.
* **Torsion-free Tarski monsters** and `B(m,n)` are **open**. No choice of
  `K`, `Sigma_1`, `Y` has been checked.
