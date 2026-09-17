---
rg: 2
id: fpbs-soft-collapse-over-conjugate-intersection-subgroups
kind: claim
title: A finitely generated infinite-index subgroup whose finite conjugate intersections are all infinite gives invariant sparse spines, and hence soft collapse families, on every Cayley graph, including every nonamenable Baumslag-Solitar group and SL_2(Z[1/p])
distinct_from:
  fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups: that selects cosets of a normal subgroup, where every trial point of a coset follows the same coset itinerary; here the subgroup need not be normal and the itinerary is only preserved on the infinite subgroup H ∩ v_1 H v_1^-1 ∩ ... ∩ v_d H v_d^-1, which is what (C) supplies. It covers BS(2,3) and SL_2(Z[1/p]), which that claim does not, and this proof does not depend on that open claim
  fpbs-soft-collapse-on-wreath-and-split-extensions: that criterion never applies to a commensurated subgroup (its own scope remark); here commensurated subgroups are the main case, so the two mechanisms are disjoint
  fpbs-soft-collapse-iff-invariant-sparse-spines: that proves the equivalence and builds spines only over a surjection onto Z with finitely generated kernel; here spines are built over an arbitrary coset space Gamma/H with (C)
  fpbs-sparse-spine-cost-bound: that converts factor-of-iid spines into cost bounds; the spines here are not factors of iid, since the selection is iid over Gamma/H with infinite stabilisers
  gaboriau-commensurated-chain-fixed-price-criterion: that is a cost statement on free actions; this is a percolation spine used to kill soft arguments for p_c < p_u
---

**ESTABLISHED (class-killing obstruction; agent-verified only, no referee
yet).** Proof in `fpbs-soft-collapse-over-conjugate-intersection-subgroups-proof`,
which requires only `fpbs-soft-collapse-iff-invariant-sparse-spines`.

Terminology (soft collapse family (S1)--(S4), invariant sparse spines) is that
of `fpbs-soft-collapse-iff-invariant-sparse-spines`.

**Condition (C).** A subgroup `H <= Gamma` satisfies (C) if `H` is infinite,
finitely generated, of infinite index, and for every finite set
`F ⊆ Gamma` the intersection `∩_{g in F} g H g^{-1}` is infinite.

**Theorem 1.** Let `Gamma` be finitely generated with a subgroup `H`
satisfying (C). Then every Cayley graph `G = Cay(Gamma,S)` has invariant sparse
spines. Explicitly, fix words `w_1, ..., w_k` in `S` for generators of `H`, and
let `U` be the set of group elements represented by prefixes of the `w_j`
(including the empty prefix). For `eps, eta in (0,1]`, the random subgraph built
from iid Bernoulli(`eps`) selected left cosets of `H` (with their word sheets)
and random-walk excursion connectors is a.s. connected and infinite, has
`Gamma`-invariant law and has `P(o in V(L)) <= (|U| + eta) eps`. If `Gamma` is
nonamenable, every Cayley graph of `Gamma` therefore carries a soft collapse
family (Theorem A).

**Proposition 2 (sufficient conditions for (C)).** Let `H <= Gamma` be
infinite, finitely generated and of infinite index. Then (C) holds in each of
the following cases.

* (a) `H` is commensurated: `g H g^{-1} ∩ H` has finite index in `H` for every
  `g`.
* (b) `H` contains an infinite normal subgroup of `Gamma` (finitely generated
  or not).
* (c) `H` is the stabiliser of a vertex `v` for an action of `Gamma` on a
  connected locally finite graph, and the orbit `Gamma v` is infinite. (This is
  a special case of (a).)

**Corollary 3 (members).** Every Cayley graph of each of the following
nonamenable groups carries a soft collapse family:

* `BS(m,n) = <a,t | t a^m t^{-1} = a^n>` with `|m|, |n| >= 2`, via `H = <a>`;
  in particular `BS(2,3)`;
* `SL_2(Z[1/p])` for a prime `p`, via `H = SL_2(Z)`;
* the fundamental group of a finite graph of groups with finitely generated
  infinite vertex groups, all edge groups of finite index in the adjacent vertex
  groups, and infinite Bass--Serre tree (so generalized Baumslag--Solitar groups
  that are nonamenable), via a vertex group;
* every group with a finitely generated infinite-index subgroup containing an
  infinite normal subgroup, which recovers the normal-subgroup case of
  `fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups` independently.

**Corollary 4 (obstruction).** On every Cayley graph of every nonamenable group
with a subgroup satisfying (C), no argument can prove `p_c < p_u` if its only
inputs are (a) facts about Bernoulli percolation at `p <= p_c` and (b) the
supercritical properties invariance, ergodicity, insertion tolerance,
monotonicity, uniqueness for `t > p_c` and continuity of `theta` at `p_c`.

- **Invariant:** existence of invariant sparse spines.
- **Step where every member dies:** the continuation from `p_c` to
  `p_c + eps`, exactly as in Theorem A.

**Mechanism, and why normality is not needed.** Sheets of selected cosets are
joined by random-walk excursions launched from every point of a selected coset
until the walk first enters a different selected coset. For a normal subgroup,
launching from `zh` instead of `z` does not change the sequence of cosets that a
fixed word visits. In general it does, and that is where the `F_2`, `<a>`
example of `fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups` blocks the
argument. But the itinerary of the word `v` is unchanged for
`h in H ∩ v_1 H v_1^{-1} ∩ ... ∩ v_d H v_d^{-1}`, where the `v_j` are the
prefixes of `v`, because `zh v_j H = z v_j (v_j^{-1} h v_j) H = z v_j H`.
Condition (C) makes this set of launch points infinite. The launch points give
independent trials, so Borel--Cantelli joins the two sheets a.s.

**Calibration (not load-bearing).** In `F_2` and in surface groups every
infinite finitely generated infinite-index subgroup is quasiconvex, and by
Gitik--Mitra--Rips--Sageev quasiconvex subgroups have finite height. So some
finite intersection of conjugates is finite and (C) fails, as it must: these
groups have cost greater than one. The Remark below shows that (C) forces
infimal cost one, consistent with Lyons. For the named members fixed price one
is also known from Gaboriau's criterion
`gaboriau-commensurated-chain-fixed-price-criterion`. For `BS(m,n)` take
`Gamma_1 = <a>` and the element `t`. For `SL_2(Z[1/p])` take `Gamma_1` the
upper unipotent `<u>`, then add `d = diag(p, 1/p)` (`d u d^{-1} = u^{p^2}`),
then the Weyl element `w`, which conjugates `d` to `d^{-1}`, so
`w^{-1} <u,d> w ∩ <u,d>` contains `<d>`. The group `<u,d,w>` contains all
upper and lower unipotents over `Z[1/p]`, which generate `SL_2(Z[1/p])`
(`Z[1/p]` is Euclidean). So these members lie in the fixed-price-one kernel.

**Remark (direct graphing, not load-bearing).** For the free action given by
the spine law times Bernoulli, the graphing that uses the edges of `L` together
with one edge from each vertex outside `L` toward `L` (ties broken by the
Bernoulli labels) generates the orbit relation. Its cost is at most
`1 + |S|(|U| + eta) eps / 2`, so `Gamma` has infimal cost one.

**Effect on the fixed-price-one kernel.** Of the survivors named in
`fpbs-fixed-price-one-percolation-kernel` and in the scope section of
`fpbs-soft-collapse-on-wreath-and-split-extensions`:

* `BS(2,3)` is **killed** (Corollary 3).
* **Torsion Tarski monsters** remain **open**. They have no infinite proper
  subgroup, so (C) cannot hold.
* **Torsion-free Tarski monsters** remain **open**. Every proper subgroup is
  infinite cyclic, and in the Ol'shanskii construction maximal cyclic subgroups
  are expected to be malnormal, which would make (C) fail. This is not checked
  here.
* **Free Burnside groups `B(m,n)`** remain **open**. No subgroup satisfying (C)
  is known.

Any remaining test case for soft arguments must be a group in which every
infinite, finitely generated, infinite-index subgroup has a finite intersection
of finitely many conjugates. Torsion Tarski monsters satisfy this vacuously.
For torsion-free Tarski monsters and `B(m,n)` it is unverified.
