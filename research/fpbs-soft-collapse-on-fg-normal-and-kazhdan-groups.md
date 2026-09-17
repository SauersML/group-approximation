---
rg: 2
id: fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups
kind: claim
title: Invariant sparse spines, and hence soft collapse families, exist on every Cayley graph of a nonamenable group with an infinite finitely generated normal subgroup of infinite index and of every infinite Kazhdan group
distinct_from:
  fpbs-soft-collapse-iff-invariant-sparse-spines: that proves the equivalence and builds spines only over a surjection onto Z with finitely generated kernel; here the quotient is an arbitrary infinite group, the connectors are random-walk excursions instead of powers of a fixed element, and the Kazhdan class is added through the Hutchcroft--Pete condensation
  fpbs-finite-energy-fkg-collapse-over-central-z2-slabs: that adds deletion tolerance and Harris--FKG but needs a central Z inside a Z2; here only the soft axioms (S1)--(S4) are produced, on a much larger class
  fpbs-kazhdan-sparse-spines: that asks for factor-of-iid spines, which would give fixed price one; the Kazhdan spines here are invariant but not factors of iid, and prove nothing about cost beyond Hutchcroft--Pete
  fpbs-kazhdan-groups-have-cost-one: that is the cost statement; here the same construction is used as a percolation spine to kill soft arguments for p_c < p_u
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts); it is not
established because one referee lens refuted the statement as written.

Terminology (soft collapse family (S1)--(S4), invariant sparse spines) is that
of `fpbs-soft-collapse-iff-invariant-sparse-spines`. A finitely generated group
`Gamma` *has spines* if some Cayley graph of `Gamma` has invariant sparse
spines.

**Lemma 1 (spines are a commensurability property).** If one Cayley graph of
`Gamma` has invariant sparse spines, then every Cayley graph of `Gamma` does.
If `Gamma' <= Gamma` has finite index, then `Gamma` has spines if and only if
`Gamma'` does.

**Theorem 1 (normal subgroups).** Let `Gamma` be finitely generated with an
infinite, finitely generated normal subgroup `N` of infinite index. Then every
Cayley graph of `Gamma` has invariant sparse spines. Explicitly, for
`eps, eta in (0,1]` the random subgraph built from iid Bernoulli(`eps`) sheets
over `Gamma/N` and random-walk connectors has density at most
`(1 + sum_j |w_j| + eta) eps`, where the `w_j` are words for generators of `N`.

**Theorem 2 (Kazhdan groups).** Let `Gamma` be an infinite group with
Kazhdan's property (T). Then every Cayley graph of `Gamma` has invariant sparse
spines: for every `p in (0,1)`, the unique infinite cluster of the
Hutchcroft--Pete graph `eta` from the proof of their Theorem 1.2
(arXiv:1810.11015) is an invariant connected infinite subgraph with
`P(o in V) <= p`.

**Corollary 3 (obstruction on the Lyons kernel).** Let `K` be the class of
nonamenable finitely generated groups that are commensurable, by passing to a
finite-index subgroup or overgroup, with a group having an infinite finitely
generated normal subgroup of infinite index, together with all infinite Kazhdan
groups. Every Cayley graph of every group in `K` carries a soft collapse family
(Theorem A of `fpbs-soft-collapse-iff-invariant-sparse-spines`). Hence no
argument whose only inputs are Bernoulli facts at parameters `p <= p_c` and the
supercritical properties (S1)--(S4) (invariance, ergodicity, insertion
tolerance, monotonicity, uniqueness above `p_c`, continuity of `theta` at
`p_c`) can prove `p_c < p_u` on any Cayley graph of any group in `K`.

- **Invariant:** existence of invariant sparse spines.
- **Step where every member dies:** the continuation from `p_c` to
  `p_c + eps`. The collapse family on `G` satisfies every admissible input and
  has a unique infinite cluster for every `t > p_c`.
- This does not depend on whether a window is already known on `G`, nor on
  whether `Gamma` has fixed price one. On Kazhdan groups fixed price one is open
  (Hutchcroft--Pete, abstract), but soft arguments die there either way.

Members of `K` that the kernel `fpbs-fixed-price-one-percolation-kernel` and the
residual class `fpbs-residual-price-one-non-ah-class-nonuniqueness` are about:

- every `H x K'` with `H` and `K'` infinite and finitely generated and the
  product nonamenable, including the
  residual-class members `T x T'` (torsion Tarski monsters) and
  `B(m,n) x B(m',n')`;
- every nonamenable group with infinite finitely generated centre of infinite
  index, braid groups `B_n` (`n >= 3`), and fibred hyperbolic 3-manifold groups;
- surface-by-surface groups, and `F_2 x F_2`;
- every infinite Kazhdan group: torsion Kazhdan groups, lattices in `Sp(n,1)`
  and `F_4^(-20)`, Kazhdan hyperbolic groups, Kazhdan Golod--Shafarevich groups,
  and `SL_n(Z)` for `n >= 3`.

**Calibration.** Invariant sparse spines force cost one for the product of the
spine action with Bernoulli (`fpbs-sparse-spine-cost-bound`). This agrees with
Gaboriau (infinite finitely generated normal subgroup of infinite index gives
fixed price one) and with Hutchcroft--Pete (Kazhdan groups have cost one).
`F_2` is in neither class.

**What remains open for soft arguments.** Nonamenable groups outside `K`. The
named test cases are:

- a single torsion Tarski monster (simple, no (T) known);
- a torsion-free Tarski monster with trivial centre. Its proper subgroups are
  cyclic, and a normal infinite cyclic subgroup of a group with no proper
  finite-index subgroup is central, so it has no infinite proper normal
  subgroup;
- a single free Burnside group `B(m,n)` with `m >= 2` and odd `n >= 1003`,
  unless it is shown to have (T) or to be commensurable with a group having an
  infinite finitely generated normal subgroup of infinite index;
- groups whose infinite normal subgroups are all infinitely generated and which
  lack (T), such as `Z/2 wr F_2` and `BS(2,3)`.

The first three are exactly the unsettled members of the residual class
`fpbs-residual-price-one-non-ah-class-nonuniqueness` that are not products.
Whether soft arguments can succeed there is the question of whether they have
invariant sparse spines.

## Attempts

1. **Iid Bernoulli coset sheets joined by random-walk excursions, plus the
   Hutchcroft--Pete maximal-frequency cluster (2026-09-17).** See
   `research/artifacts/fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups-proof-2026-09-17.md`.
   It requires `fpbs-soft-collapse-iff-invariant-sparse-spines`. Referee lens 2
   returned *refuted*, at the level of the statement only: the membership
   bullet "every `H x K'` with `H` infinite and finitely generated" drops the
   hypothesis the proof's membership check (section 4) uses, namely `K'`
   infinite (so `H x {e}` has infinite index), and membership in `K` also needs
   `K'` finitely generated and the product nonamenable. As written, `K' = {e}`
   would put `F_2` in `K`, contradicting the calibration, and `K' = Z/2` would
   settle a single torsion Tarski monster, listed as open. The bullet above has
   been corrected accordingly. Lens 2 also flagged that the `F_2` calibration
   cites `fpbs-sparse-spine-cost-bound`, which is about factor-of-iid spines;
   an invariant spine times Bernoulli is not FIID, so the calibration should
   instead cite Hutchcroft--Pete Prop 2.1 or Gaboriau's induction formula with
   fixed price 2 for `F_2`. Lenses 1 and 3 returned *survives*; all three lenses
   checked Lemma 1, Theorem 1 (including the Borel--Cantelli joining step),
   Theorem 2 against arXiv:1810.11015v2, and Corollary 3, and found no
   mathematical gap. Lens 3 noted that the claim that `Z/2 wr F_2` and
   `BS(2,3)` have no infinite finitely generated normal subgroup of infinite
   index is thinly justified (not load-bearing). *Pending referee.*
