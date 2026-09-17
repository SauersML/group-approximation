---
rg: 2
id: fpbs-finite-energy-fkg-collapse-over-central-z2-slabs
kind: claim
title: Collapse families that equal Bernoulli up to p_c and are also deletion tolerant and Harris-FKG exist on every Cayley graph of a nonamenable group with a central Z inside a Z2
distinct_from:
  fpbs-soft-collapse-iff-invariant-sparse-spines: that family forces whole sheets open, so it is not deletion tolerant and FKG is left undecided; here every edge can be closed, every omega_t is an increasing function of independent variables, and the spine is built from thinned amenable slabs joined by connectors that recur along a central direction
  fpbs-sparse-spine-cost-bound: that converts an FIID spine into a cost bound; this builds a percolation family and is not FIID
---

**ESTABLISHED (class-killing obstruction).** Proof in
`fpbs-finite-energy-fkg-collapse-over-central-z2-slabs-proof`.

**Class `Z`.** A finitely generated nonamenable group `Gamma` belongs to `Z` if
it has a central element `t` of infinite order and an element `g` with
`<g> ∩ <t> = 1`, so that `H = <g,t> ≅ Z^2`. Examples:

* `Lambda x Z` for every finitely generated nonamenable `Lambda` with an element
  of infinite order, including `F_2 x Z`;
* braid groups `B_n` with `n >= 3`;
* `pi_1` of the unit tangent bundle of a closed hyperbolic surface.

Let `S` be a finite symmetric generating set, `G = Cay(Gamma,S)`, and
`xi_t = {e : U_e <= t}` the standard coupling.

**Strong soft collapse family.** It satisfies (S1)–(S4) of
`fpbs-soft-collapse-iff-invariant-sparse-spines`: monotone; Bernoulli joint law
for `t <= p_c`; ergodic and insertion tolerant; for every `t > p_c` exactly one
infinite cluster, with `theta(t) -> 0` as `t ↓ p_c`. It also satisfies:

* **(S5) deletion tolerance.** For every `t in (0,1]`, edge `e` and event `A`
  with `P(omega_t in A) > 0`, we have `P(omega_t in Pi_{¬e} A) > 0`. Together
  with (S3), this is qualitative finite energy in both directions.
* **(S6) Harris–FKG.** For every `t`, `omega_t` is an increasing function of
  countably many independent real variables. So increasing events are
  positively correlated.

**Theorem.** For every `Gamma in Z` and every finite symmetric generating set
`S`, `Cay(Gamma,S)` carries a strong soft collapse family. For `t > p_c` close
to `p_c`, `omega_t` is not a product measure.

**Corollary (obstruction).** `F_2 x Z` is in `Z`, and by
`fpbs-simple-generating-set-with-gap-exists` some Cayley graph of it has
`p_c < p_u`. So on that graph no argument can prove `p_c < p_u` if its inputs
are only:

1. facts about Bernoulli percolation at `p <= p_c`;
2. for `t > p_c`: invariance, ergodicity, a monotone coupling that agrees with
   the standard one up to `p_c`, insertion and deletion tolerance, Harris–FKG,
   uniqueness, and continuity of `theta` at `p_c`;
3. everything derived from items 1 and 2, such as Burton–Keane trifurcation
   counting, Lyons–Schramm indistinguishability, the Newman–Schulman `0/1/∞`
   law, the BLPS results for invariant percolations, and FKG gluing.

The same holds for `Cay(F_2 x Z, S)` with every other `S`, including the rigid
sets of `fpbs-product-every-generating-set` (Choi–Seo Q1.3): a proof for any
of those graphs cannot be soft in this sense either.

**Exact failing step.** Take any "collapse `p_u = p_c` leads to a contradiction"
argument that goes from `p_c` to `p_c + eps` using only the supercritical
properties in item 2. That step must fail, because the family has all of them
and collapses anyway. What the family lacks, at every `t` close to `p_c`, is:

* **Independent increments.** `omega_t \ omega_s` is not independent of
  `omega_s`. This is what BK/Reimer, Russo–Margulis, the Aizenman–Barsky and
  Menshikov differential inequalities, and sprinkling all use.
* **Mixing.** The slab selection is invariant along the central direction, and
  mixing is not claimed.
* **Uniform finite energy.** Only a qualitative bound is proved. The
  conditional cost of closing an edge can involve the finite detached set `D`
  of the proof.
* **FIID-ness over `Gamma`.**

With sw-008, this changes the known requirement from "must use supercritical
product structure, or at least deletion tolerance or FKG" to "must use
independent increments, mixing, uniform finite energy, or an FIID/cost
property". On `Z`, the last of these is useless for `p_c < p_u` (next section).

**Calibration and consistency.**

* Every group in `Z` has an infinite amenable normal subgroup `<t>`. So it has
  fixed price one (Gaboriau), and Lyons' cost route gives nothing, as it must.
* `F_2` and `F_2 x F_2` have trivial centre and are not in `Z`.
* The spines `eta_n` of the proof are invariant sparse spines, which agrees
  with Theorem A of sw-008.
* On an amenable group such as `Z^d` (take `H = Z^2`, `t` any basis vector,
  and `d >= 11`, where `theta(p_c) = 0` is known), the same construction runs
  and gives a collapse. This matches `p_c = p_u` (Burton–Keane), so the method
  proves nothing false. Nonamenability enters only through
  `fpbs-critical-no-infinite-cluster` and the fact that a window exists.

**Paradigm answers.**

* **Why this succeeds where sw-008 stopped.** It changes the spine object. A
  deterministic open sheet cannot lose an edge. A *thinned amenable slab* has
  a unique giant (Burton–Keane inside the slab), which loses only a finite piece
  when an edge is closed. Gluing is done by all-or-nothing connectors whose
  existence comes from recurrence along the central `t`, not from forcing.
  The finite piece that falls off is absorbed into the critical Bernoulli part,
  which gives deletion tolerance. The structure is an increasing function of
  independent variables, which gives FKG.
* **First falsifiable step.** Removing one edge from the thinned slab giant
  detaches only a finite set. This follows from the a.s. uniqueness of the slab
  giant and absolute continuity of the edge flip.
* **Calibration.** Lyons' fixed-price-two groups are not in `Z`, and every
  group in `Z` has fixed price one, as above.
