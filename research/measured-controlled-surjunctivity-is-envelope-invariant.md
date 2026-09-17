---
rg: 2
id: measured-controlled-surjunctivity-is-envelope-invariant
kind: claim
title: Strict automata over measured Cantor bases induce across cocompact lattices of a totally disconnected envelope, so measured controlled surjunctivity is an envelope invariant
distinct_from:
  compressible-base-controlled-automata-are-strict: that builds strict controlled automata over bases with no invariant measure and kills fibrewise arguments there; this transports strict controlled automata between two lattices of one envelope and keeps an invariant measure on the base, where that swindle is unavailable.
  surjunctivity-is-a-commensurability-invariant: that moves ordinary surjunctivity between commensurable groups; this moves the controlled, measured-base property between any two cocompact lattices of a totally disconnected group, and recovers the finite-index case with a discrete envelope.
  induced-actions-sofic-iff-homogeneous-action-sofic: that tracks soficity of induced p.m.p. actions; this induces cellular automata and needs no sofic model of any action.
  paunescu-class-is-measure-equivalence-invariant: that moves soficity of all actions along measure couplings; this moves strictness of automata along topological couplings with clopen fundamental domains.
artifacts:
  - research/measured-controlled-surjunctivity-is-envelope-invariant-proof.md
---

**ESTABLISHED (unreviewed; proof in `measured-controlled-surjunctivity-is-envelope-invariant-proof`).**

**Setting.** Controlled automata are as in `compressible-base-controlled-automata-are-strict`. A
group `G` acts on a compact metrizable zero-dimensional space `X`, and `A` is a finite alphabet.
An `X`-controlled automaton is a continuous `Phi(y, x) = (tau_x(y), x)` on `A^G x X` that commutes
with the diagonal `G`-action, where `tau_x(y)(e)` depends only on `y|_S`, for a finite `S`, and on
the cell of `x` in a finite clopen partition.

Call `Phi` **strict** if every fibre map `tau_x` is injective and no fibre map `tau_x` is
surjective. Call `G` **measured-controlled surjunctive** (MCS) if no `X` that carries a
`G`-invariant Borel probability measure of full support admits a strict `X`-controlled automaton.

**Theorem.** Let `H` be a locally compact second countable unimodular group whose compact open
subgroups form a neighbourhood basis of the identity. Let `Gamma, Lambda <= H` be discrete
cocompact subgroups.

1. **Induction.** Suppose `Gamma` acts on `Y` and `Psi` is a strict `Y`-controlled automaton over
   the alphabet `A`. Put `Z = (H x Y)/Gamma`, where `(h, y)gamma = (h gamma, gamma^-1 y)`, and let
   `Lambda` act on the left. Then:
   - `Z` is compact, metrizable and zero-dimensional;
   - there are `K >= 1` and a strict `Z`-controlled automaton for `Lambda` over the alphabet
     `A^K`;
   - every fibre map of the new automaton is conjugate to some `psi_y` times an identity map on
     the unused coordinates.
2. **Measure.** If `nu` is a `Gamma`-invariant probability of full support on `Y`, then `Z`
   carries a `Lambda`-invariant probability of full support.
3. **Invariance.** `Gamma` is MCS iff `Lambda` is MCS.
4. **Consequence for automata.** An MCS group is surjunctive, by taking the one-point base. So if
   one cocompact lattice of `H` is MCS, every cocompact lattice of `H` is surjunctive. In
   particular, a strict cellular automaton on `Gamma` produces a strict controlled automaton for
   `Lambda` over the homogeneous space `H/Gamma`, and that space carries Haar probability.

**Why it matters.** Surjunctivity itself is not known to pass between two lattices of one
envelope. The controlled, measured-base strengthening does pass, and it is exactly what induction
produces. `compressible-base-controlled-automata-are-strict` shows the measure hypothesis cannot be
dropped: every nonamenable group has strict controlled automata over some measureless Cantor base.

**Case H discrete.** Then `Gamma` and `Lambda` are finite-index subgroups of `H`, so MCS is a
commensurability invariant.

**Main application.** `product-tree-lattices-surjunctive-via-envelope-transfer` puts
every cocompact lattice in `Aut(T_p) x Aut(T_q)` below one residually finite group,
`C_2^(*p) x C_2^(*q)`, for this property. That covers Radu's lattice, Burger–Mozes groups and
Wise's lattices.
