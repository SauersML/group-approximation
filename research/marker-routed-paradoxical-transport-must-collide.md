---
rg: 2
id: marker-routed-paradoxical-transport-must-collide
kind: claim
title: Over every group, a local rule that routes clopen marker sites 2-to-1 into markers collides on a set of positive Bernoulli density, and is collision-free only on subshifts of finite type where no invariant measure charges the markers
distinct_from:
  certificate-controlled-routing-is-surjunctive: that routes data along a separate certificate kept in the output and concludes surjectivity of the automaton; this lets the routing read the routed configuration itself (Garden-of-Eden markers), allows m targets per source and a target set, and concludes a collision density bound and a support theorem for the transport, not for an automaton.
  f2-groups-have-paradoxical-free-minimal-subshifts: that builds a subshift carrying an elementary paradox; this proves that any locally defined paradox must live on a subshift of finite type without invariant measures charging the markers, and that on the full shift or any automaton image it collides.
  injective-ca-random-order-transport-identity: that transports decoder information (log |A| per output site) under a random order; this transports sites, and the invariant is the indegree expectation, not information.
  measure-free-minimal-cantor-action-with-finite-clopen-type: that exhibits a measure-free action with finite clopen type; this shows measure-freeness is forced on any configuration class where a local marker compression works, and exhibits the end-pointer SFT over F_2.
artifacts:
  - experiments/paradoxical-transport-2026-09-17/marker_routing_sat.py
---

**ESTABLISHED** by `marker-routed-transport-mass-balance-proof` (self-contained; mass-transport principle).

This is the obstruction answering lane (d), *configuration-dependent paradoxical transport*, of
`notes/agent-coordination-playbook-2026-09-17.md`, Section 11. That lane asks for clopen markers built from a
Garden of Eden pattern of `τ` and a finite-radius rule that uses them to route a collision-free 2-to-1 compression of
sites. The answer: over **every** group the compression must collide, and the collision mass is exactly the paradox
gain under every invariant measure.

## Setting

`G` is a countable discrete group, `B` a finite alphabet, `(h·x)(g) = x(h^(-1) g)`, and `X ⊆ B^G` a closed invariant
set. For a subset `E ⊆ X` put `E(x) = {g ∈ G : g^(-1)·x ∈ E}`; for clopen `E` this is "a fixed finite pattern occurs at
`g`". A **marker routing** is `(M, T, S, s_1, …, s_m)`:

- `M, T ⊆ X` clopen (markers and admissible targets), `S ⊆ G` finite, `m >= 1`;
- continuous `s_i : M → S`, used at a marker site `g ∈ M(x)` to send it to `p_i(x, g) = g · s_i(g^(-1)·x)`.

Its indegree at the identity is `N(x) = #{(g, i) : g ∈ M(x), p_i(x, g) = 1}`. The routing is **collision-free into `T`
on `Y ⊆ X`** if for every `x ∈ Y` the map `(g, i) ↦ p_i(x, g)` is injective on `M(x) × {1..m}` with image in `T(x)`;
equivalently `N <= 1_T` on all translates of `Y`.

## Statement

1. **Balance.** For every `G`-invariant Borel probability `μ` on `X`: `E_μ N = m μ(M)`. Hence
   `E_μ[(N-1)_+] + E_μ[N 1_(X∖T)] >= m μ(M) - μ(T)`. The same identity holds for Borel `s_i`.
2. **Paradox is invisible to invariant measures.** If the routing is collision-free into `T` on a closed invariant
   `Y`, then `m μ(M ∩ Y) <= μ(T ∩ Y)` for every invariant `μ` on `Y`. With `m >= 2` and `T ⊆ M`:
   `μ(M) = 0` for every invariant `μ` on `Y`.
3. **Full shifts and automaton images collide.** Let `X = Ψ(C^G)` for a cellular automaton `Ψ` (for example
   `X = B^G`, or the image of `τ`, or the image of a design). Then `ν = Ψ_* β` (`β` uniform Bernoulli) is invariant with
   full support, so a nonempty clopen `M` has `ν(M) > 0`. With `m >= 2` and `T ⊆ M`, **no** marker routing on `X` is
   collision-free, and the defect density satisfies `E_ν[(N-1)_+] + E_ν[N 1_(X∖M)] >= (m-1) ν(M) > 0`. The defect event
   is determined by a finite window, so it is witnessed by an explicit finite pattern. For markers `M = [x|_K = P]`
   given by a Garden of Eden pattern `P` of `τ` on the input shift `A^G`: defect density `>= (m-1) |A|^(-|K|)`.
4. **Where a collision-free paradox can live.** If the routing is collision-free into `T ⊆ M` (`m >= 2`) on a closed
   invariant `Y`, then there is `R` such that it is collision-free on the subshift of finite type
   `Y_R = {x : every pattern of x on a translate of B_R occurs in Y}`. So `Y_R` carries no invariant probability
   charging `M`, and `β(M ∩ Y_R) = 0` for the uniform Bernoulli measure on `B^G`. A design defined on the whole input
   shift can invoke the compression collision-free only on a locally certified SFT on which no invariant measure charges `M` (so `M ∩ Y_R` is Bernoulli-null).
5. **Sharpness (both hypotheses are used).**
   - *Invariant measure.* Over `F_2 = <a, b>` the **end-pointer SFT** `Y ⊆ {a, a^(-1), b, b^(-1)}^(F_2)` (each site
     points to one neighbour; if `x(g) = c` then `x(gc) ≠ c^(-1)`, and if `x(g) ≠ c` then `x(gc) = c^(-1)`) is nonempty
     (point towards a fixed end), and the radius-0 rule "send `g` to the first two of the three non-parent neighbours"
     is collision-free into `T = M = Y` with `m = 2`. Consistently, `Y` has no invariant probability.
   - *Unimodularity.* On the end-fixing tree calibration (`end-fixing-tree-symmetries-carry-strict-automata`) the
     children map is a collision-free equivariant 2-to-1 compression; step 1 fails there with the modular factor 2.
   - *Continuity versus measurability.* Item 1 holds for Borel routings, so a Borel (measurable) paradox does not help
     either. What could survive is only a non-measurable phenomenon, such as a Baire-category paradox on a
     Bernoulli-null comeager set; no local rule realizes it on a set that a full-support invariant measure charges.

## What dies, and the gate

- **Killed class.** Every design for the ascent `k ∈ NS ⇒ k+1 ∈ NS` (and every strict-automaton construction) whose
  room is produced by a site-injective, configuration-dependent paradoxical transport read by a local rule from the
  input shift, from `τ`'s image, or from any automaton image. The invariant is the indegree expectation under the
  pushforward of Bernoulli measure; the step where every member dies is the double count `E N = m μ(M)` at the
  identity site. This is the precise form of item 8 of Section 5 of
  `notes/gottschalk-surjunctivity-conjecture-frontier-swarm-2026-09-16.md` ("dies at overlaps"): overlaps carry
  collision mass at least `(m-1) μ(M)` under every invariant `μ`.
- **Budget form.** For non-paradoxical targets, a collision-free routing needs `m μ(M) <= μ(T)` for *every*
  invariant `μ`, including point masses on periodic orbits. For the Garden of Eden marker `11` of
  `τ(x)(g) = x(g) ∧ ¬x(ga)`, the constant configuration `1` already breaks `2 μ(M) <= μ(G) = 1`.
- **Gate.** A surviving design must either
  (a) patch a defect set of Bernoulli density `>= (m-1) ν(M)` by a non-transport mechanism, or
  (b) create room by *site mixing*: output sites combining several input values (Ornstein–Weiss type), so that the
  room is informational rather than a site count. Item 1 does not see such room; it is what
  `every-injective-ca-preserves-uniform-bernoulli-measure` and the Rokhlin-entropy holes measure.

## Computation

`experiments/paradoxical-transport-2026-09-17/marker_routing_sat.py` encodes lane (d)'s first step as SAT per radius on
`F_2` (exact: all constraints are local). With `τ(x)(g) = x(g) ∧ ¬x(ga)` (Garden of Eden pattern `11` on `{1, a}`),
markers `M = [11]`, `m = 2`, targets in markers:

| rule window | marker patterns | vars | clauses | result |
|---|---|---|---|---|
| `a`-line radius 1..6 | 2 .. 2048 | up to 40778 | up to 431360 | UNSAT at every radius |
| ball `B_1` | 8 | 26 | 84 | UNSAT |
| ball `B_2` (17 sites) | 32768 | 213914 | 3457024 | UNSAT (7 s) |

Controls: `m = 1` into markers SAT (identity); markers `10`, targets any site SAT, and the solver's rule is checked
collision-free on random configurations (budget `sup 2μ(M) = 1`); markers `11`, targets any site UNSAT (constant
configuration); end-pointer SFT, `m = 2`, SAT, with the explicit rule verified on random end-pointer configurations.
