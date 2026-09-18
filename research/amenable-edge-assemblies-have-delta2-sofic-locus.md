---
rg: 2
id: amenable-edge-assemblies-have-delta2-sofic-locus
kind: claim
title: Degenerate graph-of-groups assemblies over Noetherian amenable edges have a Delta-zero-two sofic locus, so they cannot make soficity Pi-zero-two hard
distinct_from:
  sofic-fp-hard-for-every-finite-difference-level: that is the lower bound realised by kill and collapse gadgets; this is the matching ceiling for the whole assembly calculus those gadgets live in, and it answers that node's open question whether a one-way propagator can be built from such gadgets.
  finite-graphs-of-amenable-groups-have-sigma1-locus: that is about amenability with amenable vertex groups and genuine edges; this is about soficity with arbitrary vertex groups and edge maps that need not be injective, where the locus reaches every finite difference level and the ceiling is Delta-zero-two rather than Sigma-zero-one.
  sofic-recognition-finite-presentations-is-pi2-complete: that is the open completeness statement; this is an obstruction that rules out one family of proofs of it and names what a proof must contain instead.
  genuine-hnn-switches-over-amenable-bases-are-sigma1: that treats genuine one-edge HNN extensions and amenability; this treats degenerate finite assemblies of any shape and soficity.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `amenable-edge-assemblies-delta2-sofic-locus-proof`.

## Setting

An *assembly* `A_e`, computed from `e`, is:
- a finite graph `Y_e` (loops and multiple edges allowed);
- a finite presentation `V_v` for each vertex `v`;
- for each edge `eps`, a finitely generated group `E_eps` and two word tuples that define homomorphisms
  `iota_(eps,o) : E_eps -> V_o(eps)` and `iota_(eps,t) : E_eps -> V_t(eps)`.

The edge maps are **not** assumed injective.  The output is the standard finite presentation

```text
P_e = < *_v V_v , tau_eps | tau_eps iota_(eps,o)(x) tau_eps^-1 = iota_(eps,t)(x)  (x a generator of E_eps),
                            tau_eps = 1 on a fixed maximal forest >.
```

The kill and collapse gadgets of [[sofic-fp-hard-for-every-finite-difference-level]], and their nests, are
assemblies with `E_eps = Z`.

An edge class `E` is *Noetherian and decidable* when:
- (N1) every group in it is amenable and satisfies max-n: every normal subgroup is the normal closure of a
  finite set;
- (N2) given `E` in the class and a finite `S ⊆ E`, the word problem of `E/<<S>>` is decidable, uniformly.

Examples: cyclic and finitely generated abelian groups (Smith normal form), polycyclic-by-finite groups
(Baumslag-Cannonito-Robinson-Segal 1991), and finitely generated metabelian groups (max-n by P. Hall 1954;
uniform word problem by Baumslag-Cannonito-Robinson 1994).

## Theorem

**(A) Normal form, for any amenable edge groups.**  Put `N_eps = ker(E_eps -> P_e)` and
`V*_v = V_v / <<iota_(eps,*)(N_eps) : eps incident to v>>`.  Then:
- `P_e` is the fundamental group of the **genuine** graph of groups with vertex groups `V*_v` and edge groups
  `E_eps/N_eps`;
- `V*_v` is the image of `V_v` in `P_e`;
- `P_e` is sofic iff every `V*_v` is sofic.

**(B) Oracle normalisation.**  If every `E_eps` lies in a Noetherian decidable class, a Turing machine with
oracle `0'` computes, from `e`, finite sets `S_eps` with `<<S_eps>> = N_eps`.  So it computes finite
presentations of all the `V*_v`.

**(C) Delta-zero-two ceiling.**  Suppose, in addition, hypothesis (V): soficity of
`V_v/<<iota_(eps,*)(S_eps)>>` is decidable from `0'`, uniformly in `e`, `v` and the finite sets `S_eps` with
`<<S_eps>> = N_eps`.  Then

```text
L = { e : P_e is sofic }  is  Delta^0_2.
```

Hence no computable family of such assemblies many-one reduces `INF`, or any other `Pi^0_2`-complete set, to
`SOFIC_fp`.

**(D) Bounded-change refinement.**  Suppose the edges are cyclic and tame: each `N_eps` is `1` or `E_eps`.
Suppose also that soficity of `V_v/<<iota(E_eps) : eps in K>>` is omega-c.e. with a computable change bound,
uniformly in `K`.  The approximation must be defined for every subset `K` of the edges, but it only needs the
correct limit when every edge in `K` really dies in `P_e`.  Then `L` is omega-c.e. with a computable change
bound.  So at the bounded-change level the difference-hierarchy lower bound of [[sofic-fp-hard-for-every-finite-difference-level]]
is sharp for this calculus.

## The exact step where the calculus dies

- A kill is recorded as a normal subgroup of an edge group.
- Normalisation only enlarges these normal subgroups.
- By max-n this stops after finitely many steps, and `0'` detects the stop, because "some element outside
  the current `<<S>>` dies" is a `Sigma^0_1` question once `<<S>>` has decidable membership.

A `Pi^0_2` event needs infinitely many independent kills, and a finite assembly over Noetherian amenable edges
can only record finitely many.  The "one-way propagator" asked for in the attempts on
[[sofic-recognition-finite-presentations-is-pi2-complete]] cannot be a finite amenable-edge assembly.
Finitely many Baumslag-Solitar, free-by-cyclic or machine-group vertices (with a `Delta^0_2` vertex table as in
(V)) joined along cyclic, abelian, polycyclic or metabelian edges never suffice.

## What a Pi-zero-two hardness proof must contain instead

At least one of the following:
1. **A non-amenable edge.**  Soficity permanence is lost; this is the Higman rope of
   [[sofic-safe-finite-presentation-compiler]].
2. **An amenable edge outside every Noetherian decidable class.**  The finitely presented solvable `A_p^2 A`
   machine groups of Kharlampovich-Myasnikov-Sapir are examples: their word problem is undecidable, so (N2)
   fails.  In such an edge the oracle cannot detect when normalisation has stopped, so the edge could in
   principle record an unbounded chain of kills.  This is the only amenable route left inside colimits.  The
   pumped machine groups behind [[residual-finiteness-of-finite-presentations-is-pi2-complete]] are of this
   kind.  The obstruction therefore points the one-way propagator at a machine group used as an
   **edge**, not as a vertex.
3. **Vertex groups whose normalised soficity table is not Delta-zero-two.**  The vertices then already
   carry the hardness, which is circular for a compiler.
4. **A construction that is not a finite graph-of-groups colimit**, for example the lamp modules of
   [[kazhdan-lamp-amplifier-for-machine-center]].

**Calibration.**
- The theorem does not contradict the known lower bounds.  The difference levels `D_n` and bounded omega-c.e.
  all lie inside `Delta^0_2`.
- The residual-finiteness hardness is not an assembly.
- The MF compiler rope `K_e *_(L_e) (L_e x Z)` has a non-amenable edge that also lacks max-n.
- The normal form in (A) holds for arbitrary edge groups.  Only its last clause, the soficity equivalence,
  uses amenability of the edges.
