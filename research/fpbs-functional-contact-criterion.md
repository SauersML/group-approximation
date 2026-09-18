---
rg: 2
id: fpbs-functional-contact-criterion
kind: claim
title: A functional graphing whose components are joined by infinite Cayley contacts, in an action weakly contained in Bernoulli, forces fixed price one
distinct_from:
  fpbs-infinite-contact-zero-relative-cost: that is the relative-cost repair lemma for an arbitrary subrelation with a finite-cost graphing; this specializes it to the graph of one Borel self-map (cost at most one) and adds the weak-containment transfer from the witnessing action to the Bernoulli shift, so the output is fixed price one rather than a cost bound on one action.
  fpbs-sparse-spine-cost-bound: that needs one FIID connected infinite vertex set of small density and pays its internal edges; here nothing is thinned, the whole space is covered by the components of one self-map of cost at most one, the witnessing action need only lie in the weak-containment closure of Bernoulli, and connection is by infinite contacts rather than by internal connectivity.
  fpbs-hp-condensation-bernoulli-exit: that is a dichotomy for the Hutchcroft--Pete percolation recursion inside W_b; this is a criterion for arbitrary functional graphings in any action weakly contained in Bernoulli, with no percolation or frequency hypothesis.
  fpbs-malnormal-subgroup-relations-finite-contacts: that obstructs infinite-contact repair from subgroup orbit relations; the subrelations here are components of a Borel self-map, which need not be orbit relations of any subgroup.
---

**OPEN (written deduction proposed in `fpbs-functional-contact-criterion-proof`; not yet fully refereed).**

**Setting.**
- `Gamma` is a finitely generated infinite group, `S` a finite symmetric generating set not containing `e`, and
  `b_Gamma` the Bernoulli shift on `[0,1]^Gamma`.
- For a free p.m.p. action `a` of `Gamma` on `(X,mu)` with orbit relation `R_a`, the Cayley graphing is
  `H_a = {(x, s.x) : x in X, s in S}`.
- A *functional graphing* is the graph `F_f = {(x, f(x)) : f(x) != x}` of a Borel map `f : X -> X` with
  `(x, f(x))` in `R_a` for a.e. `x`. Its *components* are the classes of the subrelation `S_f` of `R_a` generated
  by `F_f`.
- The *contact graph* of `f` in an orbit has the `S_f`-classes of that orbit as vertices, and joins two classes when
  infinitely many `H_a`-edges run between them. Say `f` is *contact-connected* if the contact graph is connected in
  almost every orbit.

**Theorem.** If some free p.m.p. action `a` with `a ≺ b_Gamma` carries a contact-connected functional graphing, then
`Gamma` has fixed price one: every free p.m.p. action of `Gamma` has cost exactly one.

**Contrapositive, as an obstruction.** If `Gamma` has a free action of cost above one (for example `F_r` with `r >= 2`,
or any group with positive first `l^2`-Betti number), then no Borel self-map in any action weakly contained in
`b_Gamma` is contact-connected. For descent maps that move each point to a Cayley neighbour, this is visible
directly in a tree: the components are subtrees, and two disjoint subtrees of a tree are joined by at most one edge.

**Calibration.**
- `Gamma = F_2 x Z = <u,v> x <z>`, `a = b_Gamma`, `f(x) = z.x`: the components are the `<z>`-orbits, and the
  coset `g<z>` meets `gu<z>` along the edges `g z^n -> g z^n u = g u z^n` for every `n`. So `f` is
  contact-connected and the theorem returns the known fixed price one of `F_2 x Z`.
- Two further candidates for `f` are the nucleus-descent map of an ideal Voronoi tessellation
  (`fpbs-ideal-voronoi-descent-limit-exists`) and a map along an invariant line field.

**Scope.** No necessity is claimed. Whether Bernoulli cost one forces a contact-connected functional graphing in
some action weakly contained in `b_Gamma` is open.

## Attempts

- **2026-09-17: written deduction `fpbs-functional-contact-criterion-proof`, held at OPEN.** Two of three referee
  lenses returned survives (Lusin--Novikov bounds the functional graphing by cost one, the imported infinite-contact
  lemma applies with `H_a` simple of cost `|S|/2`, and Kechris monotonicity is used in the correct direction before
  Abert--Weiss maximality; one lens noted the tree remark is only stated for free groups but is unused). The third
  referee vote was lost, so the claim is not promoted to ESTABLISHED until a full referee panel survives. The proof
  file is kept as the attempt.
