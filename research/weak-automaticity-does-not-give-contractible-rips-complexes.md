---
rg: 2
id: weak-automaticity-does-not-give-contractible-rips-complexes
kind: claim
title: Autostackability with type F_infinity and a quadratic Dehn function, or asynchronous combability, does not give a contractible Rips complex
distinct_from:
  automatic-groups-have-contractible-rips-complexes: that is the open claim for automatic groups; this is an established obstruction showing that every weakening of automaticity satisfied by F or T is too weak for it
  thompson-f-has-no-contractible-rips-complex: that is the fact about F alone; this pairs it with F's autostacking, and T's asynchronous combing and unbounded 2-torsion, to rule out a whole class of proof strategies
  contracting-combings-give-contractible-rips-complexes: that is Alonso's positive theorem for contracting combings; this is a negative result for asynchronous and prefix-rewriting structures
---

**ESTABLISHED** (route `weak-automaticity-no-contractible-rips-proof`).

1. Thompson's group `F` has all of the following, and for no finite generating set
   `S` and no scale `d` is `R_d(F,S)` contractible:
   - it is autostackable, with a bounded regular convergent prefix-rewriting system;
   - it is of type `F_∞`;
   - it has quadratic Dehn function.
2. Thompson's group `T` is asynchronously combable, and no `R_d(T,S)` is
   contractible. Two independent invariants rule it out: `T` contains `F`, and it
   contains cyclic subgroups `Z/2^k` for every `k`.

**Obstruction to a class of approaches** (for
`automatic-groups-have-contractible-rips-complexes`). Consider any argument that
concludes "some `R_d(G,S)` is contractible" using only the following hypotheses
on `G`:

- autostackability, which covers stacking or rewriting flows, prefix-closed regular
  normal forms and asynchronously automatic structures on prefix-closed languages;
- type `F_∞` or `FP_∞`;
- a quadratic Dehn function or linear isodiametric function;
- solvability of the word problem;
- an asynchronous fellow-traveller combing.

Every such argument is refuted by `F` or `T`.

The invariant is `contractible-rips-conjugates-p-subgroups-into-balls`. A
contractible `R_d(G,S)` bounds the cohomological dimension of every torsion-free
subgroup by `|B_S(d)| - 1`. It also puts every finite `p`-subgroup, up to
conjugacy, inside `B_S(d)`.

The rigorous content is items 1 and 2: each listed hypothesis, alone or in the
combinations above, fails to imply contractibility. The next paragraph is a reading
of where the natural arguments break, not a theorem.

Every member dies at the same step: the one that converts the structure into a
deformation of a finite subcomplex of `R_d` **inside `R_d` itself**.

- Flow functions and asynchronous fellow travelling control displacement only up
  to a reparametrization, or a bounded but scale-independent flow length.
- So they give filling at a larger scale `s(d) > d`: coarse contractibility and
  finiteness properties. They never give filling at the fixed scale `d`.
- `F` and `T` show that filling at a larger scale is consistent with
  `cd = ∞` and with unbounded `p`-torsion.

**Consequence.** A proof of the target must use the **synchronous** fellow traveller
property, or an Alonso-bounded (synchronous) combing, at the fixed-scale step. This
is the one input of automaticity not known for `F` or `T`. The recorded attempt that
dies at the change of scale `P_d → P_(Kd)` is the synchronous survivor, and this
claim shows that nothing weaker can replace it.
