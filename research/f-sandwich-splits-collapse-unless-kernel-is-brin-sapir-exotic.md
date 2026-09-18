---
rg: 2
id: f-sandwich-splits-collapse-unless-kernel-is-brin-sapir-exotic
kind: claim
title: "Every twisted-embedding or co-amenable-induction split of amenability of F has a conjunct equivalent to amenability of F, unless its kernel is F-free and not elementary amenable; such a kernel refutes Brin–Sapir and makes F sofic"
distinct_from:
  f-functor-cocycles-need-an-exotic-recurrent-action: that collapses functor cocycles when a normal subgroup of F acts trivially, and asks for recurrent F-sets; this collapses every datum, faithful or not and recurrent or not, by the Brin–Sapir type of its kernel.
  thompson-f-amenable-iff-dyadic-action-extensively-amenable: that is one datum (the breakpoint cocycle, trivial kernel) falling under item 3; this is the trichotomy for all data.
  thompson-f-interval-stabilizer-cosets-separate-only-if-amenable: that proves the implication (amenable co-amenable subgroup gives amenability of F) used here; this classifies which splits built on it are not reformulations.
  thompson-f-mean-free-actions-dense-configurations-or-unconfined: that splits mean-free amenable actions into shapes (I) and (II); this shows an F-free co-amenable subgroup gives a shape (II) witness.
---

**ESTABLISHED.** Write `A` for "`F` is amenable", `EA(X)` for extensive amenability of an action
(JMBMdlS Definition 1.1), and `Coam(K)` for "`F/K` carries an `F`-invariant mean".

**Sandwich data.**
- **(T1) Twisted embedding.** An `F`-set `X`, a functor `𝔉 : I → Amen` from finite sets with injections
  to amenable groups, and a cocycle `c : F → 𝔉(X)` with `c_{gh} = c_g · g(c_h)`. The kernel is
  `K = {g : c_g = 1}`, the action conjunct is `P = EA(X)`.
- **(T2) Co-amenable induction.** A subgroup `K ≤ F`, with action conjunct `P = Coam(K)`.

The split is `A ⇐ P ∧ Amen(K)`.

**Statement.** For every datum of type (T1) or (T2):

1. **Sandwich.** `A ⟺ P ∧ Amen(K)`.
2. **Kernel containing F.** If `K` has a subgroup isomorphic to `F`, then `Amen(K) ⟺ A`.
3. **Amenable kernel.** If `K` is amenable, in particular elementary amenable, then `P ⟺ A`.
4. **Escape shape.** A datum in which neither conjunct is equivalent to `A` by items 2–3 has `K`
   *Brin–Sapir exotic*: no subgroup isomorphic to `F`, and not elementary amenable. So such a datum
   refutes `every-subgroup-of-thompson-f-is-ea-or-contains-f` and proves
   `some-subgroup-of-thompson-f-is-neither-ea-nor-contains-f`. Under the Brin–Sapir conjecture every
   datum collapses.
5. **F-free co-amenable subgroups are mean-free.** If `K ≤ F` has no subgroup isomorphic to `F` and `m`
   is an invariant mean on `F/K`, then `m(Fix(g)) = 0` for every `g ≠ e`. Consequently:
   - `K` is not confined in `F`;
   - `F` admits a mean-free amenable action of shape (II) of
     `thompson-f-mean-free-actions-dense-configurations-or-unconfined`;
   - `F` is sofic.

**Invariant and where every member dies.** The invariant is the Brin–Sapir type of the kernel: contains
`F`, amenable, or exotic. The approach dies at the kernel step (item 2) or at the action step (item 3).

Examples:
- the breakpoint cocycle on `D` has `K = 1`, so it falls under item 3;
- Jones' subgroup `\vec F ≅ F_3` contains `F`, so it falls under item 2;
- interval stabilizers `F_Z` contain `F`, so they fall under item 2;
- every recurrent orbit in a host has stabilizer meeting `F` in a copy of `F`
  (`thompson-f-recurrent-orbits-have-stabilizers-containing-f`), so it falls under item 2.

**What survives.** A non-collapsing split needs a Brin–Sapir counterexample `K`. In case (T2) it also
needs a co-amenable, unconfined `K` whose coset mean is mean-free, which already proves `F` sofic. Neither
kind of object is known. The surviving decomposition is the route
`thompson-f-amenable-via-brin-sapir-exotic-co-amenable-subgroup`.

Proof route: `thompson-f-sandwich-splits-collapse-proof`.
