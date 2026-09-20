---
rg: 2
id: thompson-t-escapes-quotient-free-mf-permanence-closure
kind: claim
title: "Thompson's T maps trivially to every group built from T-bar, amenable, residually finite, linear and hyperbolic groups by subgroups, arbitrary extensions, arbitrary graphs of groups, colimits, products, ultraproducts and local embeddings; so descent from T-bar to T, and any MF proof for T, must pass through the central quotient"
distinct_from:
  sofic-permanence-closure-omits-simple-fa-nonsofic-groups: that needs a group Sigma that is not sofic, so that the sofic groups lie in D_Sigma; T is not known to be nonsofic, so that theorem says nothing about T. Here the base is replaced by explicit classes that provably avoid T, T-bar among them, FA for T is proved from the Lochak--Schneps orders, and the conclusion is read in the MF setting (every homomorphism from T into the closure is trivial).
  lifted-thompson-t-escapes-haagerup-permanence-closure: that keeps T-bar out of a Haagerup closure whose extension step needs an amenable quotient and whose graphs of groups need finite edge groups; here the invariant is "contains T", which survives arbitrary extensions (including central ones), arbitrary edge groups, unrestricted products and ultraproducts, and T-bar is put in the base.
  thompson-f-in-permanence-closure-only-via-base-copy: that is the closure theorem for F, which has no FA and no simplicity; T has both, so no relative tree lemma is needed.
  lifted-thompson-t-centre-has-commutant-eigencorners: that is the open eigencorner claim; this shows that the central fibre it asks for cannot be bypassed by group-level permanence.
  thompson-t-has-full-mf-radical: that is the open claim that every corona representation of T is trivial; this only shows that no corona representation of T factors through the closure other than the trivial one, so no permanence argument can refute it.
---

**ESTABLISHED** by `thompson-t-escapes-quotient-free-mf-permanence-closure-proof`.
The proof is elementary once its inputs are granted. It has not been independently reviewed.

## Setting

- `T` is Thompson's group, `T = <alpha, beta>` with `alpha^4 = beta^3 = (beta alpha)^5 = 1`
  (`thompson-t-lochak-schneps-presentation`).
- `T̄` is its lift to `R`, with centre `<z>`, `z(x) = x + 1`
  (`lifted-thompson-t-perfect-centre-cubically-elliptic`).
- `D_T` is the class of groups that have no subgroup isomorphic to `T`.

## Statement

1. **FA.** Every action of `T` on a tree without inversions fixes a vertex.
2. **Closure.** `D_T` is closed under the following operations:
   - subgroups;
   - extensions `1 -> N -> E -> E/N -> 1` with `N` and `E/N` in `D_T`, with no condition
     on the action or the cocycle, so central extensions are included;
   - fundamental groups of graphs of groups whose vertex groups lie in `D_T`, with any edge
     groups and any edge maps (free products, amalgams, HNN extensions);
   - directed colimits with arbitrary structure maps;
   - unrestricted direct products and ultraproducts of families in `D_T`;
   - local embeddability: if every finite subset of `G` embeds partially into some member of
     `D_T`, then `G` is in `D_T`. The same holds for limits in the space of marked groups.
3. **Base.** `D_T` contains `T̄`, every finite group, every amenable group, every residually
   finite group, every linear group over any field and every word-hyperbolic group. By item 2
   it also contains every LEF and every LEA group.
4. **No factorization.** Let `𝒞` be the smallest class containing the base of item 3 and closed
   under the operations of item 2. Then `𝒞 ⊆ D_T`, and every homomorphism from `T` to a group
   in `𝒞` is trivial. The same holds for `V` and every `nV` (they contain `T`): they are not in
   `𝒞`.

## What this changes

- **Descent needs the central quotient.** Suppose a proof of "`T̄` MF implies `T` MF" (the
  descent leaf of the w21 twist-set route) or of the negation of `thompson-t-has-full-mf-radical`
  produced a corona representation of `T` as a composite `T -> G -> U(Q)` with `G` built by
  the operations of item 2 from `T̄` and the base classes. By item 4 that composite is
  trivial. So the only step not covered by item 2 is a quotient. By item 1 of
  `lifted-thompson-t-escapes-haagerup-permanence-closure`, the nontrivial quotients of `T̄` are
  the central quotients `T̄/<z^j>`. In corona terms, that step is exactly a corona
  representation of `T̄` in which `z` becomes a scalar or of finite order: a central fibre.
  This is the object of `lifted-thompson-t-centre-has-commutant-eigencorners`. Nothing
  group-theoretic replaces it.
- **The step where every member dies.** For each operation of item 2, `T` either lands in an
  input (subgroups, extensions via simplicity, graphs of groups via FA, colimits and local
  embeddings via finite presentation plus simplicity, products via simplicity) or the input
  already contains `T`. The invariant is "contains a copy of `T`".
- **Future permanence theorems do not help.** Extensions with arbitrary quotients, amalgams
  over arbitrary subgroups and ultraproducts are not known to preserve MF. Item 2 shows that
  proving such permanence theorems would still not reach `T`, `V` or `nV` from these bases.
- **Scope.** This does not say `T` is not MF, and it does not touch the `C*`-algebraic
  constructions (tensor products, corners) applied to a given representation. It is a statement
  about proof architecture at the level of groups.
