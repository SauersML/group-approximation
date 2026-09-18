---
rg: 2
id: jndls-recurrent-groupoid-extension-theorem
kind: claim
title: "Import: the Juschenko–Nekrashevych–de la Salle germ-groupoid criterion (Theorem 3.1 of arXiv:1305.2637) and its definitions of germs, isotropy groups and topological full groups"
distinct_from:
  thompson-f-recurrent-orbits-have-stabilizers-containing-f: that proves a theorem about stabilizers of recurrent orbits; this only imports the JNdlS statement, whose amenability inputs are a full group [[H]] and germ groups, not stabilizers.
  juschenko-zheng-liouville-actions: that imports Liouville actions from a different paper.
---

**ESTABLISHED by citation.** K. Juschenko, V. Nekrashevych, M. de la Salle, *Extensions of
amenable groups by recurrent groupoids*, arXiv:1305.2637v2 (24 May 2013), §3.1–3.2. Verbatim from
the arXiv PDF, read 2026-09-18:

> Let G be a group acting faithfully by homeomorphisms on a topological space X. A germ of the
> action is an equivalence class of pairs (g,x) ∈ G×X, where two germs (g1,x1) and (g2,x2) are
> equal if and only if x1 = x2, and there exists a neighborhood U of x1 such that g1|U = g2|U. The
> set of all germs of the action of G on X is a groupoid. Denote by o(g,x) = x and t(g,x) = g(x)
> the origin and target of the germ. A composition (g1,x1)(g2,x2) is defined if g2(x2) = x1, and
> then it is equal to (g1g2,x2). The inverse of a germ (g,x) is the germ (g,x)^{−1} = (g^{−1},g(x)).

> For a given groupoid G of germs of an action on X, and for x ∈ X, the isotropy group, or group
> of germs G_x is the group of all germs γ ∈ G such that o(γ) = t(γ) = x. If G is the groupoid of
> germs of the action of G on X, then the isotropy group G_x is the quotient of the stabilizer G_x
> of x by the subgroup of elements of G that act trivially on a neighborhood of x.

> The topological full group of a groupoid of germs G, denoted [[G]] is the set of all
> homeomorphisms F : X −→ X such that all germs of F belong to G. The (orbital) Schreier graph
> Γ(x,G) is the Schreier graph of the action of G on the G-orbit of x.

> Theorem 3.1. Let G be a finitely generated group of homeomorphisms of a topological space X,
> and G be its groupoid of germs. Let H be a groupoid of germs of homeomorphisms of X. Suppose that
> the following conditions hold.
> (1) The group [[H]] is amenable.
> (2) For every generator g of G the set of points x ∈ X such that (g,x) ∉ H is finite. We say
> that x ∈ X is singular if there exists g ∈ G such that (g,x) ∉ H.
> (3) For every singular point x ∈ X the orbital Schreier graph Γ(x,G) is recurrent.
> (4) The isotropy groups G_x are amenable.
> Then the group G is amenable.

**Reading notes.**
- In (4) the groupoid is the groupoid of germs of `G`, so `G_x` is the germ group of the stabilizer
  of `x`, written `𝒢_x` downstream to separate it from the stabilizer `G_x`.
- The text calls `[[H]]` a group. So the identity homeomorphism lies in `[[H]]`, and every unit germ
  `(1,x)` lies in `H`.
- Whether (4) quantifies over all `x` or only over singular `x` does not matter downstream. The
  downstream use only needs it at points in orbits of singular points, and germ groups along one
  orbit are conjugate.

**Scope.** Citation import only. Used by `thompson-f-recurrent-germ-criteria-proof`.
