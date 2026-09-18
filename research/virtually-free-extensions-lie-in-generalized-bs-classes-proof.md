---
rg: 2
id: virtually-free-extensions-lie-in-generalized-bs-classes-proof
kind: route
title: Pull back the Bass–Serre tree of the virtually free quotient
target: virtually-free-extensions-lie-in-generalized-bs-classes
requires: []
---

1. **Quotient tree.** A finitely generated virtually free group `Q` is the fundamental group of a
   finite graph of finite groups (Karrass–Pietrowski–Solitar; textbook, not re-read). After one
   barycentric subdivision, `Q` acts on the Bass–Serre tree `T` without inversions, with finitely
   many orbits of vertices and edges and finite stabilizers `Q_v`, `Q_e`. If `Q` is finite, take
   `T` a point.
2. **Pull back.** Let `G` act on `T` through `π: G -> Q`. This action is without inversions and
   has the same finitely many orbits. Its stabilizers are `G_v = π^-1(Q_v)` and `G_e = π^-1(Q_e)`.
3. **Commensurability.** `N = ker π ≤ G_e ≤ G_v`, with `[G_v : N] = |Q_v|` and `[G_e : N] = |Q_e|`
   finite. So every vertex and edge group contains `N` with finite index; in particular it is
   abstractly commensurable with `N`, and `[G_v : G_e] = [Q_v : Q_e]` is finite.
4. **Structure theorem.** By the Bass–Serre structure theorem (Serre, *Trees*, I.5.4; standard, not
   re-read), `G` is the fundamental group of the finite quotient graph of groups `G\T` with these
   vertex and edge groups. Hence `G ∈ BS_N`.

`N` infinite is only used so that "commensurable with `N`" is the intended nontrivial condition;
the argument does not use faithfulness of any action, and `G` need not split.
