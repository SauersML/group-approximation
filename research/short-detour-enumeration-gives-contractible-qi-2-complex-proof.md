---
rg: 2
id: short-detour-enumeration-gives-contractible-qi-2-complex-proof
kind: route
title: Add one vertex at a time and kill each extra edge by a polygon with a free face
target: short-detour-enumeration-gives-contractible-qi-2-complex
requires: []
---

**Construction.** Let X_0 = {g_0}. Given a finite 2-complex X_k with
1-skeleton Γ[A_k], let v = g_{k+1} and let e_1, …, e_m be the Γ-edges from v
to A_k, with endpoints u_1, …, u_m. The first bullet of the definition gives
m ≥ 1. Every edge of Γ[A_{k+1}] not in Γ[A_k] is one of these.

For i ≥ 2 choose a path p_i in Γ[A_k] from u_1 to u_i of length ≤ L. It is
constant if u_i = u_1 (parallel edges). Attach a 2-cell c_i along the closed
edge path e_1^{-1} · p_i · e_i, a polygon with ≤ L + 2 sides:
X_{k+1} = X_k ∪ {v} ∪ e_1 ∪ … ∪ e_m ∪ c_2 ∪ … ∪ c_m.
Put X = ∪_k X_k. Then X^(1) = ∪ Γ[A_k] = Γ.

**Contractible.**
1. In X_{k+1}, the edge e_i (i ≥ 2) lies on exactly one cell, c_i, and
   occurs once in its boundary. So (c_i, e_i) is an elementary collapse:
   D^2 deformation retracts onto the complement of the boundary arc mapped
   onto e_i.
2. After collapsing c_2, …, c_m, the vertex v is a free face of e_1, so
   X_{k+1} collapses to X_k. By induction each X_k is contractible.
3. Spheres are compact, so every map S^j → X factors through some X_k.
   Hence π_j(X) = 0 for all j, and X is contractible by Whitehead's theorem.

**Locally finite.**
1. A cell created when v is added has boundary within distance (L + 2)/2 of
   v.
2. So a vertex w lies on cells created by the finitely many v with
   d(v, w) ≤ (L + 2)/2, and each such v creates at most |S| cells.

**Metric.**
1. Give edges length 1 and each 2-cell the metric of a regular Euclidean
   polygon with sides of length 1. X is then a locally finite polyhedral
   complex with finitely many shapes, so it is a complete geodesic space
   (Bridson–Haefliger, Theorem I.7.19). Being locally finite, it is proper.
2. On vertices, d_X ≤ d_Γ. A path segment crossing a polygon can be replaced
   by a boundary arc at most kappa(L) times longer, so d_Γ ≤ kappa(L) d_X.
3. Every point of X lies within (L + 2)/2 of a vertex.
4. So G → X, g ↦ g, is a quasi-isometry. ∎
