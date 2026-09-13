---
rg: 2
id: fg-group-qi-to-simply-connected-geodesic-space-is-fp-proof
kind: route
title: Fill coarse loops by fine triangulations of discs in X and project back to G
target: fg-group-qi-to-simply-connected-geodesic-space-is-fp
requires: []
---

**Setup.**
- S is a finite symmetric generating set and d is the word metric.
- R_rho(G) is the Rips complex: its simplices are the finite sets of
  diameter ≤ rho.
- f: G → X satisfies d(x,y)/lambda − c ≤ d_X(f x, f y) ≤ lambda d(x,y) + c,
  and every point of X lies within C of f(G).

**Step 1 (coarse filling).** Every edge loop g_0, …, g_m = g_0 of the Cayley
graph (d(g_i, g_{i+1}) ≤ 1) is null-homotopic in R_rho(G), where
rho = max(1, rho_1, 2 rho_2) with rho_1 = lambda(1 + 2C + c) and
rho_2 = lambda(lambda + 2c + C).

1. Put p_i = f(g_i). Then d_X(p_i, p_{i+1}) ≤ lambda + c. Joining consecutive
   points by geodesic segments gives a loop gamma: S^1 → X.
2. X is simply connected, so gamma extends to H: D^2 → X. H is uniformly
   continuous, so there is a triangulation K of D^2 with |H(v) − H(w)| < 1
   along every edge vw of K. We may take the boundary vertices of K to
   include points theta_i with H(theta_i) = p_i.
3. For each vertex v of K choose phi(v) ∈ G with d_X(f phi(v), H v) ≤ C, and
   put phi(theta_i) = g_i. Along an edge vw of K,
   d_X(f phi v, f phi w) ≤ 1 + 2C, so d(phi v, phi w) ≤ rho_1. Hence phi is a
   simplicial map K → R_{rho_1}(G), and it fills the boundary edge loop
   phi(∂K).
4. The boundary vertices between theta_i and theta_{i+1} map under H into
   the geodesic from p_i to p_{i+1}, so they lie within lambda + c + C of
   f(g_i). Their phi-values lie within rho_2 of g_i. So they span, together
   with g_i and g_{i+1}, a simplex of R_{2 rho_2}(G). Inside that simplex the
   boundary arc of phi(∂K) is homotopic rel endpoints to the edge
   [g_i, g_{i+1}].
5. So the edge loop bounds in R_rho(G).

**Step 2 (finite presentation).**
1. For every h with |h| ≤ rho fix a word w_h representing h, with w_s = s for
   s ∈ S and w_e empty. Let 𝓡 be the finite set of words w_y w_{y^{-1}z}
   w_z^{-1} for 2-simplices {e, y, z} of R_rho(G).
2. Map each edge [x, xh] of R_rho(G) to the Cayley-graph path from x
   labelled w_h. Each 2-simplex {x, xy, xz} then bounds a translate of a
   relator in 𝓡.
3. Let u be a word with u = 1 in G. Its edge loop bounds a simplicial disc in
   R_rho(G) (Step 1, plus simplicial approximation). Reading the disc
   triangle by triangle writes u in the free group F(S) as a product of
   conjugates of elements of 𝓡.
4. Hence G = ⟨S | 𝓡⟩, which is a finite presentation. ∎
