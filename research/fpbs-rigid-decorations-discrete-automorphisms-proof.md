---
rg: 2
id: fpbs-rigid-decorations-discrete-automorphisms-proof
kind: route
title: Rigid decoration shapes force fibre-preserving automorphisms to be group elements, and triangle counts force fibre preservation
target: fpbs-tree-projected-rigid-decorations-discrete-automorphisms
requires: []
artifacts:
  - research/artifacts/fpbs/scripts/letter_exchange_rigid_check.py
---

Notation as in the claim. `T = Cay(F_n,B)`. For an oriented edge `epsilon` of `T`
let `D(epsilon)` be the set of height changes of `X`-edges over it: `D_s` along a
label `s`, `-D_s` against it.

1. **Induced tree automorphism and affine fibre maps.** Let `Psi in Aut(X)` map
   vertical lines onto vertical lines, and let `phi` be the induced bijection of
   `F_n`. Two lines are joined by an `X`-edge iff their projections are adjacent in
   `T`, so `phi in Aut(T)`. The map on a line is an automorphism of the line graph
   `Cay(Z,{±1})`, so `Psi(g,m) = (phi g, eps_g m + h(g))` with `eps_g in {±1}`. If
   `g, g'` are adjacent, the image of `(g,m)–(g',m+d)` has height change
   `eps_(g') (m+d) + h(g') - eps_g m - h(g)`, which must lie in a finite set for all
   `m`; so `eps_(g') = eps_g`, and `eps` is constant.
2. **Shape equation.** Fix `epsilon = (g -> g')` and `m`. `Psi` maps the `|D(epsilon)|`
   edges at `(g,m)` over `epsilon` injectively to edges at `Psi(g,m)` over
   `phi epsilon`, and `Psi^(-1)` maps back. So
   `D(phi epsilon) = eps D(epsilon) + (h(g') - h(g))`.
3. **Rigidity.** The oriented shapes are the `2n` sets `D_s`, `-D_s`.
   * If `eps = +1`, `D(phi epsilon)` is a translate of `D(epsilon)`. By rigidity the
     two have the same label and orientation, and the translation is 0, since a
     finite nonempty set is invariant under no nonzero translation.
   * If `eps = -1`, `D(phi epsilon)` is a translate of `-D(epsilon)`, the shape of the
     reversed label. By rigidity `phi epsilon` has the same label as `epsilon` with
     the opposite orientation, and again the translation is 0.

   So `h` is constant. If `eps = +1`, `phi` keeps every label and orientation. A tree
   automorphism of `Cay(F_n,B)` keeping labels and orientations is determined by the
   image of `1`, so `phi(g) = gamma g` with `gamma = phi(1)`. If `eps = -1`, `phi o theta`
   keeps labels and orientations, so `phi = L_gamma o theta`. Hence
   `Psi = (gamma, k)` or `Psi = (gamma, k) o alpha`, with `(gamma,k) in Gamma` acting on
   the left.
4. **`alpha` is an automorphism.** `alpha` is a group automorphism of `Gamma` with
   `alpha(s,d) = (s^(-1),-d)`, so `alpha(S) = S^(-1) = S` and it preserves the Cayley
   graph.
5. **Discrete and unimodular.** `Gamma` acts freely, so vertex stabilizers in
   `Gamma ⋊ <alpha>` have order at most 2. Every closed subgroup `H` is discrete. For
   `y = h x` in one orbit, `H_y = h H_x h^(-1)`, so
   `|Stab_x y| = |H_x| / |H_x ∩ H_y| = |H_y| / |H_x ∩ H_y| = |Stab_y x|`: `H` is
   unimodular in the sense of Section 1 of arXiv:1711.02590v3.
6. **The example `S_rig`.** `D_a = {0,1,3}` has gaps `(1,2)`, `-D_a` gaps `(2,1)`,
   `D_b = {0,1,4}` gaps `(1,3)`, `-D_b` gaps `(3,1)`. These are pairwise distinct, so
   the decorations are rigid.
   * *No triangle meets three lines*, since `T` has no triangles, and *none lies in one
     line*, since `m` and `m+2` are not adjacent.
   * *Vertical edge* `(g,m)–(g,m+1)`: a third vertex `(g',k)` on an adjacent line over
     an oriented edge with shape `E` needs `k-m-1` and `k-m` in `E`, one triangle per
     consecutive pair in `E`. `D_a, -D_a, D_b, -D_b` each have exactly one consecutive
     pair, so the edge lies in 4 triangles.
   * *Horizontal edge* `(g,m)–(g',m+d)` over shape `E`, `d in E`: the third vertex is
     `(g,m±1)` or `(g',m+d±1)`, and each of `d-1, d+1` that lies in `E` gives two
     triangles. For `D_a` the heights `0, 1, 3` give `2, 2, 0` triangles; for `D_b`
     the heights `0, 1, 4` give `2, 2, 0`. Edges against a label give the same counts.

   So an automorphism of `X_rig` maps vertical edges to vertical edges, hence vertical
   lines onto vertical lines, and items 1–5 give
   `Aut(X_rig) = Gamma ⋊ <alpha>`.

**Check.** `research/artifacts/fpbs/scripts/letter_exchange_rigid_check.py`, run on
MSI on 2026-09-12, reports:
* triangle census on a core ball of `X_rig`: 90 vertical edge-ends with 4 triangles,
  360 horizontal edge-ends with 2 and 180 with 0;
* shape-preserving type maps: only the identity for `eps = +1`, and only
  `a <-> a^(-1)`, `b <-> b^(-1)` for `eps = -1`;
* every exchange lift for `D_a = {0,1,3}`, `D_b = {0,1,4}` breaks edges for every
  shift in `[-6,6]`, in both the translate and the reflected mode.
