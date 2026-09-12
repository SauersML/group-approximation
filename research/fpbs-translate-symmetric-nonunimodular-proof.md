---
rg: 2
id: fpbs-translate-symmetric-nonunimodular-proof
kind: route
title: Lift tree automorphisms with height potentials and apply the nonunimodular theorem to lifted end stabilizers
target: fpbs-tree-projected-translate-symmetric-nonunimodular
requires:
  - fpbs-hyperbolic-and-nonunimodular-nonuniqueness
---

Notation as in the claim. `T` is the Cayley tree of `F_n` for `B`, `X = Cay(Gamma,S)`
with vertex set `F_n x Z`, and for an oriented tree edge `e = (g -> gs)`,
`s in B ∪ B^(-1)`, put `D(e) = D_s`.

1. **Translation cocycle.** From `c - D = D` we get `-D = D - c`, so
   `D_(s^(-1)) = -D_s` is again a translate of `D`. So every `D(e)` is a translate
   of `D`. For oriented edges `e, f` let `t(e,f)` be the unique integer with
   `D(f) = D(e) + t(e,f)`. It is unique because `D` is finite and nonempty.
   * *Additivity.* `t(e,f) + t(f,k) = t(e,k)`.
   * *Reversal.* `t(ē, f̄) = -t(e,f)`, since `D(ē) = -D(e)`.
2. **Height potential.** Fix `phi in Aut(T)`, with no label condition. Put
   `delta_phi(e) = t(e, phi e)` on oriented edges. By step 1,
   `delta_phi(ē) = -delta_phi(e)`, so `delta_phi` is an antisymmetric edge function.
   Since `T` is a tree it has a potential: `h_phi : F_n -> Z` with
   `h_phi(g') - h_phi(g) = delta_phi(g -> g')`, unique up to a constant.
3. **Lift.** `Psi_(phi,k)(g,n) = (phi(g), n + h_phi(g) + k)` is an automorphism of `X`.
   * *Vertical edges.* `(g,n)–(g,n+v)` with `v in V` maps to
     `(phi g, n+h+k)–(phi g, n+v+h+k)`.
   * *Horizontal edges.* An edge `(g,n)–(gs,n+d)`, `d in D(e)`, maps to a pair over
     the oriented edge `phi e`. Its height difference is
     `d + h_phi(gs) - h_phi(g) = d + t(e,phi e)`, which lies in `D(phi e)`. So the
     image is an edge of `X`.
   * *Bijectivity.* `Psi_(phi,k)` is bijective and its inverse is again a lift, so
     it is a graph automorphism.
4. **The subgroup.** Fix an end `xi` of `T` and let
   `G = {Psi_(phi,k) : phi in Aut(T)_xi, k in Z}`.
   * *Group.* `h_(phi psi) = h_psi + h_phi o psi + const`, so `G` is a group.
   * *Closed.* If `Psi_(phi_j,k_j) -> Psi` pointwise, then `phi_j -> phi` and
     `phi in Aut(T)_xi`, because end stabilizers are closed. The value of
     `h_(phi_j)` at each vertex is fixed by `phi_j` on a finite path, and `k_j` is
     eventually constant. So `Psi = Psi_(phi,k)`.
   * *Transitive.* `Aut(T)_xi` is vertex-transitive on `T`, and `k` shifts heights.
5. **Nonunimodular.** Let `p` be a vertex, `g` a neighbour of `p` that is not on
   the ray from `p` to `xi`, `e = (g -> p)`, `u = (g,0)` and `v = (p,0)`.
   * *`Stab_G(u)·v`.* If `Psi_(phi,k)` fixes `u`, then `phi` fixes `g` and `xi`,
     hence the ray from `g` to `xi`, hence `p`, and `phi e = e`. So the image of
     `v` is `(p, h_phi(p) - h_phi(g)) = (p, t(e,e)) = v`. Therefore
     `|Stab_G(u)·v| = 1`.
   * *`Stab_G(v)·u`.* If `Psi_(phi,k)` fixes `v`, the image of `u` is
     `(phi g, t((p->g),(p->phi g)))`. The height is determined by `phi(g)`, and
     `Aut(T)_(xi,p)` permutes the `2n-1` neighbours of `p` off the ray
     transitively. So `|Stab_G(v)·u| = 2n-1`.
   * *Conclusion.* For a closed transitive group, unimodularity is equivalent to
     `|Stab(u)·v| = |Stab(v)·u|` for all `u,v` (Trofimov; Benjamini–Lyons–Peres–Schramm).
     Here the ratio is `1/(2n-1)`, so `G` is nonunimodular.
6. **Nonuniqueness.** `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` item 2
   (Hutchcroft arXiv:1711.02590, for a closed quasi-transitive nonunimodular
   subgroup) gives `p_c < p_h <= p_u` on `X`.

**Scope.** `Gamma = F_n x Z` only. In a non-split or orientation-twisted
cyclic-by-free group some letters invert the fibre, and the compensation has to
be redone.
