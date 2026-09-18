---
rg: 2
id: hyperplane-extensions-into-davis-lattices-are-split
kind: claim
title: Automorphisms of a hyperplane carrier of X_{O_d} extend by a homomorphic section through the Coxeter retraction, so every torsion-free edge-transitive lattice on T' × T_d is a hyperplane sub-amalgam of a torsion-free lattice K_0 ⋊ Γ on T' × X_{O_d}; the extension is split, so the open gate for Kourovka 21.46 is irreducibility, not extension
requires:
  - kourovka-21-46-reduces-to-simple-amalgams-of-davis-lattices
---

**ESTABLISHED** (lane proof, elementary, not reviewed). This settles the gate EXT of the required
node. EXT itself turns out to be easy. What remains is an irreducibility gate, (IRR) below.

## Setting

`X = X_L` with `L = O_d` (`d >= 3`). Vertices of `X` are the elements of `W_L`, and an edge `(w, wE)` has
**type** `E ∈ V(L)`. For `g ∈ Aut(X)` and a vertex `x`, the local action `σ_g(x) ∈ Aut(L) = Sym(2d-1)`
records how `g` permutes the types of the edges at `x`.

Fix a vertex `D` of `L` and the hyperplane `H_0` dual to the edge `(1, D)`. Its carrier `C` is the
Davis complex of `st(D)`, i.e. `C = H_0 × [edge]`, whose vertices form `W_{st(D)} = ⟨D⟩ × W_{lk(D)}`.

## Statement

1. **Fields.**
   - Automorphisms of `X` correspond to pairs (image of the vertex `1`, a field `x ↦ σ_x ∈ Aut(L)`).
   - A field is admissible iff it is **compatible**: `σ_w` and `σ_{wE}` agree on `st(E)` for every edge `(w, wE)`.
2. **Commensurator.** `g ∈ Comm_{Aut X}(W_L)` iff `σ_g` is invariant under left translation by a
   finite-index subgroup of `W_L`.
3. **Canonical extension.** Let `r: W_L → W_{st(D)}` be the Coxeter retraction, which kills every
   generator outside `st(D)`.
   - For `h ∈ Aut(C) = Aut(H_0) × Z/2`, let `τ_h(y) ∈ Sym(D^c) ≅ Sym(lk(D))` be its local action on the
     edge colours of `H_0`.
   - Define `E(h)` by `E(h)(1) = h(1)` and the field `σ_x := (id_D, τ_h(y(r(x))))`, a permutation of
     `[2d-1] = D ⊔ D^c`. Here `y(c)` is the vertex of `H_0` at `c`.
   - Then `E: Aut(C) → Stab_{Aut X}(C)` is an injective homomorphism with `E(h)|_C = h` and
     `r ∘ E(h) = h ∘ r`.
   - `E` maps `Comm_{Aut C}(W_{st(D)})` into `Comm_{Aut X}(W_L)`, and it is the identity on `W_{st(D)}`.
4. **Normalized kernels.**
   - `K := ker r` is normalized by `E(Aut C)`, and `W_L = K ⋊ W_{st(D)}`.
   - Let `ψ: W_L → (Z/2)^{P(D)}` send `E ↦ e_{E ∩ D}`. Then `K_0 := K ∩ ker ψ` is a torsion-free subgroup
     of finite index in `K`, and it is also normalized by `E(Aut C)`.
5. **Hyperplane realization.**
   - For every torsion-free uniform lattice `F ≤ Aut(H_0)`, the group `W_F := K_0 ⋊ E(F)` is a Davis
     lattice (a torsion-free uniform lattice of `Aut(X)`) with `Stab_{W_F}(H_0) = E(F)`, which restricts
     to `F` on `H_0`.
   - So every free lattice of the `d`-regular tree is a hyperplane stabilizer of some Davis lattice.
6. **EXT holds.** Let `Γ = F_a *_{F_e} F_b` be a torsion-free, edge-transitive lattice on `T' × T_d`
   with `pr_{T_d}` injective, for instance any irreducible Burger–Mozes, Rattaggi or Radu group.
   - Put `W_1 = W_{F_a}` and `W_2 = W_{F_b}`. Then `W_1 ∩ W_2 = K_0 ⋊ E(F_e)` has finite index in both,
     and its stabilizer of `H_0` is `E(F_e)`.
   - `Λ := W_1 *_{W_1 ∩ W_2} W_2` is a torsion-free uniform lattice of cohomological dimension 3 in
     `Aut(T') × Aut(X)`. Its hyperplane sub-amalgam at `H_0` is `Γ`, so `Λ` is non-residually finite
     whenever `Γ` is.
7. **But it is split.** `Λ ≅ K_0 ⋊ Γ`. `K_0` is normal in both factors and lies in the edge group, so it
   acts trivially on the tree. Hence `Λ` is never just-infinite and never virtually simple, so
   conditions (N1)/(N2) of the required node fail.

   The open gate is:
   - **(IRR)** realize the hyperplane data (`Stab_{W_i}(H_0) = F_a, F_b`, with intersection `F_e`) by
     Davis lattices whose intersection `A` contains **no nontrivial subgroup normal in both** `W_i`.
     Equivalently, `Λ` acts faithfully on its tree.
   - In addition, (N1) should hold: `⟨W_1, W_2⟩` is dense in `U(Alt_{2d-1})`.

## Proof

1. **Fields.** Given a compatible field and an image `y_0` of `1`, set
   `g(E_1⋯E_k) = y_0 · σ_{x_0}(E_1) σ_{x_1}(E_2) ⋯`, where `x_i = E_1⋯E_i`.
   - **Well defined.** The relators of `W_L` are respected.
     - For `EE`: `σ_{xE}(E) = σ_x(E)`, since `E ∈ st(E)`.
     - For a commuting pair `EE' = E'E` (adjacent in `L`): `σ_{xE}(E') = σ_x(E')` and `σ_{xE'}(E) = σ_x(E)`,
       and `σ_x(E)`, `σ_x(E')` are adjacent, so they commute.
   - **Automorphism.** So `g` is a graph automorphism that preserves squares. Since `X` has no 3-cubes
     (`O_d` is triangle-free), it is an automorphism of `X`.
   - **Converse.** The field of any automorphism is compatible: an edge has one type from both ends,
     and opposite edges of a square have the same type. This is AL's universal-group calculus (§3).
2. **Commensurator.** The field of `g w g^{-1}` at `g x` is `σ_g(wx) σ_g(x)^{-1}`. The type-preserving
   automorphisms are exactly `W_L`, since such an automorphism fixing a vertex is the identity. So
   `g W' g^{-1} ⊆ W_L` iff `σ_g` is `W'`-invariant, and then the index is finite by covolume.
3. **Canonical extension.**
   - **Compatibility of `E(h)`.** Take an edge `(w, wE)`.
     - If `E ∉ st(D)`, then `r(w) = r(wE)`, so the two fields are equal.
     - If `E = D`, the edge lies over one vertex of `H_0`, so again equal.
     - If `E = D' = D^c ∖ {p} ∈ lk(D)`, then `st(D') = {D'} ∪ {(D ∪ {p}) ∖ {q}}`. The field
       `(id_D, τ)` sends `D' ↦ D^c ∖ τ(p)`, `(D∖q) ∪ {p} ↦ (D∖q) ∪ {τ(p)}` and `D ↦ D`. The two values
       of `τ` agree at `p`, because `h` is an automorphism of the coloured tree `H_0`.
   - **Restriction and equivariance.** `σ` preserves `st(D)` and `L ∖ st(D)`. So `E(h)` preserves `C`,
     agrees with `h` there (same base point, same field), and maps the `st(D)`-letters of a path to their
     images under `h`. That is `r ∘ E(h) = h ∘ r`.
   - **Homomorphism.** Combine the cocycle identity `σ_{hh'}(c) = σ_h(h'c) σ_{h'}(c)` with equivariance.
   - **Commensurators.** If `τ_h` is invariant under a finite-index `F' ≤ W_{st(D)}`, then `τ_h ∘ r` is
     invariant under `r^{-1}(F')`, because `r(kx) = r(k) r(x)`. Apply item 2.
4. **Normalized kernels.**
   - **`K`.** The field of `E(h) k E(h)^{-1}` at `E(h)x` is `τ̂(r(kx)) τ̂(r(x))^{-1} = id`, since
     `r(kx) = r(x)`. So this element is in `W_L`, and by equivariance its `r`-image is `1`.
   - **`K_0`.** `K` is generated by the reflections in hyperplanes of type `E ∉ st(D)`. Conjugation by
     `E(h)` sends such a reflection to the reflection in the image hyperplane, whose type is `σ(E)`, and
     `σ(E) ∩ D = E ∩ D`. So `ψ|_K` is `E(h)`-invariant.
   - **Torsion-freeness of `K_0`.** Finite subgroups of `W_L` are conjugate to `W_σ` with `σ` a vertex or
     an edge of `L`.
     - Their nontrivial elements in `K` are conjugates of `E ∉ st(D)`, with `ψ = e_{E∩D} ≠ 0`.
     - Or they are conjugates of `EE'` with `E, E' ∉ st(D)` disjoint, where `E∩D` and `E'∩D` are disjoint
       and nonempty, so `ψ ≠ 0`.
     - Any other finite-order element has nontrivial `r`-image.
5. **Hyperplane realization.**
   - **Orbits.** `V(X) = K · W_{st(D)}`. `K` is simply transitive on each fibre of `r`, and `E(F)` covers
     the action of `F` on `V(C)`. That action is free, because a torsion-free tree lattice acts freely on
     vertices. So `K ⋊ E(F)` acts freely on `V(X)` with finitely many orbits.
   - **Torsion-freeness.** Its torsion maps trivially to `F`, so it lies in `K`. Hence `K_0 ⋊ E(F)` is
     torsion-free, a uniform lattice.
   - **Hyperplane stabilizer.** `k E(h)` preserves `C` only if `k` does, and `K ∩ W_{st(D)} = 1`.
6. **EXT holds.**
   - **Intersection.** Decompositions `k E(h)` are unique, so `W_1 ∩ W_2 = K_0 ⋊ E(F_a ∩ F_b)`. Also
     `F_a ∩ F_b = F_e`: `pr_{T_d}` is injective on `Γ`, and adjacent vertex stabilizers meet in the edge
     stabilizer.
   - **Conclusion.** Apply items 2 and 3 of the required node.
7. **Splitting.** Both actions on `K_0` are restrictions of the conjugation action of `E(Aut C)`. So the
   universal property gives `(K_0 ⋊ E F_a) *_{K_0 ⋊ E F_e} (K_0 ⋊ E F_b) ≅ K_0 ⋊ (F_a *_{F_e} F_b)`.
   - `K_0` is nontrivial and normal, lies in the edge group, and has infinite index, since `Λ/K_0 ≅ Γ`.
   - So `Λ` is not just-infinite. By Bader–Shalom, its two projection closures cannot both be just
     non-compact.

## Consequences

- EXT (`kourovka-21-46-reduces-to-simple-amalgams-of-davis-lattices` item 7) is proved. Every
  Burger–Mozes, Rattaggi or Radu group sits in a hyperplane of a torsion-free lattice on `T' × X_{O_d}`
  of cohomological dimension 3.
- The whole difficulty of Kourovka 21.46 on this route is **(IRR)**. `A` must be core-free, which
  forces the gluing to be transverse to every Coxeter retraction `r`.
  - **Amir–Lazarovich.** AL's lattice escapes the splitting only because their `ζ_z` do not preserve the
    `D`-parts `E ∩ D`. They pay for this with involutions.
  - **A torsion-free twist.** The next attempt is
    `W_2 = φ E(b) W_{F_a} E(b)^{-1} φ^{-1}`, where:
    - `F_b = b F_a b^{-1}`;
    - `φ ∈ Comm(W_L)` fixes `C` pointwise and commutes with `E(F_e)`;
    - `φ` moves `K_0` off itself, i.e. it does not preserve the fibres of `r`.

## Lesson for general BH

- **Extension through a hyperplane is free.** A Coxeter retraction onto the special subgroup of a star
  gives a homomorphic section `Aut(carrier) → Aut(X)`, and it preserves commensurators. So any lattice
  on a product of trees, and any group that embeds in one, sits in a hyperplane of a lattice on
  `T × X_{O_d}`.
- **But such extensions are split** (`K_0 ⋊ Γ`), and splitting is the enemy of simplicity.
- **Where simplicity must come from.** In lattice-built simple hosts, the content is never the
  embedding. It is **irreducibility**: the gluing must be transverse to every retraction, so that no
  common normal subgroup survives. More generally, any BH host built by retraction-extension is a
  split extension. A simplicity proof must use an ingredient that no retraction sees.
