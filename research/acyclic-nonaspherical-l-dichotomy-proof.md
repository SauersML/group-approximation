---
rg: 2
id: acyclic-nonaspherical-l-dichotomy-proof
kind: route
title: Run the Bestvina--Brady shadow argument for any acyclic finite flag 2-complex with nonzero pi_2
target: acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead
requires: []
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

All cited statements are from Bestvina--Brady, Invent. Math. 129 (1997),
read from the Springer PDF on MSI. Each one is stated there for an arbitrary
finite flag complex `L`, which was checked in the text; see the artifact,
Section 2.

**Step 0: `pi_1(L)` is nontrivial.** A simply connected acyclic CW complex is
contractible, by the Hurewicz and Whitehead theorems. So `pi_2(L) != 0` forces
`pi_1(L) != 1`.

**Step 1: finiteness and cohomological dimension.** `L` is acyclic, so it is
connected, and `H_L` is finitely generated (Main Theorem (1)). By Example (3)
of the Introduction (quoted verbatim in
`eilenberg-ganea-or-whitehead-bestvina-brady-citation`), `H_L` is FP, not
finitely presented, and has cohomological dimension 2.
- The upper bound comes from the free cocompact action of `H_L` on the level
  set `X_t`. It is 2-dimensional and acyclic by Theorem 8.6: `X_J` is homotopy
  equivalent to a wedge of copies of `L`.
- For the lower bound: cohomological dimension at most 1 would make `H_L` free
  (Stallings--Swan), and a finitely generated free group is finitely presented,
  contradicting Example (3).

**Step 2: geometric dimension not 2.** Then `H_L` has cohomological dimension 2
and no 2-dimensional `K(H_L,1)`, which is a counterexample to the
Eilenberg--Ganea conjecture as stated on p. 461.

**Step 3: geometric dimension 2.** This is the proof of Theorem 8.7
(pp. 469--470). The only property of `L` it uses is `pi_2(L) != 0`.
1. Let `Y` be a contractible 2-complex on which `H_L` acts freely, properly and
   cellularly. Let `X`, `f` and `X_t` be as in Theorem 5.12. Since `Y` is
   contractible there is an `H_L`-equivariant PL map `phi: X_t -> Y`. Both
   `X_t` and `phi(X_t)` carry free cocompact `H_L`-actions and are connected,
   so they are quasi-isometric, and point preimages of `phi` have uniformly
   bounded diameter.
2. For a vertex `v` with `f(v) > t`, the shadow `S_(v,L)` of Definition 8.8 is
   homeomorphic to `L`. By the observation after Definition 8.8, which uses the
   convexity of `K_v` (Lemma 8.3), it is quasi-isometric to `L` with
   equilateral triangles of side `|f(v) - t|`, with constants independent of
   `|f(v) - t|`. Choose `|f(v) - t|` large compared with the quasi-isometry
   constants.
3. For `x` in `S_(v,L)`, the minimal simplex `sigma` determined by the geodesic
   `[x,v]` gives a preimage `phi_v^(-1)(phi_v(x))` inside
   `S_(v, St0(sigma,L))`. That set is contractible by Proposition 5.10 (1),
   which holds for every flag complex.
4. Mapping each vertex of `phi_v(S_(v,L))` to a point of its preimage and
   extending over skeleta gives a left homotopy inverse `psi` of
   `phi_v: S_(v,L) -> phi_v(S_(v,L))`, so `psi phi_v ~ id`.
5. After subdividing `Y`, `K = phi_v(S_(v,L))` is a finite connected subcomplex
   of `Y`. Since `psi phi_v ~ id`:
   - `pi_2(L) = pi_2(S_(v,L)) -> pi_2(K)` is injective, so `pi_2(K) != 0`;
   - `pi_1(L)` is a retract of `pi_1(K)`.
6. `Y` is contractible, hence aspherical. So `K` is a connected non-aspherical
   subcomplex of an aspherical 2-complex.

**Step 4: examples.** If `G = pi_1(L)` is finite and nontrivial, the universal
cover `L~` is a finite simply connected 2-complex with `chi(L~) = |G| chi(L) =
|G|`. So `H_2(L~)` is free of rank `|G| - 1 >= 1`, and `pi_2(L) = H_2(L~) != 0`.

**Trust surface.** The general lemmas (Theorems 5.12 and 8.6, Lemma 8.3,
Proposition 5.10, the observation after Definition 8.8, and Example (3)) are
taken from the source as stated, not re-proved. The quasi-isometry and
left-inverse steps follow the source's proof of Theorem 8.7.
