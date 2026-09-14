---
rg: 2
id: kms-hb2-girth-surfaces-give-surface-subgroups-proof
kind: route
title: Symbolic normal forms give the vertex groups, intersections and link girths of G_HB2(p), and girth link walks develop isometrically into its CAT(-1) complex
target: kms-hb2-girth-surfaces-give-surface-subgroups
requires: [cckw-kms-triangle-groups-structure]
artifacts:
  - experiments/kms-hb2-surface-subgroups/verify_integer_certificate.py
  - experiments/kms-hb2-surface-subgroups/verify.log
  - experiments/kms-hb2-surface-subgroups/girth_bounds.py
  - experiments/kms-hb2-surface-subgroups/girth-bounds.log
  - experiments/kms-hb2-surface-subgroups/girth_calibration.py
  - experiments/kms-hb2-surface-subgroups/girth-calibration.log
---

The notation is that of the target. BH is Bridson–Haefliger (1999). The BH items below are those read at
source for `ghb7-girth-surfaces-give-surface-subgroups-proof`; they were not re-read here. Steps 2–7
follow that proof with `7` replaced by `p`. Step 0 replaces its computations in `SL_4(F_7)` by
arguments valid for every odd prime.

## Step 0. Vertex groups, intersections and link girths

Let `U^{ab} = <a,b | a^p, b^p, [a,b,a], [a,b,b]>`. For `(x,y) = (c,b)` and `(c,a)`, let
`U^{xy} = <x,y | x^p, y^p, [x,y,x], [x,y,y,x], [x,y,y,y]>`.

**(a) Normal forms.**
- In `U^{ab}` put `u = [a,b]`. The relators say that `u` commutes with `a` and `b`. So `b^{−1}ab = au`,
  every element is `b^β a^α u^μ`, and conjugating `a^p = 1` by `b` gives `u^p = 1`.
- In `U^{xy}` put `u = [x,y]` and `v = [u,y]`. The relators say `[u,x] = [v,x] = [v,y] = 1`.
  - So `v` is central, `y^{−1}xy = xu` and `y^{−1}uy = uv`.
  - `<u,v>` is normal and abelian with abelian quotient, so every element is `y^β x^γ u^μ v^ν`.
  - Conjugating `x^p = 1` by `y` gives `u^p = 1`, and then conjugating `u^p` gives `v^p = 1`.
- So all exponents may be read mod `p`.

**(b) A quotient.** Put `ψ(a) = I + E_03 + E_12`, `ψ(b) = I + E_10 − E_23`, `ψ(c) = I + E_31`.
- Over `Z` these satisfy the eight commutator relators of `G`, and `(ψ(g) − I)^2 = 0`
  (`verify.log`, items 6–7).
- So `ψ(g)^p = I + p(ψ(g) − I)`. Reducing mod `p` gives a homomorphism `ψ : G → SL_4(F_p)` for every
  prime `p`.

**(c) Symbolic images** (`verify.log`, item 9, polynomial identities over `Z`, hence mod `p`). The
verifier prints the four exponents as `s, t, u, w`; here they are `s, t, w, z`. Entries not listed
are those of `I`.
- `ψ(b^s a^t u^w)`, `u = [a,b]`: `(0,3) = t`, `(1,0) = s`, `(1,2) = t`, `(1,3) = −2w + st`, `(2,3) = −s`.
- `ψ(b^s c^t u^w v^z)`, `u = [c,b]`, `v = [u,b]`: `(1,0) = s`, `(2,0) = 2z + w − sw`, `(2,1) = w − st`,
  `(2,3) = −s`, `(3,0) = w`, `(3,1) = t`.
- `ψ(a^s c^t u^w v^z)`, `u = [c,a]`, `v = [u,a]`: `(0,1) = −w + st`, `(0,2) = −2z − w + sw`,
  `(0,3) = s`, `(1,2) = s`, `(3,1) = t`, `(3,2) = w`.

**(d) Injectivity.**
- If `ψ(b^s a^t u^w) = I`, then `s ≡ t ≡ 0`, so `−2w ≡ 0` and `w ≡ 0` because `p` is odd.
- If `ψ(b^s c^t u^w v^z) = I` or `ψ(a^s c^t u^w v^z) = I`, then `s ≡ t ≡ w ≡ 0` and `2z ≡ 0`.
- With (a): `ψ` is injective on `U^{ab}`, `U^{cb}` and `U^{ca}`. Their orders are `p^3, p^4, p^4`,
  and each generator has order `p`. So the vertex groups map injectively onto `X_0, X_1, X_2`.

**(e) Intersections.** Compare the entries in (c).
- `X_0 ∩ X_1 = <b>`. Write an element both ways. Then `(0,3)`, `(3,1)` and `(3,0)` vanish in both
  forms, `(2,0)` forces `z ≡ 0`, and `(1,3)` forces `w ≡ 0`. So its image is `ψ(b^s)`, and injectivity
  on `X_0` gives the element `b^s`.
- `X_0 ∩ X_2 = <a>`. `(1,0)` gives `s ≡ 0` in the `X_0` form; `(3,1)` and `(3,2)` give `t ≡ w ≡ 0` in
  the `X_2` form; `(0,2)` gives `z ≡ 0`; and `(1,3)` gives `w ≡ 0` in the `X_0` form.
- `X_1 ∩ X_2 = <c>`. `(1,0)` and `(0,3)` kill both `s`; `(3,0)` and `(3,2)` kill both `w`; `(2,0)` and
  `(0,2)` kill both `z`.
- So `X_i ∩ X_j = <g_k>` whenever `{i,j,k} = {0,1,2}`, and `X_0 ∩ X_1 ∩ X_2 = 1`.

**(f) Link girths.** Let `Γ` be the coset graph of a group with respect to subgroups `A` and `B`, with
`A ∩ B = 1`. A backtrack-free closed walk of length `2n` in `Γ` gives a relation `α_1 β_1 ⋯ α_n β_n = 1`
with every `α_q ∈ A ∖ 1` and every `β_q ∈ B ∖ 1`.
- `U^{ab}`, `n = 2` (`girth-bounds.log` (A)). The exponent sums and `u`-exponent force `e_1 + e_2 ≡ 0`,
  `f_1 + f_2 ≡ 0` and `e_1f_1 + (e_1 + e_2)f_2 ≡ 0`, so `e_1f_1 ≡ 0`: impossible.
- `U^{xy}`, `n = 2` (`girth-bounds.log` (B)). Impossible in the same way.
- `U^{xy}`, `n = 3`. Here `e_3 ≡ −e_1 − e_2`, `f_3 ≡ −f_1 − f_2`, and `μ ≡ ν ≡ 0`. `girth-bounds.log` (C)
  gives the integer polynomial identity `2ν + e_3 f_2 f_3 = −(1 + f_1) μ`. So `2ν ≡ −e_3 f_2 f_3 ≢ 0`.
- `n = 1` is impossible because `A ∩ B = 1`. Relations of lengths 6 and 8 exist (`girth-bounds.log` (D)).
- So the coset graphs `Γ_0, Γ_1, Γ_2` have girths `6, 8, 8`. `girth-calibration.log` recomputes these
  girths and the orders `p^3, p^4` for `p = 3, 5, 7, 11` by breadth-first search in `SL_4(F_p)`.

## Step 1. Local structure of `Y`

The presentation of `G` is the union of the presentations of `U^{ab}`, `U^{cb}`, `U^{ca}`, amalgamated
along `<a>`, `<b>`, `<c>`. So `G` is the fundamental group of the triangle of groups with these vertex
groups, cyclic edge groups of order `p` and trivial face group.

By Step 0(f) its half girths are `3, 4, 4`, and `1/3 + 1/4 + 1/4 < 1`. So Theorem 3.1(i),(v) (item 1 of
`cckw-kms-triangle-groups-structure`, in the reading recorded there) gives the following.
- `G` acts by simplicial isometries on a CAT(−1) simplicial complex `Y`.
- A chamber `C = (v_0, v_1, v_2)` is a strict fundamental domain, isometric to the hyperbolic triangle
  with angles `π/3, π/4, π/4`.
- `Stab(v_i) = X_i`.

(a) *Every simplex of `Y` is `gF` for a face `F` of `C`.* Let `y` be an interior point of a simplex `σ`,
and write `y = g y_0` with `y_0 ∈ C`. Then `g^{−1}σ` is a face of `C`.

(b) *Stabilizers.*
- The vertices of `C` lie in distinct orbits. So `gC = C` forces `g ∈ X_0 ∩ X_1 ∩ X_2 = 1`, and `G`
  acts simply transitively on chambers.
- Let `e_k` join `v_i` and `v_j`. If `g` fixes `e_k`, then `g ∈ X_i ∩ X_j`.
- Conversely, the side `e_k` is a local geodesic (at an interior point the two directions along it are
  at angle `π`), hence the unique geodesic from `v_i` to `v_j`. So every element of `X_i ∩ X_j` fixes it.
- Hence `Stab(e_k) = X_i ∩ X_j = <g_k>` by Step 0(e).

(c) *Simplices at a vertex.*
- If `gσ ∋ v_i` for a face `σ` of `C`, then `g ∈ X_i`. So the chambers at `v_i` are the `xC` with
  `x ∈ X_i`, all distinct.
- The edges at `v_i` are the `x e_j` and `x e_k`, and `x e_j = x' e_j` if and only if `x^{−1}x' ∈ <g_j>`.
- So `Lk(v_i, Y)` is the metric graph `Γ_i`:
  - its vertex set is `X_i/<g_j> ⊔ X_i/<g_k>`;
  - it has one edge of length `π/m_i` for each `x ∈ X_i`, joining `x<g_j>` to `x<g_k>`;
  - its combinatorial girth is `2m_i`.
- The chambers containing `e_k` are the `hC` with `h ∈ <g_k>`, `p` of them.

## Step 2. The surface

`S` is an `M_{−1}`-polyhedral complex (BH Definition I.7.37).
- An interior point of a side has two half-discs around it.
- The corners identified with the `v_i`-corner of `Δ_t` are the `2m_i` points of the `<r_j, r_k>`-orbit
  of `t`, arranged cyclically. So the vertex has total angle `2m_i · π/m_i = 2π`.

Hence `S` is a closed surface, connected by transitivity. It has `V = T/6 + T/8 + T/8`, `E = 3T/2`,
`F = T`, so `χ(S) = −T/12`. Let `S̃` be its universal cover with the lifted structure.
- `Shapes(S̃)` is one triangle, so `S̃` is a complete geodesic space (BH Theorem I.7.50).
- `ε(w) > 0` for every `w ∈ S̃` (BH 7.38), since `w` lies in finitely many cells.

## Step 3. The developing map

Crossing from a chamber `D` of `S̃` over `Δ_t` across its side of type `k` carries `g_k^{x(t,k)}`. For a
gallery `γ`, let `h(γ)` be the product of its crossing elements.
- *`h(γ)` depends only on the endpoints.* Two galleries with the same endpoints in the simply connected
  surface `S̃` differ by inserting or deleting backtracks, which contribute `g^x g^{−x} = 1`, and full
  turns around vertices, which contribute cyclic rotations of vertex words or their inverses, all `1`.
- Fix a base chamber `D_0`. For a chamber `D` with a gallery `γ` from `D_0`, let `F` map `D` onto
  `h(γ)C` by the type-preserving isometry.
- If `D'` is adjacent to `D` across type `k` with crossing `g_k^x`, then `h(γ') = h(γ)g_k^x`. Since `g_k`
  fixes `e_k` pointwise, the two maps agree on the common side. So `F : S̃ → Y` is continuous and an
  isometry on each chamber.
- Deck transformations preserve crossing labels. So `F(σD) = φ(σ)F(D)`, where
  `φ(σ) = h(D_0 → σD_0)` is a homomorphism `π_1(S) → G`.

## Step 4. Link maps preserve `d_π = min(d, π)`

**At a vertex `w` of type `i`.** Translate so that `F(w) = v_i`.
- The chambers around `w` map, in cyclic order, to `c_0C, …, c_{2m_i−1}C`, with
  `c_{q+1} = c_q g_{k_q}^{±x_q}` and every `x_q ≢ 0 (mod p)`.
- In `Γ_i` this is a closed walk of `2m_i` edges, of length `2π`. It has no backtracking, since
  `g_{k_q}` has order `p` and so `c_{q+1} ≠ c_q`.
- *The walk is an embedded cycle `Z`.* A repeated vertex would split off a shorter closed walk without
  interior backtracking, hence a nontrivial cycle shorter than the girth.
- *`Z` is isometric for `d_π`.* Suppose `u, u' ∈ Z` with `d_{Γ_i}(u,u') < d_Z(u,u') ≤ π`. A geodesic
  `σ` and the shorter arc `α` between them are distinct reduced paths. So `σα^{−1}` cyclically reduces
  to a nontrivial cycle of length `< 2π`, contradicting the girth.

**At an interior point of a side.** The link of `S̃` is two semicircles. They map to two of the `p`
arcs at `F(w)`, distinct because `x ≢ 0 (mod p)`. Two arcs form an isometrically embedded circle.

**At an interior point of a chamber.** There is nothing to check.

## Step 5. `F` is locally an isometric embedding

By BH Theorem I.7.39, small balls about `w` and `F(w)` are isometric to balls about the cone points of
the `(−1)`-cones over the links. `F` is the cone over the link map `f`, and the cone metric depends only
on `d_π` of the link (BH Definition I.5.6). By Step 4, `F` restricted to a small ball is an isometry
onto its image.

## Step 6. `F` is an isometric embedding

Let `c` be a geodesic in `S̃` from `P` to `Q`. By Step 5, `F∘c` is a local geodesic in the CAT(−1) space
`Y`, hence a geodesic (BH Proposition II.1.4(2)). So `d_Y(FP, FQ) = d(P,Q)`.

## Step 7. Conclusion

- *Injectivity.* If `φ(σ) = 1`, then `F(σD_0) = F(D_0)`, so `σD_0 = D_0` because `F` is injective, and
  `σ = 1` because deck transformations act freely.
- *Quasiconvexity.*
  - `F(S̃)` is convex, since geodesics in `Y` are unique and `F` sends geodesics to geodesics.
  - `φ(π_1 S)` acts cocompactly on `F(S̃)`.
  - `G` acts properly and cocompactly on the locally finite complex `Y`.
  - So an orbit of `φ(π_1 S)` is coarsely dense in a convex subset, and `φ(π_1 S)` is quasiconvex.
- *Genus.* `π_1(S)` is a closed surface group with `χ = −T/12 < 0`. If `S` is orientable its genus is
  `1 + T/24`. An orientable connected double cover gives genus `1 + T/12` in either case.
