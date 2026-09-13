---
rg: 2
id: labbe-full-group-embeds-in-its-supertile-corner-proof
kind: route
title: Recognizability of Labbé's morphism recodes the groupoid onto its anchor corner, which gives the corner endomorphism
target: labbe-full-group-embeds-in-its-supertile-corner
requires:
  - minimal-aperiodic-wang-shift-exists
---

**Input (read from source, arXiv:1802.03265).**
- **Definition** (TeX lines 1136–1146). A pair `(k, x)` with `y = sigma^k omega(x)` is an
  `omega`-representation of `y`. It is *centered* if `0 <= k < shape(omega(x_0))` coordinatewise.
  `omega` is recognizable in `X` if each `y` has at most one centered representation with
  `x ∈ X`.
- **Proposition `prop:pre-main`** (line 2269). `omega = alpha∘beta∘gamma` is expansive and
  recognizable in `Omega_U`, and
  `Omega_U = omega(Omega_U) ∪ sigma^(e_1) omega(Omega_U) ∪ sigma^(e_2) omega(Omega_U) ∪ sigma^(e_1+e_2) omega(Omega_U)`.
  Its proof notes that some letter is sent to a word of shape `(2, 2)`.
- `omega(x)` places the rectangular blocks `omega(x_w)` on a grid. Block widths are constant along
  columns and heights along rows, which is how `omega : Omega_U -> Omega_U` is defined.

**Proof.**
1. **Centered representations exist.** Given `y`, write `y = sigma^v omega(x)` with
   `v ∈ {0, e_1, e_2, e_1+e_2}`. If `v` leaves the block of `x_0` in a coordinate, that block has
   side 1 there, and `v` is the origin of the neighbouring block. Replace `x` by `sigma^(e_i) x`
   and subtract `e_i`. The result is centered.
2. **They are unique.** This is recognizability.
3. **The representation map is continuous.** Let `K` be the finite set of possible `k`. The set
   `Γ = {(y, k, x) : y = sigma^k omega(x), (k, x) centered}` is closed in
   `Omega_U x K x Omega_U`, since `omega` is continuous and centeredness reads `x_0`. So `Γ` is
   compact. By steps 1 and 2 the projection `Γ -> Omega_U` is a continuous bijection, hence a
   homeomorphism, so `y -> (k(y), x(y))` is continuous.
4. **Item 1.**
   - `A = {y : k(y) = 0}` is clopen.
   - It is nonempty. It is proper: take `x` whose origin tile is sent to a `(2,2)` block (all tiles
     occur, by minimality), and put `y = sigma^((1,1)) omega(x)`; then `k(y) = (1,1)`.
   - The invariant probability has full support by minimality, so `0 < mu(A) < 1`.
5. **Item 2.**
   - **The recoding.** `omega : Omega_U -> A` is continuous and surjective. It is injective by
     uniqueness of the representation with `k = 0`. So it is a homeomorphism.
   - **The cocycle.** Let `L(x, w)` be the position in `omega(x)` of the bottom-left corner of the
     block `omega(x_w)`: a signed sum of block widths along row `w_2` and heights along column
     `w_1`. It depends on finitely many tiles of `x`, so it is continuous. Also
     `omega(sigma^w x) = sigma^(L(x,w)) omega(x)` and `L(x, w + w') = L(x, w) + L(sigma^w x, w')`.
   - **Injective.** `w -> L(x, w)` is injective, since distinct blocks have distinct corners.
   - **Surjective.** Suppose `sigma^v omega(x) ∈ A`. Write `v = L(x, w) + k` with `k` inside the
     block of `x_w`. Then `sigma^v omega(x) = sigma^k omega(sigma^w x)` is a centered
     representation. The point also has the centered representation `(0, x')`, so `k = 0` and
     `v = L(x, w)`.
   - Hence `(x, w) -> (omega(x), L(x, w))` is a bijective, continuous and open morphism
     `𝒢 -> 𝒢|_A`.
6. **Item 3.**
   - **Well-defined.** For `g ∈ [[𝒢]]` with cocycle `c_g`, on `A` we have
     `Phi(g)(omega(x)) = sigma^(L(x, c_g(x))) omega(x)`, a homeomorphism of `A` with continuous
     cocycle. Extended by the identity on the clopen complement, it lies in `[[𝒢]]`.
   - **Injective homomorphism.** `Phi(gh) = Phi(g) Phi(h)`, and `Phi(g) = id` forces `g = id`,
     since `omega` is injective.
   - **Image.** Let `h` fix `Omega_U \ A` pointwise, with cocycle `v` on `A`. By step 5, `v(omega(x))`
     equals `L(x, w(x))` for a unique `w(x)`, which is continuous in `x`. Then `g(x) = sigma^(w(x)) x`
     is a bijection with continuous cocycle, and `Phi(g) = h`.
7. **Item 4.** `Phi` is an isomorphism onto its image, so it maps commutators onto commutators and
   `Phi(D([[𝒢]])) = D_A`. Commutators of elements of `[[𝒢]]` lie in `D([[𝒢]])`, so
   `D_A ≤ D([[𝒢]])`.
   - **Properness.** Pick `y ∉ A`. By aperiodicity there is a clopen `U ∋ y` with `U`,
     `sigma^(e_1) U` and `sigma^(2e_1) U` pairwise disjoint.
   - The 3-cycle permuting these three sets lies in `D([[𝒢]])` (ChJN arXiv:1602.04255, line 209) and moves `y`.
   - Every element of `D_A` fixes `y`, so the inclusion is proper. ∎
