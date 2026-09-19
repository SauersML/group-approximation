---
rg: 2
id: w-contains-heisenberg-with-divisible-centre
kind: claim
title: The twisted integral-affine group W contains H_3(Z) x_Z Q, a Heisenberg group with divisible, quadratically distorted centre; the next step toward U_3(Q) needs register addition
distinct_from:
  u3-q-embeds-in-fp-simple-group: that is the open target U_3(Q); this is its second layer {a, b in Z, c in Q}, realized inside W with the centre distorted, and the exact reason the third layer fails in W.
  rational-slope-germ-groups-have-bs-but-no-heisenberg: that excludes Heisenberg groups from one-dimensional rational-slope germ groups; here the Heisenberg distortion comes from linear shears on 2-adic coordinates, which are the higher-dimensional germs that node points to.
---

**ESTABLISHED** (lane proof, not reviewed; no priority or novelty claimed for Boone–Higman).

**Statement.** In `W` (`twisted-integral-affine-full-group-is-finitely-presented`), let
`x = e_12(1)`, `y = e_23(1)` and `z = e_13(1)` act linearly on the 2-adic coordinates `d_1, d_2, d_3`.
Let `* ∈ D` be a fourth coordinate. Then:
1. `z` lies in a copy `Q_z ≤ W` of `(Q, +)`, all of which commutes with `x` and `y`. And
   `⟨x, y, Q_z⟩ ≅ H_3(Z) ×_{⟨z⟩} Q = {(a, b, c) : a, b ∈ Z, c ∈ Q} ≤ U_3(Q)`.
2. `z` is quadratically distorted in `⟨x, y⟩`, so `W` holds a divisible central element that is
   also distorted. `VA`-type hosts cannot do this, since their cyclic subgroups are undistorted (O4, as recorded by
   gq-heis-q).
3. **The third layer fails in this form.** Build a root `x'` of `x` by the same register on another
   coordinate. Then `[x', y]` is `z` applied on the top register cylinder of `x'`, not an element
   of `Q_z`. In the suspension (register) model, matching it to `z_{1/n}` would require the map `(r, r') ↦ (r + r', r')` on two
   register coordinates. That map is not a homeomorphism of the Cantorized circle: it is
   discontinuous where `r + r' ∈ Q/Z` but `r, r' ∉ Q/Z`.

**Proof.**
1. `z = id_{C_*} × z'`, where `z'` does not read or change coordinate `*`. The registers `r_n` of
   `twisted-bt-point-fixing-actor-elements-are-divisible-proof`, item 1, are piecewise "prefix
   replacement on `*`" composed with `z'^q`, and these are elements of `W`. That proof's relations
   use only `z = id_* × z'` of infinite order, so `⋃ ⟨r_n⟩ ≅ Q` with `r_0 = z`.
   `x` and `y` fix coordinate `*` and commute with `z'`, so they commute with every `r_n`. The map
   `(h, q) ↦ h · r(q)` has kernel `{(z^{-q}, q) : q ∈ Z}`, because `r(q)` rotates the register
   unless `q ∈ Z`. This is exactly the central product.
2. This is classical for `H_3(Z)`.
3. Compute `x' y x'^{-1} y^{-1}` with the carry cocycle `κ ∈ {0, 1}` of the `x'`-register. Since
   `xyx^{-1} = zy`, it equals `z^κ`. ∎

## Lesson for general BH

**Divisibility and shear live on incompatible Cantor models.** A profinite group has no nonzero
divisible element: `x = m y_m` for every `m` forces `x ∈ U` for each open subgroup `U`. So on a
totally disconnected compact space, divisibility never comes from a compact group structure. It
must be register-type, as for the Cantorized circle, and registers carry no continuous addition.
Shears, and hence Heisenberg distortion, need a continuous group structure, as on the 2-adic
coordinates.

A host like `W` can hold both on **different coordinates**. That gives every central-divisible
extension of a linearly acting group (item 1). But any input in which a divisible element must
shear another divisible element, as in `U_3(Q)`, `Aff(Q)` or `GL_n(Q)`, needs a new local model
where register values can be added. That is a precise design target for the `U_3(Q)` and
`GL_n(Q)` roots.
