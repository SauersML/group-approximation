---
rg: 2
id: deligne-class-dies-on-some-rational-projective-host
kind: claim
title: For some n >= 2 there is an embedding of Sp_2n(Z) in a rational projective full group T_m on whose action groupoid Deligne's class dies
distinct_from:
  deligne-class-survives-on-standard-rational-projective-hosts: that shows the standard linear embedding, and every representation sphere with a Hermitian block in its generic stabilizer, fails; this asks for some embedding that works.
  deligne-extension-dies-on-lagrangian-cantor-covers: that kills the class over Cantor covers of the Lagrangian Grassmannian, whose natural full groups have no known finiteness; this asks for the same inside the rational projective full groups T_m, whose Farey structure is that of closed-mcg-embeds-in-rational-projective-full-group.
---

**OPEN.** There are `n ≥ 2` (ideally `n = 2`, the case of
`deligne-lattice-satisfies-boone-higman`), `m ≥ 1`, and an injective homomorphism
`j : Sp_{2n}(Z) → 𝒯_m`, linear or piecewise, such that Deligne's class dies in
`H^2(Sp_{2n}(Z); C(Ŝ_m, Z))` for the action through `j`.

**Sufficient.** A `j`-equivariant continuous map `Ŝ_m → Λ_n(R)`, by item 2 of
`deligne-extension-dies-on-lagrangian-cantor-covers`.

**Why it matters.** With `central-extension-shear-lift-into-rational-projective-groups`,
it puts Deligne's lattice in `𝒯_{m+2}`. Boone–Higman for it then follows from the same
finiteness claim as for closed mapping class groups
(`rational-projective-full-groups-are-finitely-presented`). That is route
`deligne-bh-via-rational-projective-full-group`.

## Attempts

1. **Standard representation: dead.** See
   `deligne-class-survives-on-standard-rational-projective-hosts`. The same holds for
   the 5-dimensional representation of `Sp_4`.
2. **`k·std`: dead, and so is every linear embedding (corrected 2026-09-18).**
   - An earlier lane remark here said that the measure obstruction does not fire for `k·std`,
     `k ≥ 2n`, because generic stabilizers are trivial. That is wrong: Lebesgue-generic points
     are not needed.
   - The orbit of `[v ⊗ a]`, with `a` having `Q`-independent coordinates, lies in no rational
     hyperplane and has a symplectic block in its stabilizer.
   - In general, `deligne-class-survives-on-every-linear-rational-projective-host` shows that no
     homomorphism `Sp_{2n}(Z) → GL_N(Z)` works, so the embedding `j` must be genuinely piecewise.
3. **Gram–Schmidt does not extend.** Symplectic Gram–Schmidt on the first `2n`
   vectors of a tuple gives an `Sp_{2n}(R)`-equivariant, scale-invariant map to
   `Λ_n(R)`. It is continuous off the real quadric where the successive pairings
   `ω(·,·)` vanish. That quadric is not a union of rational hyperplanes. Its generic
   points lie on no rational hyperplane, so `Ŝ` does not resolve it there, and the
   map has no continuous extension to `Ŝ`. A working map must be only
   `Γ`-equivariant, with its discontinuities moved onto rational hyperplanes, which
   form a `Γ`-invariant but not `G`-invariant family.
4. **Circles are no help.** Here `m = 1` needs an action of `Sp_{2n}(Z)` on the circle
   with Euler class `[ε]`. Such actions have finite image (Ghys; Burger–Monod;
   Witte Morris). So `m ≥ 2` is needed, and every `m ≥ 2` host contains the Kazhdan
   `SL_{m+1}(Z)`.
