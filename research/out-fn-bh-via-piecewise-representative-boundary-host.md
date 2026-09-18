---
rg: 2
id: out-fn-bh-via-piecewise-representative-boundary-host
kind: route
title: Strictify the Aut/Out(F_n) band on the boundary shift of F_n by piecewise representatives, then take the simple derived full group of the resulting germ groupoid
target: out-free-groups-satisfy-boone-higman
requires:
  - out-free-extension-pushed-into-the-boundary-full-group
  - out-free-acts-on-boundary-by-piecewise-representatives
  - piecewise-representative-boundary-hosts-are-fp-type-a
  - matui-purely-infinite-minimal-full-groups-have-simple-d
  - aut-f4-has-property-t
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Let `n ≥ 4`. This is Track A of the BH SYNTHESIS instantiated on one specific coding: the
reduced-word shift of `F_n`, which SYNTHESIS v5 records as quantum rigid by compression; this route does not use rigidity. The input
`Out(F_n)` acts on that coding by groupoid automorphisms rather than as the shift group.

1. **Strict action.** By `out-free-acts-on-boundary-by-piecewise-representatives` (open), a
   finite-index `Γ ≤ Out(F_n)` acts on `∂F_n` by piecewise representatives `h`. By item 3 of
   `out-free-extension-pushed-into-the-boundary-full-group`, `h` is injective, and
   `H_h = [[F_n ⋉ ∂F_n]] ⋊ h(Γ)` is finitely presented.
2. **Simplicity.** Let `𝒢_h` be the germ groupoid of `H_h`.
   - It is ample with Cantor unit space, and effective, since it is a germ groupoid.
   - It is **Hausdorff**. Near any point an element of `H_h` equals one map `(c_uΦ)^`. If
     that map is the identity on an open set accumulating at the point, it is trivial by
     (G) of the parent node, so the germ there is trivial.
   - It is **minimal and purely infinite**, since it contains the SFT groupoid
     `F_n ⋉ ∂F_n`, which is minimal and purely infinite (Matui, arXiv:1210.5800, Theorem `SFT>pim`), on the same unit space.
   - By `matui-purely-infinite-minimal-full-groups-have-simple-d`, `D_h = D([[𝒢_h]])` is
     simple.
   - Every `h_q` is a global bisection of `𝒢_h`, so `h([Γ,Γ]) ⊆ D_h`.
3. **Finite index.** `Γ` has property (T) for `n ≥ 4` (`aut-f4-has-property-t`: Aut(F_n)
   for n ≥ 4, hence its quotient Out(F_n) and its finite-index subgroups). So `Γ^{ab}` is
   finite, and `[Γ,Γ]` has finite index in `Out(F_n)`.
4. **Conclusion.** By `piecewise-representative-boundary-hosts-are-fp-type-a` (open),
   `D_h ∈ B_A`. So `[Γ,Γ] ∈ B_A`, and then `Out(F_n) ∈ B_A` by finite-index closure
   (`boone-higman-type-a-class-closed-under-finite-extensions`, part 2). By part 3 of that
   claim, `Out(F_n)` embeds in a finitely presented simple group. `∎`

**Status.** Open at steps 1 and 4.
- Step 1 is the only Out-specific input. It is strictly weaker than a virtual section of
  `Aut(F_n) → Out(F_n)`.
- Step 4 is a finiteness gate of the usual Stein–Farley kind.

**`n = 3`.** Step 3 fails, since `Out(F_3)` is not Kazhdan. The route then needs `Γ` itself
inside a simple host. For example, Cuntz-stabilize `𝒢_h` as in
`cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple`, if that node's
transformation-groupoid hypothesis can be met. Not checked.

**Why not the branch-host route.** `Out(F_n)` is a Kazhdan RF input for `n ≥ 4`. Bishop–Schesler
branch hosts are annular hosts over V, which are rank one. There FW rigidity confines a Kazhdan
input to one point's germ group (LESSONS, bh-synth-hosts), and finite presentation at that point
is the open crux of `board/major-branch.md` item 4. That route uses nothing about `Out(F_n)`.
This route uses the one piece of Out-structure available, the band `F_n → Aut(F_n) → Out(F_n)`,
and moves the whole difficulty into strictification (step 1) plus a standard finiteness gate.
