---
rg: 2
id: sfts-without-two-sided-faults-are-quantum-rigid
kind: claim
title: A Z^2 subshift of finite type in which every line has a determining side is quantum rigid, so its crossed product is finitely presented over every field; rigidity is decided at two-sided faults
requires:
  - determinism-closure-certifies-quantum-rigidity
  - sft-crossed-product-fp-iff-quantum-rigid
distinct_from:
  determinism-closure-certifies-quantum-rigidity: that is a combinatorial criterion, commutation along a closure of rule shapes; this is a dynamical hypothesis on determining normals that always makes the closure all of Z^2, together with the exact geometric condition under which a determinism argument can succeed.
  permutive-triangle-sfts-are-quantum-rigid: that treats one local mechanism, where the non-determining normals lie on three rays; here any closed set of non-determining normals without an antipodal pair is allowed, for any rule shapes.
  triangle-permutive-existence-iff-hex-cone-determinism: that proves that sub-SFTs of quasigroup spacetimes have their non-determining normals on three rays with no antipodal pair; combined with it, this node gives a second proof that all of them are rigid.
  self-similar-sft-thin-walls-refute-quantum-rigidity: that is the refuting side, where a wall is a special two-sided fault; this is the certifying side, with no two-sided fault at all.
---

**ESTABLISHED (2026-09-18)** through `sfts-without-two-sided-faults-rigidity-proof`. Lane proof (bh-free-35),
elementary, not independently reviewed. No priority is claimed; a bounded search of the rigidity and determinism
nodes on main found this hypothesis only in the three-ray form of `triangle-permutive-existence-iff-hex-cone-determinism`.

## Definitions

- `Ω ⊆ A^(Z^2)` is a nonempty SFT.
- As in `triangle-permutive-existence-iff-hex-cone-determinism`, a nonzero `n ∈ R^2` is **determining** if, for every
  real `t`, two points of `Ω` that agree on `{z : ⟨z,n⟩ < t}` are equal. This is invariant under conjugacy
  (Theorem B there).
- The line `n^⊥` is a **two-sided fault** if neither `n` nor `−n` is determining.
- Every expansive line has both normals determining.

## Theorem

1. **Rigidity.** If `Ω` has no two-sided fault (rational or irrational), then `Ω` is `D`-quantum rigid for some `D`,
   and `LC(Ω, k) ⋊ Z^2` is finitely presented over every field `k`.
2. **Quantitative form.** Compactness gives finitely many rules `F_1, …, F_m`, each `F_i` inside an open half-plane
   through `0`, with the following properties.
   - A uniform margin `η > 0`: every unit `u` has some `i` and sign `ε` with `⟨f, εu⟩ <= −η` for all `f ∈ F_i`.
   - A radius `ρ` with `F_i ⊆ B^E_ρ(0)`.
   - `D = ρ + ⌈(ρ²/η + ρ)/2⌉` works.
3. **A two-sided fault blocks every determinism proof.** If `n^⊥` is a two-sided fault, no rule lies in either open
   half-plane of `n^⊥`. The determinism closure from any initial ball then stays in a slab normal to `n`. This is
   the argument of item 3 of `determinism-closure-certifies-quantum-rigidity`, with "fault normal" weakened to "two-sided
   fault".
4. **Trichotomy.**
   - (a) No two-sided fault: rigid, by item 1.
   - (b) A **wall**, meaning that for every width there are two points agreeing on a strip parallel to `ℓ` and
     differing on both sides: not rigid. This is the wall certificate of `sft-crossed-product-fp-iff-quantum-rigid`.
     For self-similar SFTs a single thin wall suffices (`self-similar-sft-thin-walls-refute-quantum-rigidity`).
     Every wall line is a two-sided fault.
   - (c) Two-sided faults without walls. The typical case is **slabs**: two points differing only inside a strip.
     Here the two-dimensional glued family built from the pair commutes, because off the slab its operators are
     scalars. So neither determinism nor the wall certificate decides. This is exactly the fault-crossing gate
     (Labbé: slab faults in four directions by item 4 of `determinism-closure-certifies-quantum-rigidity`, and no walls
     to first order by `labbe-shift-is-wall-rigid`).

## Corollaries

- **Known rigid classes.** Items 1–4 recover Ledrappier's shift and, via Theorem B of
  `triangle-permutive-existence-iff-hex-cone-determinism`, every sub-SFT of a quasigroup spacetime
  (`permutive-triangle-sfts-are-quantum-rigid`). The two proofs are independent.
- **Fixed-point tile sets.**
  - By `fixed-point-tile-set-rigidity-is-a-bounded-range-test`, commutation up to range `R(D) = N(2D+2) − 2` suffices.
  - A determinism closure reaching `B_(R(D))` exists only if there is no two-sided fault, by item 3, since
    `B_(R(D))` leaves every slab of the initial ball. Item 1 then already gives rigidity.
  - So a bounded-range certificate search teaches something new only through **noncommutative** derivations, that is,
    ideal membership that is not a composition of rule identities.
- **Design target for G2 over Z^2.** Some free minimal SFT has no two-sided fault. It is posed as
  `free-minimal-sft-without-two-sided-faults-exists`. That is strictly weaker than
  `free-minimal-triangle-permutive-sft-exists`, which confines the non-determining normals to three rays. Here any
  closed set of normals without an antipodal pair is allowed, for example an arc of length just under `π`.

## Lesson for general BH

Rigidity of a Z^2 SFT is decided at its two-sided faults.
- If every line has a determining side, pure determinism proves finite presentation, with no permutivity and no group
  law needed.
- If some line carries walls, it fails.
- Everything open lies between these: slab and resonant faults, where information is invisible from both sides but
  never separates two sides.

For the master route this changes what to build, not only what to check. A rigid free minimal SFT needs one-sided
information flow across *every* line (the "one-way flow" design rule), or else a noncommutative mechanism at slab faults.
Walls are what to avoid, and the thin-wall test decides them in one step for self-similar designs.
