---
rg: 2
id: machine-sheet-rigid-layers-force-zero-entropy-fates
kind: claim
title: Gate 4 on the machine sheet splits into a rigid ambient SFT on K_M plus a carving; if the ambient is determined on each sheet by a half-plane rule (Ledrappier or no-two-sided-fault type), every sheet pattern class has N×N complexity |A|^{O(N)}, so the machine's fate configuration must have zero window entropy, which sparse accepting sets allow at every complexity
requires:
  - quantum-rigidity-passes-to-subshifts
  - machine-subgroup-is-core-free-and-draws-the-machine
  - sfts-without-two-sided-faults-are-quantum-rigid
distinct_from:
  machine-subgroup-is-core-free-and-draws-the-machine: that refutes the free fate-bit candidate; this states what a rigid replacement must satisfy.
  modular-machine-mortality-at-infinity-is-uniform: that shows unterminated m-adic runs are unavoidable; this shows a sheet-deterministic ambient can still carry them, provided the fate configuration has zero entropy.
---

**ESTABLISHED** (lane proof, bh-free-56, 2026-09-18; elementary; not reviewed) for items 1–2. Item 3 is a
remark.

**Setting.**
- The sheet of `machine-subgroup-is-core-free-and-draws-the-machine`: each coset `hZ² ⊆ K_M` is a grid.
  On the genuine sheet, `t` has loops exactly over `−H_0(M)`.
- The fate configuration `f_M(z) = [−z ∈ H_0(M)]`, a point of `{0,1}^{Z²}`.
- A relative seed must read `f_M` locally, since the `t`-loops are a local feature of the forced point.
  So `f_M` is a sliding-block image of the forced point restricted to the sheet.

## Statement

1. **Carving reduction.** It suffices to find:
   - an SFT `𝒜` on `K_M` that is `D`-quantum rigid;
   - a sub-SFT `W ⊆ 𝒜` over the same alphabet;
   - a point of `W`, isolated with stabilizer `T'_M`, whose orbit is dense in `W`.

   Then `(K_M, T'_M) ∈ 𝓡`, by `quantum-rigidity-passes-to-subshifts`. Rigidity is a property of the
   ambient alone, and isolation and (S3) are properties of the carving alone.
2. **Sheet determinism forces zero entropy.** Suppose `𝒜` is *sheet-deterministic*.
   - That is, there are a nonzero `n ∈ R²` and a finite `F ⊆ {w ∈ Z² : ⟨w, n⟩ < 0}` such that, for every
     point of `𝒜` and every coset `hZ²`, the letter at `hz` is determined by the letters at `h(z + F)`.
   - Any Z²-SFT layer with a determining direction has this form, by Step 1 of
     `sfts-without-two-sided-faults-rigidity-proof`. This covers Ledrappier and all layers without
     two-sided faults.

   Then for every point and every coset, the `N × N` windows of the sheet restriction take at most
   `|A|^{c(N+1)}` values, where `c` depends only on `F`.
   - **For `f_M`.** The window complexity of `f_M`, i.e. the number of distinct `N × N` windows, is
     `2^{O(N)}`.
   - **At infinity.** By (S3), the same bound holds for every joint pattern of fates that occurs at
     infinity, on the `m`-adic rogue sheets.
3. **Entropy is not complexity (remark).**
   - Window complexity `2^{O(N)}` means zero entropy. It is compatible with membership in `H_0` of any
     decidable complexity: any set whose accepted configurations are sparse in the sheet has at most
     `(N²)^{O(1)}` fate windows of size `N`.
   - A padding that keeps a mortal decider mortal and makes the accepting configurations sparse is
     expected by the usual checksum encodings. It is not proved here.
   - So item 2 constrains the machine's presentation, not its complexity, and does not by itself give
     CAP.

## Proof of 2

- *Direction.* Replace `n` by a nearby rational direction that still has `⟨F, n⟩ < 0`, since `F` is
  finite. Change coordinates by an element of `GL_2(Z)` so that `⟨f, n⟩ < 0` means `f_2 < 0`, i.e. every
  point of `F` lies strictly below the origin. Let `ρ = max |f|_∞` over `f ∈ F`.
- *Induction by rows.* The row `j` of a box `[0, N) × [0, N)` is determined by rows `j − ρ, …, j − 1`
  over a column range widened by `ρ` on each side.
  - So the whole box is determined by the `ρ` rows below it, over columns `[−ρN, (ρ+1)N)`.
  - That is at most `ρ(2ρ + 1)N` sites, which gives at most `|A|^{ρ(2ρ+1)N}` windows. Take
    `c = ρ(2ρ + 1)`.
- *Sliding-block images.* A sliding-block image `f` of a sheet restriction, with window radius `r`, has
  at most `|A|^{c(N+2r)}` windows of size `N`.
- *Joint fates at infinity.* Under (S3), every pattern of `W` occurs in the forced point's orbit. So joint
  fate patterns at infinity are windows of `f_M` and inherit the bound. `∎`

## What this means for gate 4

**The target.**
- A rigid ambient on `K_M` that is sheet-deterministic, or at least has a determining direction on each
  sheet.
- It must be coupled across `r`- and `l`-edges, the multiplicative moves between sheets, and across the
  pointer layer.
- A carving must cut out the forced point.

**Consequences.**
- By `modular-machine-mortality-at-infinity-is-uniform`, the ambient must also determine the letters on
  unterminated `m`-adic runs. It does, automatically, once the sheet rule is deterministic. This is the
  coupling that the fate-bit candidate lacked.
- By item 2, only machines with zero-entropy fate configurations can be carried. So the tower's machine
  should accept sparsely. That costs nothing in complexity.

**Next test.**
- A Ledrappier-type carrier on the sheets whose values along each move word are a reversible function of
  the machine's quadruple.
- Check it for determinism across the multiplicative `r`-edges, where the grid is rescaled by `m` and `m²`.
- In the Baumslag–Solitar geometry, the relevant known models are the Aubrun–Kari tilings of BS groups.

## Lesson for general BH

A rigid computing layer has zero entropy on every sheet on which it is deterministic. The answers it
carries must therefore be sparse, but sparseness costs nothing in complexity. So entropy is not where
CAP lives. The whole gate is the construction of a zero-entropy rigid carrier that crosses the
multiplicative edges of a Baumslag–Solitar-type geometry and is modulated by a reversible machine.
