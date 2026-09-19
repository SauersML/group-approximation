---
rg: 2
id: exponential-growth-groups-admit-no-contracting-block-hierarchies
kind: claim
title: A finitely generated group with a bounded-block hierarchy whose collapse map coarsely contracts the word metric has polynomial growth, so no hierarchical tiling of a regular tree, of F_2 × F_2 or of any exponential-growth group has an inflation that is a quasi-isometric self-embedding with expansion greater than one
distinct_from:
  nonzero-euler-characteristic-forbids-endomorphism-inflations: that excludes inflations induced by injective endomorphisms when χ ≠ 0; this excludes every geometric inflation (any bounded-block hierarchy whose inflation scales distances), endomorphic or not, for every group of exponential growth.
  substitution-inflation-hosts-are-full-contracting-rsgs: that uses a geometric inflation over Z^d, where such hierarchies exist; this shows Z^d-type (virtually nilpotent) groups are the only ones where they exist.
---

**ESTABLISHED** (elementary lane proof, bh-invent-06b, 2026-09-18; not reviewed; no priority claimed).
- The growth count is Franks' argument for expanding maps.
- The step from polynomial growth to virtual nilpotence is Gromov's theorem (recalled).

## Setting

- `Λ` is finitely generated with word metric `d`, and `β(r) = |B(r)|`.
- A **contracting block hierarchy** is a map `ψ : Λ → Λ` (the collapse; `ψ^(−1)(h)` is the supertile of `h`)
  with two properties:
  - **bounded blocks:** `|ψ^(−1)(h)| <= M` for all `h`;
  - **coarse contraction:** `d(ψ g, ψ g′) <= λ^(−1) d(g, g′) + C` for some `λ > 1` and `C >= 0`.
- **Equivalent inflation form.**
  - Let `Φ : Λ → Λ` send `h` to a cell of its supertile.
  - The hierarchy is contracting iff `Φ` is a quasi-isometric embedding with expansion `λ`,
    `d(Φh, Φh′) >= λ d(h,h′) − C′`, with `D`-dense image.
  - Indeed `ψ(g)` is the `h` whose supertile contains `g`, and `d(g, Φψ g) <= D`.

Self-similar substitution tilings of `Z^d` (inflation `v ↦ kv`, or the box grids of
`substitution-inflation-hosts-are-full-contracting-rsgs`) give contracting block hierarchies.

## Statement

1. **Growth.** If `Λ` has a contracting block hierarchy, then `β(r) <= K r^(log_μ M)` with `μ = 2λ/(λ+1)`, so
   `Λ` has polynomial growth and is virtually nilpotent.
2. **Regular trees, sharp form.** Let `d >= 3`, and partition the `d`-regular tree `T_d` into finite connected
   blocks. If the quotient graph is again `T_d`, every block is a single vertex.
3. **Consequence.** No hierarchical tiling of `T_4` (the Cayley tree of `F_2`), of `F_2 × F_2`, or of any group
   of exponential growth has an inflation that is a quasi-isometric self-embedding with expansion `λ > 1`. That
   includes non-connected, non-coset and non-endomorphic supertiles.

## Proof

**1. Growth.**
- Coarse contraction gives `ψ(B(g, R)) ⊆ B(ψg, R/λ + C)`, and each point has at most `M` preimages. So
  `β(R) <= M β(R/λ + C)`.
- Put `μ = 2λ/(λ+1) > 1` and `R_* = 2Cλ/(λ−1)`. For `R >= R_*` we have `R/λ + C <= R/μ`, so
  `β(R) <= M β(R/μ)`.
- Iterating, `β(μ^n R_*) <= M^n β(R_*)`. Hence `β(r) <= K r^(log_μ M)`: polynomial growth, and virtual nilpotence
  by Gromov.
- For exponential growth, `β(R) >= e^(hR)` contradicts `β(R) <= M β(R/λ + C)` for large `R`, because
  `e^(hR(1 − 1/λ)) > M e^(hC)` eventually. ∎

**2. Trees.**
- A connected block `S` is a subtree with `|S| − 1` internal edges. So `d|S| − 2(|S| − 1) = (d−2)|S| + 2` edges
  leave it.
- Two of them cannot reach the same block `S′`: with `S` and `S′` connected, that would close a cycle.
- So `S` has degree `(d−2)|S| + 2` in the quotient tree, and this equals `d` iff `|S| = 1`. ∎

**3.** Item 1 applies, since every group containing `F_2` has exponential growth.

## Consequences for the unlabelled-compression problem

- By `labelled-hosts-of-free-actions-have-no-contracting-loops`, a finitely coded host over a free `F_2`- or
  `F_2 × F_2`-subshift needs unlabelled compressing germs.
- The natural way to keep translations finite-state is a geometric hierarchy, whose carries across supertile
  boundaries form a finite nucleus as in `substitution-inflation-hosts-are-full-contracting-rsgs`. **Item 1 rules
  this out** over every exponential-growth group, including the Track A groups `Λ_1 × Λ_1 ⊇ F_2`.
- What remains possible:
  - **(a) Fibre compression.** Contract an auxiliary coordinate (the `V` coordinate, or telescope label spaces),
    with translations finite-state relative to it.
  - **(b) Compression by `Λ` with isotropy.** Boundary codings, gate E3′.
- For (a) with a free action, the test is sharp: does some contracting RSG contain a free group acting freely on
  its Cantor space? Contracting self-similar groups have no free subgroups (Nekrashevych, recalled), but BBMZ's
  contracting RSGs contain hyperbolic groups acting on boundaries, with isotropy. The free-action case is open.

## Lesson for general BH

Geometric self-similarity (inflation) is a polynomial-growth phenomenon: Franks' count forbids any
bounded-supertile hierarchy that scales the metric of an exponential-growth group. So the "cure for freeness"
that works over `Z^d` cannot be transplanted to the non-amenable acting groups of Track A.
- There, compression is either **by the group**, which forces isotropy and topological (not full) freeness,
  or **in a fibre**, which is not geometric in `Λ`.
- The fallback "a tree tiling whose inflation is a quasi-isometric self-embedding" is impossible in the
  expanding form. The sharp open question left for free Track A is whether a contracting RSG can contain a free
  group acting freely.
