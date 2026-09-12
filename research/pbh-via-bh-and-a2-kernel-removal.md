---
rg: 2
id: pbh-via-bh-and-a2-kernel-removal
kind: route
title: Place a Boone-Higman group sharply in a type [A_2] actor, remove the kernel, and read off a faithful type (A) actor
target: permutational-boone-higman-conjecture
requires:
  - boone-higman-conjecture
  - boone-higman-implies-relative-permutational-bh
  - a2-pairs-embed-in-a2-pairs-with-fng-kernels
artifacts:
  - research/artifacts/bh-type-a-actions-2026-09-12.md
---

Let `Γ` be finitely generated with solvable word problem.

1. By `boone-higman-conjecture`, `Γ` embeds in a finitely presented simple group.
   By `boone-higman-implies-relative-permutational-bh` (FFWZ Theorem C), `Γ`
   sharply embeds in `(G, K)`, where `G` acts on `S` with type `[A_2]` and kernel
   `K`.
2. By `a2-pairs-embed-in-a2-pairs-with-fng-kernels`, `(G, K)` sharply embeds in
   `(G', K')`. Here `G'` acts on `S'` with type `[A_2]` and `K'` is finitely
   normally generated.
3. Then `Γ ∩ K' = Γ ∩ K = 1`, so `Γ` embeds in `G'/K'`.
   - `G'/K'` is finitely presented, since `G'` is and `K'` is finitely normally
     generated.
   - It acts faithfully on `S'`.
   - Point stabilizers are images of finitely generated groups.
   - The pair orbits are those of `G'`.

   So `G'/K'` carries a type (A) action and contains `Γ`.

This matches FFWZ's note that a "yes" to the first part of their Question 5.9
gives (relPBH) ⇒ (PBH).

With `boone-higman-via-permutational-boone-higman`, this route forms an intended
cycle, like `permutational-boone-higman-via-mif-envelopes`. It records a
conditional equivalence, and it does not fire while
`boone-higman-conjecture` is open.
