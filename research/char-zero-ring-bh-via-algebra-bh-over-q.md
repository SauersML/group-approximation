---
rg: 2
id: char-zero-ring-bh-via-algebra-bh-over-q
kind: route
title: The algebra Boone--Higman conjecture over Q gives the ring form, by tensoring with R_L
target: char-zero-ring-boone-higman
requires:
  - algebra-boone-higman-conjecture
  - fp-simple-q-algebras-embed-in-fp-simple-rings
---

Apply `algebra-boone-higman-conjecture` with `K = Q`, a computable field: `A` embeds in a
finitely presented simple `Q`-algebra `S`. Then `A ⊆ S ⊆ R_L ⊗_Q S`, which is a finitely
presented simple ring by `fp-simple-q-algebras-embed-in-fp-simple-rings`, part 2.
