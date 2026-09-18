---
rg: 2
id: leavitt-pairs-embed-sl-n-q-in-steinberg-groups-proof
kind: route
title: Doubling swindle with a square swap matrix, Whitehead's lemma and the room lemma
target: leavitt-pairs-embed-sl-n-q-in-steinberg-groups
requires: []
artifacts:
  - research/artifacts/gq-referee-a-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md
  - research/artifacts/gq-referee-b-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md
  - research/artifacts/gq-referee-c-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md
---

Direct proof, steps (a)–(f) in Attempt 1 of the target node. It uses only:
- the Steinberg relations;
- Whitehead's lemma, with its explicit block factorization written in step (c);
- row reduction over the field `Q`.

Outline:
- (a) Kernel elements coming from a lower rank are central.
- (b) The doubling `ψ(r) = (y_s r x_t)` induces `Φ : St_N(S) -> St_2N(S)`, which doubles
  `St_N(Q)` diagonally.
- (c) `W = [[𝒴,0],[0,𝒳]] ∈ GL_3N(S)` conjugates `diag(A, I_2N)` to `diag(𝒴A𝒳, I_N)`.
- (d) Two lifts of the same homomorphism from the perfect group `St_N(S)` agree in
  rank `6N+1`.
- (e) So `z = z · ŝ_τ(z)` for `z ∈ K_2(N,Q)`.
- (f) Hence the index-shifted image of `K_2(N,Q)` is trivial.

Three referee reports PASS it (see `artifacts`).
