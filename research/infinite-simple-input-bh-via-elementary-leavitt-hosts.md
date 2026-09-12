---
rg: 2
id: infinite-simple-input-bh-via-elementary-leavitt-hosts
kind: route
title: Put the simple input in the units of an algebraic host and take the elementary group of its Leavitt tensor
target: infinite-simple-input-boone-higman
requires:
  - simple-inputs-have-fp-elementary-leavitt-tensor-hosts
  - leavitt-tensor-elementary-host-criterion
artifacts:
  - research/artifacts/bh-decidable-algebra-hosts-2026-09-12.md
---

Let `S` be infinite, finitely generated, computably presented and simple.

1. **Take the host.** `simple-inputs-have-fp-elementary-leavitt-tensor-hosts`
   gives `B`, an embedding `S -> B^x`, and `n >= 4` with finitely normally
   generated kernel `ker(St_n(B ⊗ L) -> E_n(B ⊗ L))`.
2. **`S` is perfect.** An abelian simple group is cyclic of prime order, so an
   infinite simple group is nonabelian, hence `[S,S] = S`.
3. **Apply the criterion.** `leavitt-tensor-elementary-host-criterion` makes
   `E_n(B ⊗ L)` a finitely presented simple group containing `S`.

Through `boone-higman-from-infinite-simple-inputs` this route reaches
`boone-higman-conjecture`. Its only open input is the host existence premise.
