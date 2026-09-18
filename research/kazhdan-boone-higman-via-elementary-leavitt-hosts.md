---
rg: 2
id: kazhdan-boone-higman-via-elementary-leavitt-hosts
kind: route
title: Put an infinite simple envelope of the input in an elementary Leavitt tensor host, which is automatically Kazhdan
target: kazhdan-boone-higman-conjecture
requires:
  - boone-higman-thompson-simple-envelope
  - simple-inputs-have-fp-elementary-leavitt-tensor-hosts
  - leavitt-tensor-elementary-host-criterion
  - ring-elementary-bh-hosts-are-kazhdan
artifacts:
  - research/artifacts/ring-hosts-are-kazhdan-2026-09-17.md
---

Let `G` be finitely generated with solvable word problem.

1. **Simple envelope.** Apply `boone-higman-thompson-simple-envelope` to
   `G × Z`. This embeds `G` in an infinite, finitely generated, computably
   presented simple group `S`. Here `S` is infinite because it contains `Z`.
2. **Host.** `simple-inputs-have-fp-elementary-leavitt-tensor-hosts` gives
   three things:
   - a finitely presented `F_2`-algebra `B`;
   - an embedding `S -> B^x`;
   - an `n >= 4` for which `ker(St_n(B ⊗ L) -> E_n(B ⊗ L))` is finitely
     normally generated, where `L = L_(F_2)(1,2)`.
3. **Finite presentation and simplicity.** `S` is infinite and simple, so it
   is nonabelian and perfect. `leavitt-tensor-elementary-host-criterion` then
   makes `E_n(B ⊗ L)` a finitely presented simple group containing `S`, and
   hence containing `G`.
4. **(T).** `ring-elementary-bh-hosts-are-kazhdan`(2) says that `E_n(B ⊗ L)`
   has property (T).

Hence `G` embeds in a finitely presented simple Kazhdan group. The only open
input is the host existence premise of step 2.
