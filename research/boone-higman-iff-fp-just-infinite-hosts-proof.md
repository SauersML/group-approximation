---
rg: 2
id: boone-higman-iff-fp-just-infinite-hosts-proof
kind: route
title: Simple targets are just-infinite; conversely feed the Thompson simple envelope to the host and apply the structure lemma
target: boone-higman-iff-fp-just-infinite-hosts
requires: [boone-higman-thompson-simple-envelope, just-infinite-over-simple-subgroup-gives-fp-simple-host]
---

**1 ⇒ 2.** Let `G` be infinite, finitely generated, with solvable word problem. By
statement 1, `G ≤ T` with `T` finitely presented and simple. `T` is infinite
because `G` is. An infinite simple group is just-infinite: its only nontrivial
normal subgroup is itself, which has index 1, and it is infinite.

**2 ⇒ 3.** Statement 3 is a special case of statement 2.

**3 ⇒ 1.** Let `G` be finitely generated with solvable word problem. By
`boone-higman-thompson-simple-envelope`, `G ≤ S` where `S` is finitely generated,
computably presented and simple. The body of that claim records two free
refinements: `S` may be taken infinite (apply the theorem to `G × Z`), and `S` has
decidable word problem. So `S` is an infinite finitely generated simple group with
solvable word problem. By statement 3, `S ≤ Γ` with `Γ` finitely presented and
just-infinite.

Apply `just-infinite-over-simple-subgroup-gives-fp-simple-host` to `S ≤ Γ`. Its
hypothesis holds because `Γ` is just-infinite: every nontrivial normal subgroup of
`Γ` has finite index. `Γ` is finitely presented, so clause 3 of that claim gives a
finitely presented infinite simple group `T`, and clause 2 embeds `S` in `T`. Hence
`G ≤ S ↪ T`, which is statement 1 for `G`. ∎

**Remark (what is lost).** Only "just-infinite above `<<S>>`" is used in 3 ⇒ 1.
So statement 3 may be weakened further: it suffices that every nontrivial normal
subgroup of `Γ` inside the normal closure of `S` has finite index.
