---
rg: 2
id: boone-higman-via-essential-shell-germ-algebras
kind: route
title: Prove Boone--Higman from a universal finite presentation gate on essential shell germ algebras A_nu/J and a Steinberg kernel gate on their Leavitt tensors
target: boone-higman-conjecture
requires: [boone-higman-iff-infinite-simple-inputs, shell-cantor-embeddings-are-finite-germ-extensions, shell-germ-essential-algebras-are-central-simple, simple-inputs-have-fp-essential-shell-germ-algebras, essential-shell-germ-leavitt-tensors-have-fng-steinberg-kernels, leavitt-tensor-elementary-host-criterion]
---

Let `G` be finitely generated with solvable word problem.

1. By `boone-higman-iff-infinite-simple-inputs` it suffices to embed an infinite finitely
   generated computably presented simple group `S` in a finitely presented simple group. `S` is
   perfect.
2. By `simple-inputs-have-fp-essential-shell-germ-algebras` (OPEN), choose a computable `nu` with
   `B = A_nu/J` finitely presented. Here `E_nu = <V, hat(S)>` is the shell envelope of
   `shell-cantor-embeddings-are-finite-germ-extensions`, `A_nu` is the Steinberg algebra of its germ
   groupoid over `F_2`, and `J` is the singular ideal.
3. By `shell-germ-essential-algebras-are-central-simple`, `B` is central simple and
   `S <= E_nu <= B^x`.
4. By `essential-shell-germ-leavitt-tensors-have-fng-steinberg-kernels` (OPEN), for some `n >= 4`
   the kernel `ker(St_n(B ⊗ L_(F_2)(1,2)) -> E_n(B ⊗ L_(F_2)(1,2)))` is finitely normally
   generated.
5. By `leavitt-tensor-elementary-host-criterion`, applied to the finitely presented central
   simple `B` and the perfect subgroup `S <= B^x`, `E_n(B ⊗ L_(F_2)(1,2))` is a finitely
   presented simple group containing `S`, hence `G`.

## Why this replaces the older encoding

**Distinct from `boone-higman-via-germ-steinberg-algebra-presentation`.** That route lists as its only open prerequisite the EXISTENTIAL gate `shell-germ-steinberg-algebra-is-finitely-presented` (some perfect P, some nu, A_nu finitely presented). It uses A_nu, which is never simple, as the host, and it keeps the Steinberg kernel condition outside `requires`. This route states the same idea with the quantifier the argument needs, with A_nu/J as the host, and with both gates as prerequisites.

`boone-higman-via-germ-steinberg-algebra-presentation` has three encoding defects. Each of them
would let a proof of its one open prerequisite flip `boone-higman-conjecture` to ESTABLISHED
without the argument supporting it. `bin/cairn impact shell-germ-steinberg-algebra-is-finitely-presented`
does list `boone-higman-conjecture` among the flips.

- **Quantifier.** Its step 4 is used for the given simple `S`, but the prerequisite it cites
  asserts finite presentation only for some perfect `P` and some `nu`. Even one such `P` gives
  nothing for other inputs.
- **Host.** Step 5 applies `leavitt-tensor-elementary-host-criterion`, which needs a central
  simple algebra, to `A_nu`. But `shell-germ-steinberg-algebras-are-never-simple` shows `A_nu` is
  not simple for any `nu`. The in-text correction moves to `A_nu/J`. That needs finite
  presentation of `A_nu/J`, and this is not in `requires`: neither the ideal condition nor the
  quotient gate is listed.
- **Kernel.** The finite normal generation of the Steinberg kernel is assumed in the text of step
  5 but is not a prerequisite.

This route has exactly two open prerequisites. Each can fail without the other, as recorded in
their "How it can fail independently" sections.

## What is already known to constrain the holes

- Hole 1 forces, for each simple input, a finitely presented local algebra `K[Q_nu]/J_p`
  (`shell-germ-quotient-algebra-fp-forces-fp-local-algebra`).
- The path through finite presentation of `A_nu` forces a finitely presented germ group `Q_nu`
  (`shell-germ-algebra-fp-forces-fp-germ-group`). That is the germ half of the shell group gate,
  and generic enumerations are excluded (`generic-shell-germ-algebras-are-not-finitely-presented`).
  So hole 1 has to be met either in `A_nu/J` directly or by a non-generic `nu` with finitely
  presented germ group, for every simple input.
- The two holes together imply `simple-inputs-have-fp-elementary-leavitt-tensor-hosts`, with the
  host fixed as `A_nu/J`. So this route is a specialization of the Leavitt tensor host route.
  Closing both holes is at least as hard as closing that route's hole. What the specialization
  offers is an explicit candidate host, not a weaker hypothesis.
