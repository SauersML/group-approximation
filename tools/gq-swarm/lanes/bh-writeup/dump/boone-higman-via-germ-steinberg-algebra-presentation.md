---
rg: 2
id: boone-higman-via-germ-steinberg-algebra-presentation
kind: route
title: Prove Boone--Higman by finitely presenting the germ-groupoid Steinberg algebra of a shell envelope instead of the envelope itself
target: boone-higman-conjecture
requires: [boone-higman-iff-infinite-simple-inputs, shell-cantor-embeddings-are-finite-germ-extensions, germ-steinberg-algebras-over-v-are-fg-central-simple, shell-germ-steinberg-algebra-is-finitely-presented, leavitt-tensor-elementary-host-criterion]
---

Let `G` be finitely generated with solvable word problem.

1. By `boone-higman-iff-infinite-simple-inputs` it suffices to embed an infinite finitely
   generated computably presented simple group `S` (hence perfect) in a finitely presented
   simple group.
2. Choose a bijection `nu : S -> N` and form the shell envelope
   `E_nu = <V, hat(S)> <= Homeo(C)` of
   `shell-cantor-embeddings-are-finite-germ-extensions`. It is finitely generated when `S`
   is, contains `V`, and acts minimally and faithfully.
3. Let `G_nu` be the germ groupoid and `A = A_(F_2)(G_nu)`. By
   `germ-steinberg-algebras-over-v-are-fg-central-simple`, `A` is a finitely
   generated central simple `F_2`-algebra and `S <= E_nu <= A^x`.
4. By `shell-germ-steinberg-algebra-is-finitely-presented` (OPEN), choose `nu` so that `A`
   is finitely presented as an `F_2`-algebra.
5. Put `R = A ⊗ L_(F_2)(1,2)`. Assume `ker(St_n(R) -> E_n(R))` is finitely normally
   generated for some `n >= 4`. By `leavitt-tensor-elementary-host-criterion`, `E_n(R)` is a
   finitely presented simple group containing `S`, hence containing `G`.

So Boone--Higman follows from step 4 together with the kernel hypothesis of step 5.

## Where the two open steps sit

- **Step 4** is the algebra gate. It replaces finite presentation of the *group* `E_nu`
  (`perfect-decidable-inputs-have-fp-shell-envelopes`) by finite presentation of an
  *algebra* built from the same action. Neither is known to imply the other.
- **Step 5** is the standing kernel condition of the Leavitt-tensor route. It is automatic
  when `K_1(R) = K_2(R) = 0`, for instance when `A` is regular supercoherent
  (`ara-cortinas-leavitt-tensor-k-theory-vanishes`, imported there). Whether a germ-groupoid
  Steinberg algebra of a shell envelope is regular supercoherent is not addressed on main;
  for `A = L_(F_2)(1,2)` itself it is.

## Why this is not a restatement of the route it replaces

If step 4 held for the group instead, step 2 would already give a finitely presented simple
group, by `perfect-input-shell-envelopes-are-simple`, and the algebra would be unnecessary.
The point of the exchange is that algebra relators may be multiplied by the cylinder
idempotents of `C(C, F_2)`, so relations that hold only near the singular point are
expressible, and the relations of the `V`-part are already compressed into the two Leavitt
relations of `L_(F_2)(1,2) <= A`.

## What would collapse it

A proof that finite presentation of `A_(F_2)(G_Γ)` forces finite presentation of `Γ`, or
of the germ group `(Γ)_p`, would make this route equivalent to the group gate. Nothing on
main does that; the SingFix consequence
(`bhm-singfix-condition-forces-fp-germ-groups`) is about the group hypothesis of
Belk--Hyde--Matucci Theorem 2.1, not about the algebra.
