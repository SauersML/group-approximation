---
rg: 2
id: essential-shell-germ-leavitt-tensors-have-fng-steinberg-kernels
kind: claim
title: If an essential shell germ algebra A_nu/J is finitely presented, then its Leavitt tensor has a finitely normally generated unstable Steinberg kernel at some rank n >= 4
distinct_from:
  leavitt-tensor-steinberg-kernel-is-stable-k2: that relates the unstable kernel to stable K_2 over an arbitrary B tensor L_2; this asks for finite normal generation for the specific essential shell germ algebras.
  simple-inputs-have-fp-elementary-leavitt-tensor-hosts: that asks for a host algebra and the kernel condition together, for some host; this fixes the host as A_nu/J and isolates the kernel condition.
  simple-inputs-have-fp-essential-shell-germ-algebras: that is the finite presentation gate on A_nu/J; this is the Steinberg kernel gate on its Leavitt tensor, which does not follow from finite presentation.
---

**OPEN.**

Let `P` be an infinite finitely generated perfect group, `nu : P -> N` a computable bijection, and
`B = A_nu/J` the essential shell germ algebra of `shell-germ-essential-algebras-are-central-simple`.
Put `R = B ⊗ L_(F_2)(1,2)`. The claim: if `B` is finitely presented, then for some `n >= 4` the kernel
`ker(St_n(R) -> E_n(R))` is finitely normally generated in `St_n(R)`.

## Role

This is the second universal hole of `boone-higman-via-essential-shell-germ-algebras`. In
`boone-higman-via-germ-steinberg-algebra-presentation` it appears only as the phrase "Assume ...
for some `n >= 4`" in step 5. It is not in that route's `requires`, so the frontier counts that
route as having one open prerequisite when it has at least two.

## How it can fail independently

- It is automatic when `K_1(R) = K_2(R) = 0`, for instance when `B` is regular supercoherent
  (`ara-cortinas-leavitt-tensor-k-theory-vanishes`). Regular supercoherence of `A_nu/J` is not
  addressed anywhere on main. `A_nu/J` contains the zero divisors of the cylinder idempotents,
  and nothing forces it to be regular.
- A single finitely presented `A_nu/J` whose tensor has infinitely generated `K_2`, in the stable
  range where `leavitt-tensor-steinberg-kernel-is-stable-k2` identifies the kernel with `K_2`,
  would refute it. This is independent of the finite presentation gate
  `simple-inputs-have-fp-essential-shell-germ-algebras`.

## Attempts

1. **Through vanishing K-theory (swarm-0917-w17-bh-last1, 2026-09-19).** *Deferred at regularity.*
   `ara-cortinas-leavitt-tensor-k-theory-vanishes` would give `K_1 = K_2 = 0`, and so a trivial
   kernel in the stable range, if `A_nu/J` were regular supercoherent. No shell envelope with a
   nontrivial input is known to have a regular `A_nu/J`, and none is known to have a finitely
   presented one. So the attack waits on hole 1 of `boone-higman-via-essential-shell-germ-algebras`.
