---
rg: 2
id: affine-leavitt-profile-checkpoint-proof
kind: route
title: Enumerate finite table diagrams and apply Gowers--Hatami exactification
target: affine-leavitt-profile-computable-checkpoints
requires:
  - affine-leavitt-steinberg-mark-is-fd-invisible
  - leavitt-prefixes-form-exponential-heisenberg-packet
  - leavitt-steinberg-quadratic-radius-pressure
  - gowers-hatami-finite-group-hs-stability
---

Each finite multiplication-table word `(ALP2)` is known to be null because
the packet embeds in `Gamma_A`. Enumeration of formal consequences of a
finite presentation is complete, so the parallel search terminates and
computes `B_n`. A van Kampen diagram of area at most `B_n` telescopes to
all-pairs defect at most `B_n epsilon_n=.01`.

Apply `gowers-hatami-finite-group-hs-stability`. If the exactified central
element were the identity, its compression would be the identity, contrary
to marked distance at least one and the `.42` comparison bound. The marked
exact sector is therefore nonzero and has dimension divisible by `p^(2^n)`
by the Heisenberg packet theorem. The flexible dimension estimate gives
`(ALP4)`.
