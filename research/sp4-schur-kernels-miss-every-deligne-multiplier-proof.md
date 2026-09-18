---
rg: 2
id: sp4-schur-kernels-miss-every-deligne-multiplier-proof
kind: route
title: Sp4(Z) is linear, so its Schur kernels are torsion and integral Maslov evaluations vanish on them
target: sp4-schur-kernels-miss-every-deligne-multiplier
requires:
  - linear-group-schur-kernels-are-torsion
  - deligne-schur-witness-needs-maslov-carrying-packet
---

The setting and the decomposition `H_2(Gamma; Z) = Z<h> + F`, with `F` finite
and `<e, h> = d != 0`, come from
`deligne-schur-witness-needs-maslov-carrying-packet`. That claim also
identifies Deligne's multiplier as `alpha = e_3`, the reduction mod 3 of the
integral class `e`.

**Item 1.** `Sp_4(Z)` is a finitely generated linear group: it is generated
by elementary symplectic matrices and embeds in `GL_4(C)`. By
`linear-group-schur-kernels-are-torsion`, `K_2(Gamma, w)` lies in
`Tors H_2(Gamma; Z) = F`, which is finite.

**Item 2.** Evaluation of `e` is a homomorphism
`e_H : H_2(Gamma; Z) -> Z`. Since `Z` is torsion-free, `e_H` vanishes on
`F`, and so on `K_2(Gamma, w)`.

For the reductions, evaluation is natural in the coefficient map
`Z -> Z/n`, so `(e_n)_H = (e_H mod n)`. This vanishes on `K_2` as well. It is
the Corollary of `linear-group-schur-kernels-are-torsion` with `B = Z` and
`A = Z/n`.

**Item 3.** This is item 2 with `n = 3`. So `alpha_H(K_2(Gamma, w)) = 0` for
every nonsingular `w`, which is the negation of
`sp4-schur-kernel-meets-the-deligne-triple-class`. It is also incompatible
with (MP1.2) of the packet claim for any `w`: (MP1.2) says that every witness
has rank-one `K_2` with `<e, K_2> = d m Z` and `m >= 1`. ∎
