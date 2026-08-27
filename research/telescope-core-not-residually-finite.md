---
rg: 2
id: telescope-core-not-residually-finite
kind: claim
title: The telescope core is LEF but not residually finite
distinct_from:
  literal-telescope-core-lef: That claim is the positive half — every finitely generated subgroup of `E_T` is residually finite; this one is the negative half, that `E_T` itself is not, which is exactly what makes the word "locally" there necessary rather than an artifact of the proof.
  marked-quotients-not-lef: That claim rules out local embeddings for the four groups containing the stable letter, using the compression relations; this one is about `E_T`, which has no stable letter, is LEF, and fails only the global property.
  literal-mark-quotient-finite-residual: That computes the finite residual of `E/<w>`, a quotient of the whole group containing the stable letter; this one records that the same collapse already happens in the stable-letter-free core, driven by 2-divisibility of the telescope rather than by conjugation by `tau`.
  finite-quotient-blindness: That says a finite quotient normalizes the image of the base, and its mechanism is conjugation by the stable letter; this claim's mechanism needs no stable letter at all and applies to a group that does not contain one.
  literal-group-sofic: That is soficity of `E`; this is a residual-finiteness failure one level down, and it is what forces the soficity proof to be local.
  lamp-telescope-base-is-lef: That claim is the positive LEF property for the WITNESS bases `ClLamp(X) semidirect T` and `F_2[X] semidirect T`, whose lamp kernels are locally finite; this claim is about the LITERAL core `N_E semidirect T`, whose lamp kernel is a block amalgam containing free subgroups, and its content is the negative half — that LEF cannot be upgraded to residual finiteness.
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
  - non_mf_groups_exist.tex
---

Let `E_T = N_E semidirect T` be the telescope core of the literal group, the
kernel of the stable-letter exponent `E -> Z`.  Then `E_T` is LEF — every
finitely generated subgroup is residually finite
(`literal-telescope-core-lef`) — but `E_T` is **not** residually finite: every
homomorphism from `E_T` to a finite group kills the marked involution `w`,
which is nontrivial by `prop:witness`.

The mechanism needs no stable letter.  Level collapse in a finite quotient is
usually derived from conjugation by `tau` (`finite-quotient-blindness`), and
`tau` is not in `E_T`; but `phi(T) = phi(Gbar)` already holds in every finite
quotient of `T` alone, because `Z[1/2]^3` is 2-divisible.

Two consequences worth stating.

* The word "locally" in `literal-telescope-core-lef` is necessary.  The
  positive half is optimal: one cannot strengthen it to residual finiteness of
  `E_T`.
* It makes the directed-union step of the soficity proof concrete rather than
  merely formally valid.  `w` is nontrivial in every block window `M_J`, and in
  every sufficiently fine finite quotient of every `M_J semidirect Gamma_n`,
  yet `w` dies in every finite quotient of the union `E_T`.  A directed union
  of residually finite groups need not be residually finite, and here it
  demonstrably is not — which is why the soficity argument approximates windows
  and never the whole core.
