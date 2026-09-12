---
rg: 2
id: bffhz-action-image-is-finitely-presented
kind: claim
refuted_by: [bffhz-computable-core-fp-upgrade-is-false]
title: The automorphism group of S free-producted with a free group, modulo its action kernel, is finitely presented for a computably presented simple S
distinct_from:
  torsion-free-finitely-presented-non-mf: that asserts the existence of a torsion-free finitely presented group failing MF in the norm-matrix-corona sense; this asks whether one specific automorphism-action quotient is finitely presented, and carries no approximation property, no torsion hypothesis and no existence quantifier over groups.
  boone-final-group-finitely-presented: that is the established finite presentability of the final group of the Boone HNN tower over a fixed base; this is finite presentability of a permutation quotient of the automorphism group of a free product, and neither construction occurs in the other.
  finitely-presented-nonsofic-group-exists: that is an existence statement about soficity failing in some finitely presented group; this is about finite presentability of one named quotient and says nothing about soficity.
  finitely-presented-sofic-non-mf: that is about the literal forty-one-relator group E and its approximation properties; this is about Aut_S(S*F_n) modulo an action kernel, and the two share only the words "finitely presented".
  literal-group-not-sofic: that is a refuted claim about soficity of the literal group E; this is an open finite-presentation question about a different group and has no approximation content.
  relative-automorphism-action-is-highly-transitive: that establishes the transitivity and stabilizer properties of the action; this universal finite-presentation upgrade is refuted for a computably presented MIF core, while the published question assumes a finitely presented core.
  ck-envelope-has-a-finitely-normally-generated-maximal-kernel: that remains an open finiteness statement about a maximal kernel of a marked Steinberg cover; this universal claim about an automorphism action image has an explicit counterexample.
  twisted-brin-thompson-finite-presentation-criterion: that is the imported criterion this claim would feed; this is the missing hypothesis of that criterion for one specific action.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
  - research/artifacts/boone-higman-relative-automorphism-fp-obstruction-2026-09-08.md
---

Let `S` be an infinite, finitely generated, computably presented simple
group and `n >= 2`.  Put `A = Aut_S(S * F_n)`, `X = Hom_S(S * F_n, S)`, and
`K = ker(A` acting on `X)`.  Then `A/K` is finitely presented.

False. The regular cyclic twisted Brin--Thompson group gives an infinite
finitely generated decidable simple MIF core for which K=1 and A is not
finitely presented. See `bffhz-computable-core-fp-upgrade-is-false`.

## Relation to the published question, which is NOT the same statement

Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2, Question 3.2, read
from source 2026-08-17, verbatim:

> "For G a finitely presented simple group and n≥2, is the quotient of
> Aut_G(G*F_n) by the kernel of its action on Hom_G(G*F_n,G) finitely
> presented?"

Two differences, and both matter.

1. **Their `G` is finitely presented; this claim's `S` is only computably
   presented.**  That is a strictly stronger demand, and it is the whole
   point: finite presentation of the simple core produced by
   `boone-higman-thompson-simple-envelope` is not guaranteed. If it were
   guaranteed, `boone-higman-conjecture` would already follow. The present
   universal claim includes cores which provably are not finitely presented.
2. **The stated payoff is different.**  A positive answer to Question 3.2
   would show finitely presented simple twisted Brin--Thompson groups are
   universal among finitely presented simple groups — their words: "if the
   MIF requirement could be dropped...then we would conclude that finitely
   presented (simple) twisted Brin--Thompson groups are universal among all
   finitely presented simple groups".  It would not, by itself, prove
   Boone--Higman.

So a reader must not conclude that a single published open question stands
between this repository and the conjecture.  The published question is a
special case of this claim, and the case it omits is exactly the hard one.

## Why the proposed upgrade fails

The action and stabilizer conclusions remain true. However,
`relative-automorphism-fp-host-reflects-base-presentation` proves that a
finitely presented subgroup of A containing the canonical translations
would force S to be finitely presented. For an MIF core the action kernel
is trivial, so the faithful action image cannot absorb the missing base
relators. `regular-cyclic-twisted-core-is-decidable-mif-non-fp` supplies
an explicit core meeting every hypothesis of the claim and contradicting
its conclusion. This refutes the universal upgrade, not the published
question with its finitely presented-core hypothesis.

The possibility of selecting a suitable non-MIF core for each input is
not excluded. It would require a different, restricted existence claim;
the universal premise recorded here cannot be used to justify it.

## Attempts

The first four entries record the earlier proposed approaches. The
universal statement they were intended to prove is now refuted.

1. **Higman-embed `A` and induce the action.**  *Dies at oligomorphy and at
   the kernel.*  `A` is finitely generated and computably presented (see the
   effectivity remark on
   `relative-automorphism-action-is-highly-transitive`), so
   Higman embeds it in a finitely presented `P`, and any `A`-set induces to a
   `P`-set — extending the action abstractly is not the difficulty.  But if
   `X ~= A/H` then the induced transitive `P`-set is `P/H`, whose pair-orbits
   are `H \ P / H`, and a generic Higman embedding gives no reason for that
   to be finite.  Worse, the new action's kernel must be trivial or finitely
   normally generated for a finitely presented faithful quotient, which is
   the same obstruction one category over.
2. **Compress by a finite HNN tower, as the Boone tower does.**  *Deferred at
   an identified step.*  This repository's
   `boone-normal-closure-of-t-finitely-generated` shows finite HNN towers can
   turn infinitely generated associated subgroups into finitely generated
   ones by adding finitely many stable letters, which is the right shape of
   mechanism.  But an HNN relation `t^{-1} a t = theta(a)` imposed on a group
   *acting* on a set requires the permutation assigned to `t` to conjugate
   the action of the associated subgroup to the action of its image, and
   letting `t` act trivially works only when those two actions already agree.
   Ordinary Higman/Boone compression provides no such compatibility, and the
   repository's finite-generation theorem does not address it.  The precise
   missing construction is a relative action-Higman theorem: compress into a
   finitely presented acting group while keeping point stabilizers finitely
   generated, pair-orbits finite, the core sharp, and the action kernel
   trivial or finitely normally generated.
3. **Answer the published Question 3.2 first and transfer.**  *Not a route.*
   Its hypothesis is finite presentability of `S`, which is what one is
   trying to produce; a positive answer there gives universality of twisted
   Brin--Thompson groups, not an envelope for a computably presented core.
4. **Form the abstract twisted Brin--Thompson group before quotienting the
   action kernel.**  *Dies at the same finite-presentation hole.*
   `abstract-btb-simple-quotient-fp-gate`,
   imported from Fournier-Facio--Wu--Zaremsky Corollary 4.2, says that once
   the abstract group is finitely presented, its canonical simple quotient is
   finitely presented **if and only if** `A/K` is.  Relative simplicity is a
   genuine new tool, but it cannot compress this kernel for free.
5. **Choose an MIF core to eliminate the kernel.** This exposes the
   finite-presentation obstruction instead: A is finitely presented exactly
   when the finitely generated simple MIF core already is. The regular
   cyclic twisted core supplies the counterexample used for refutation.
