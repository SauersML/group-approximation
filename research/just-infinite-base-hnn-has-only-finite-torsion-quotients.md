---
rg: 2
id: just-infinite-base-hnn-has-only-finite-torsion-quotients
kind: claim
title: Ascending HNN extensions of just-infinite groups have only finite torsion quotients unless the base is finitely presented
---

**ESTABLISHED** (proof in `just-infinite-base-hnn-has-only-finite-torsion-quotients-proof`).

Let `B` be an infinite just-infinite group (every nontrivial normal subgroup
has finite index), `phi: B -> B` an injective endomorphism, and
`Gamma = B*_phi`.

1. If no power `phi^m` (`m >= 1`) is the identity, then every torsion quotient
   of `Gamma` is finite. This holds in particular when `phi` is not surjective.
2. If `Gamma` is finitely presented and `B` is not finitely presented, then
   every torsion quotient of `Gamma` is finite.

So in the finitely presented case, killing the stable letter (or any element
outside the normal closure of `B`) produces an infinite torsion group only if
`B` itself is already a finitely presented infinite group. When `B` is torsion,
that already answers Zaremsky Problem 1.11, so the extension adds nothing.

**Scope.** The Bartholdi–Grigorchuk–Šunić survey states, after its Lemma 5.3
(arXiv:math/0510294, p. 59): "all finitely generated torsion weakly branch
groups are just-infinite branch groups". So item 2 covers every finitely
presented ascending HNN extension of a finitely generated torsion weakly branch
group that is not finitely presented. The survey states that "Branch groups are
probably never finitely presented and this is established for the known
examples" (p. 51). Its Theorem 4.7 proves that finitely generated contracting
regular branch groups are not finitely presented, and its Corollary 4.5 proves
that torsion spinal groups are not. The first Grigorchuk group is worked out in
`grigorchuk-hnn-extension-has-only-finite-torsion-quotients`.
