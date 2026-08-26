---
rg: 2
id: shift-raag-family-is-always-lef-and-sofic
kind: claim
title: The two-generator shift right-angled Artin family is LEF and sofic for every index set
distinct_from:
  centralizing-hnn-over-conjugate-basis-is-always-lef: that is the three-generator centralizing family; this is the two-generator family, so the LEF-versus-residual-finiteness gap is now realized with two generators, the minimum.
  shift-raag-family-is-rf-iff-symmetrized-index-set-closed: that says when the family is residually finite; this says it is always LEF and sofic, so local embeddability and soficity are constant on the family while residual finiteness is Pi-zero-three complete.
---

ESTABLISHED.  For every `J <= Z_{>0}` the group
`G_J = < a, t | [a, t^j a t^-j] = 1, j in J > = A(Gamma_J) x| Z` is
locally embeddable into finite groups and sofic.  Together with
[[shift-raag-family-is-rf-iff-symmetrized-index-set-closed]] and
[[residual-finiteness-two-generator-recursive-is-pi3-complete]], the
two-generator recursive family `G_{J_e}` has constant LEF and sofic
answers while its residual finiteness is `Pi^0_3`-complete.

**Promise corollary.**  Since every group in the hardness family of
[[residual-finiteness-two-generator-recursive-is-pi3-complete]] is LEF
and sofic, residual finiteness remains `Pi^0_3`-hard on two-generator
recursive presentations under the promise that the group is LEF, or
sofic: knowing that a recursively presented group has every finite-model
approximation property does not lower the complexity of deciding whether
it is residually finite.
