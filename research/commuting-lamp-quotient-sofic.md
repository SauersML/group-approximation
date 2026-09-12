---
rg: 2
id: commuting-lamp-quotient-sofic
kind: claim
title: The commuting-lamp witness quotient is sofic
distinct_from:
  sofic-non-mf-witness: That is soficity of the Clifford witness `W` itself, whose lamp kernel is the signed group `ClLamp(X)`; this is soficity of `W/<zeta>`, and soficity does not pass to quotients, so it needs its own argument.
  literal-mark-quotient-sofic: That is soficity of `E/<w>`, whose lamp kernel is a free product of `(Z/2)^8` blocks; here the blocks have been collapsed and the lamp kernel is a single elementary abelian group, which is why this one is locally finite and that one is not.
  commuting-lamp-quotient-not-mf: That is the operator-norm failure for the same group; this is the permutation-microstate property, and the two together are what make the group interesting.
artifacts:
  - GroupApproximation/Sofic/CommutingLampQuotientSofic.lean
  - non_mf_groups_exist.tex
---

`W/<zeta>`, the Clifford witness modulo its central sign, is sofic.

With `commuting-lamp-quotient-not-mf` this makes `W/<zeta>` an explicit
finitely generated **sign-free** sofic group that is not MF: the example
behind Theorem E needs no Clifford sign at all.

Killing `zeta` abelianizes the lamp kernel — `ClLamp(X)/<zeta>` is the
elementary abelian `X ->_0 Z/2` under the same vertical action — so the
group is `(X ->_0 Z/2) semidirect V`, and the sofic permanence pipeline that
proves `sofic-non-mf-witness` replays on it unchanged: finite site orbits of
a telescope level give finite invariant lamp windows, the local
finite-kernel criterion applies, and the integer shift is adjoined by the
sofic-by-cyclic extension theorem.

Machine-checked at
`CommutingLampQuotientSofic.literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF`,
which returns both halves at once.  Printed in `thm:commutinglamp` of
`non_mf_groups_exist.tex`.
