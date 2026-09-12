---
rg: 2
id: twisted-c-star-opposite-inverts-cocycle
kind: claim
title: Passing to the opposite twisted group C-star algebra inverts the multiplier
distinct_from:
  sp4-mod3-twisted-fibres-have-llp: that is the remaining lifting-property claim for the Deligne fibre; this identifies its two nontrivial fibres and reduces them to one question.
  thom-central-corner-criterion: that decomposes a finite central extension into character fibres for Connes embeddability; this is an exact opposite-algebra symmetry and applies to LLP.
---

For every discrete group `G` and normalized circle-valued multiplier `alpha`,

```text
C^*(G,conj(alpha)) ~= C^*(G,alpha)^op.                 (TOP1)
```

The isomorphism sends the canonical `conj(alpha)`-projective generator at
`g` to the opposite of the adjoint of the canonical `alpha`-projective
generator at `g`.  Consequently the local lifting property holds for one
algebra in `(TOP1)` if and only if it holds for the other.

For the `mu_3`-valued Deligne multiplier, `conj(alpha)=alpha^2`.  Hence its
two nontrivial mod-three twisted fibres are opposite C-star algebras and the
two LLP questions in `sp4-mod3-twisted-fibres-have-llp` are one and the same
open problem.
