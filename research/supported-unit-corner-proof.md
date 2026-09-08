---
rg: 2
id: supported-unit-corner-proof
kind: route
title: Shrink the fixed idempotent and return the two-coordinate Whitehead matrix
target: supported-unit-commutators-lie-in-corner-units
requires: []
artifacts:
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsStepOne.lean
  - GroupApproximation/Algebra/PurelyInfiniteMatrixEmbedding.lean
  - GroupApproximation/Algebra/CornerUnitExtension.lean
  - GroupApproximation/KOne/BlockWhitehead.lean
---

Every nonzero idempotent e is infinite. To see this from the repository's
right-ideal definition, take an infinite idempotent p=er. Then ep=p, pe
is an idempotent below e, and pe is equivalent to p via (p,e). Thus pe is
infinite. If an infinite idempotent q below e splits as q=f+g with q~f
and g nonzero, extend a normalized equivalence q~f by the orthogonal
identity e-q. This gives e~f+(e-q), with nonzero complement g, so e is
infinite as well. All these equivalences preserve the required two-sided
supports.

Choose e=f+g with f~e, g nonzero, and normalized a,b in eRe satisfying
ba=e and ab=f. Then ga=0 and bg=0. Sandwich g to the unit: choose x,y
with xgy=1. Set

    s0=1-e+a, t0=1-e+b, s1=gy, t1=xg.

Direct multiplication gives t_i s_j=delta_ij. In particular P=s0t0+s1t1
is idempotent. The map theta(A)=sum s_i A_ij t_j is a unital ring map
from M_2(R) to PRP, and

    Phi(A)=1-P+theta(A)

defines a group homomorphism GL_2(R)->R^x. Its inverse formula on unit
values is 1-P+theta(A^{-1}); the cross terms vanish because both theta
values lie in PRP.

Whitehead's two-coordinate identity gives diag([u,w],1) in EL_2(R) for
all units u,w. The preimage of EL_2(R) under the diagonal homomorphism
is a subgroup containing these commutators, so it contains [R^x,R^x].
Consequently diag(v,1) is elementary.

The supported form of v gives ev=ve=e. It follows that
s0 v t0=v-e+f, while s0t0=1-e+f. Therefore

    Phi(diag(v,1))=1-(s0t0+s1t1)+(s0 v t0+s1t1)=v.

The restriction of Phi to EL_2(R) is an admissible corner-unit family:
pure infiniteness supplies a proper isometry for the unit of R and
simplicity makes its nonzero complementary idempotent full. Hence its
image, including v, lies in the defined corner-unit subgroup.

For the manuscript's `AGPStepOne`, the hypotheses kappa(v)=1 and
ker(kappa)=[R^x,R^x] supply exactly v in the commutator subgroup used
above. The proof needs neither surjectivity of kappa nor a stabilization
rank depending on v.
