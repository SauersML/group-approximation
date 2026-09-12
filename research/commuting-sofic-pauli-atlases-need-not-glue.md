---
rg: 2
id: commuting-sofic-pauli-atlases-need-not-glue
kind: claim
title: Two marked sofic Pauli atlases need not admit a common chart
distinct_from:
  commuting-sofic-actions-need-not-combine: that is the underlying counterexample for set actions; this lifts each restriction to maximally separated shared-center Pauli microstates and proves that the two Pauli chart systems cannot be synchronized.
  sofic-action-gives-marked-pauli-central-product-microstates: that is the forward construction for one sofic action; this applies it twice to commuting restrictions whose combined action is not sofic.
  lamp-charts-recover-set-action: that is the general chart-to-set transfer lemma; this uses it contrapositively to forbid a common chart even though both restricted marked models exist.
artifacts:
  - research/artifacts/gkp-2401-04945-verified.md
  - research/artifacts/sofic-action-pauli-central-product-microstates-2026-08-30.md
---

There are a countable sofic group `G`, a countable set `Y), and two
commuting free sofic actions

~~~text
alpha_1:G action Y,              alpha_2:G action Y                 (PAG1)
~~~

with the following properties.  Put

~~~text
P_Y=F_2^(Y) x F_2^(Y) x F_2,
(u,v,e)(u',v',e')=(u+u',v+v',e+e'+<v,u'>),
J=(0,0,1).                                                     (PAG2)
~~~

Each `alpha_i` permutes both Pauli coordinates and fixes `J).  For
`i=1,2`, the semidirect product

~~~text
P_Y semidirect_(alpha_i) G                                     (PAG3)
~~~

is sofic and has sofic approximations in which the normalized Hamming
distance from `J` to the identity is exactly one at every stage.

Nevertheless the two marked chart systems cannot be synchronized.  The
combined automorphism action

~~~text
beta:G times G action P_Y                                      (PAG4)
~~~

has no sofic-`C` action chart in the sense of
Alekseev--Bradford Definition 4.23, for **any** target class `C).
Equivalently, no common finite carrier can simultaneously support the two
Pauli label families with approximately multiplicative actor permutations
and the exact covariance equations on every prescribed finite window.

The witness is the Kun--Thom diagonal-coset construction

~~~text
Y=(G times G)/Delta Gamma.                                     (PAG5)
~~~

The two coordinate actions are free and sofic, while their combined
`G times G` action is not sofic.  The individual marked models follow
from the Pauli chart construction.  A common chart for `beta` would,
by reading either named single-site Pauli generator on each carrier, give a
sofic chart for the combined set action on `Y), a contradiction.

Thus naming both Pauli coordinates does not supply a formal
common-chart theorem: common-chart gluing already fails in the purely
permutation regime, before Hilbert--Schmidt multiplicity enters.  This is
the Pauli form of the negative answer to Gao--Kunnawalkam
Elayavalli--Patchell Question 4.2.

The conclusion concerns chartable models, not arbitrary unitary
microstates.  It does not prove that the combined Pauli semidirect product
is nonhyperlinear.  A hyperlinear model may be non-Cartan and admit no
finite carrier from which Pauli labels can be read; excluding exactly those
models is the still-open quantum-to-classical converse adjacent to GKP
Theorem 3.8 and Question 4.4.

DERIVATION
kun-thom-diagonal-pauli-common-chart-obstruction
