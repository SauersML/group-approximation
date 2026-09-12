---
rg: 2
id: thom-central-corner-criterion
kind: claim
title: Thom's central-corner criterion and central-quotient descent
distinct_from:
  clifford-bernoulli-central-summands: That claim computes the two summands of this repository's specific lamp group by cutting with the sign projection; this is the general published criterion for an arbitrary central subgroup, together with the descent statement that a central quotient of a hyperlinear group is hyperlinear, which the direct-sum computation does not contain.
  central-sign-corona-obstruction: That concerns an obstruction to a central sign in corona representations; this is a positive criterion identifying hyperlinearity with embeddability of all twisted corners.
artifacts:
  - research/artifacts/thom-0810-2180-verified.md
  - notes/PERFECT_CORE_KUN_THOM_WREATH.md
---

Thom, arXiv:0810.2180, **Lemma 3.3** (verified verbatim from the PDF, record
in the artifact): for a group `G` with central subgroup `C` and classifying
cocycle `alpha`,

```text
G is hyperlinear  <=>  L_(beta o alpha)[G/C] embeds into R^omega
                       for every character beta in hat(C).
```

**Remark 3.4**: every quotient of a hyperlinear group by a central subgroup
is again hyperlinear.

Instantiated at `Wtilde=C(X) semidirect G` with `C=<z>`, the two characters
give exactly `L(W)=M_KT` and `Cl(X) crossed_product G`, so the criterion
reproduces `clifford-bernoulli-central-summands` from the literature, and the
descent step supplies the deduction chain

```text
Cl(X) crossed_product G embeddable
  ==> Wtilde hyperlinear (it embeds in U of that algebra)
  ==> W=Wtilde/<z> hyperlinear                    [Remark 3.4]
  ==> with Kun--Thom nonsoficity of W, Question 3.4 is answered.
```

Numbering note: the statements are Lemma 3.3 and Remark 3.4; a circulating
"Lemma 3.4 / Remark 3.5" reference is off by one.  The proof of Lemma 3.3
also uses, as standard, that `G` is hyperlinear iff `L(G)` embeds into
`R^omega`.
