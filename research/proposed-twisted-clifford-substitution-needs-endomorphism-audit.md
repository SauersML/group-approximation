---
rg: 2
id: proposed-twisted-clifford-substitution-needs-endomorphism-audit
kind: claim
title: The twisted binary Clifford formula has unresolved square, relator, and equivariance obligations
artifacts:
  - experiments/renormalization_transport_audit.py
  - research/artifacts/renormalization-stable-letter-audit-2026-08-20.md
distinct_from:
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that rules out changing finite packet multiplicity by conjugacy; this audits whether the proposed map is an endomorphism at all.
  untwisted-sign-replication-flips-minus: that diagnoses one sign-replication formula; this gives the general three-factor square law and also records the independent tree-equivariance obligation.
  ascending-hnn-cannot-create-nonhyperlinearity: that assumes a genuine injective endomorphism and proves the resulting HNN step preserves hyperlinearity; this records why the proposed formula has not yet reached that premise.
---

The schematic formula

```text
t u_k t^(-1)=v_k u_(2k+1) u_(2k)                         (TCS1)
```

does not by itself define an ascending HNN extension.  Before Britton's lemma
can preserve the base and the mark, one must prove that the right-hand words
define an injective endomorphism of the **specified** base presentation.

Already the square relation depends on omitted data.  If the three factors
in `(TCS1)` pairwise anticommute by a central involution `J` and have squares
`J^s_v,J^s_1,J^s_2`, then

```text
(v_k u_(2k+1) u_(2k))^2=J^(s_v+s_1+s_2+1).               (TCS2)
```

Thus three involutive factors square to `J`, while three `J`-square factors
square to `1`; neither preserves the corresponding uniform source-square
convention.  A mixed convention can repair `(TCS2)`, but it must be declared
and then checked against every commutator relation.

Independently, transporting one base-site relation through Thompson
transitivity is not automatically compatible with binary parent-child
incidence.  One must specify the acting subgroup, prove that its relators
preserve the substitution, prove all transported definitions agree, and
prove injectivity.  Proper image dimension on one finite window proves none
of these global statements.  The proposed `G_subst` therefore is not an
established finitely presented ascending HNN extension.  Moreover, even if
this audit is passed, `ascending-hnn-cannot-create-nonhyperlinearity` shows
that the stable-letter step cannot be the first source of nonhyperlinearity.
