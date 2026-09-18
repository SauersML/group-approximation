---
rg: 2
id: fg-linear-groups-embed-in-fp-self-similar-groups
kind: claim
title: Every finitely generated linear group, over any field, embeds in a finitely presented self-similar group
distinct_from:
  char-zero-linear-pbh-via-polynomial-self-similar-hosts: that route uses the finitely presented self-similar affine host only as a step toward permutational Boone--Higman in characteristic zero; this records the host itself, in every characteristic, as the answer to a printed question.
  finitely-generated-linear-groups-satisfy-boone-higman: that is the simple-envelope conclusion; this is the intermediate self-similar embedding, which is what Llosa Isenrich--Schesler--Wu ask for.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED (lane proof by composition of nodes on main; not independently
reviewed as a composition; no priority claimed).**

**Printed question.** C. Llosa Isenrich, E. Schesler, X. Wu, *Infinitely presented
simple groups separated by homological finiteness properties*, arXiv:2510.01952v1,
Question 1.11 (TeX label `quest:embedding`, l.302–304; numbering consistent with
main's records of Question 1.10 at l.289 and Question 1.12 at l.309):

> Does every finitely generated linear group embed into a finitely generated
> self-similar group?

**Answer: yes, even into a finitely presented one.** Let `K` be a field and
`H ≤ GL_n(K)` finitely generated.
- **Characteristic 0.** Steps 1–4 of `char-zero-linear-pbh-via-polynomial-self-similar-hosts`
  give an injective homomorphism `H → E_N(R)` with `R = Z[1/m][s_1,…,s_k]`, and
  `G = R^N ⋊ E_N(R)` is finitely presented
  (`elementary-groups-over-polynomial-s-integers-are-fp`,
  `affine-extension-of-fp-elementary-group-is-fp`) and acts faithfully and
  self-similarly on a rooted regular tree
  (`polynomial-parameter-affine-groups-are-self-similar`).
- **Characteristic p.** Steps 1–4 of `char-p-linear-pbh-via-polynomial-self-similar-hosts`
  give the same with `R = F_p[s_1,…,s_k]`, using
  `elementary-groups-over-polynomial-f-p-rings-are-fp`,
  `affine-extension-of-fp-elementary-group-is-fp` and
  `positive-char-polynomial-affine-groups-are-self-similar`.

In both cases `H ≤ E_N(R) ≤ G`, and `G` is a finitely presented (so finitely
generated) self-similar group in the sense used by LISW and by Zaremsky
(arXiv:2405.09722, Definition 2.1: every state of every element lies in the group).

**Trust surface.** The composed chain was adversarially re-checked end to end by
lane bh-verify-linear (`research/artifacts/gq-bh-bh-verify-linear-report.md`,
ac8c87777) and bh-verify-metabelian (05d6a15ff); both are internal checks. LISW
Theorem 1.4 already covers subgroups of `GL_n(Q)` by self-similar split extensions;
the question as printed is for arbitrary fields. A MathSciNet/zbMATH priority check
has not been done.
