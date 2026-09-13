---
rg: 2
id: every-fg-rp-group-has-rp-fp-n-hosts-for-each-finite-n
kind: claim
title: "For each finite n, every finitely generated recursively presented group embeds in a recursively presented group of type FP_n"
distinct_from:
  universal-fp-group-embeds-in-rp-fp-infinity-group: that asks for one recursively presented FP_infinity host of a universal finitely presented group; this allows the host to depend on n, and is implied by that claim
  every-type-fn-group-embeds-in-a-type-fn-plus-1-group: that is the homotopical first part of Zaremsky Problem 1.1; this is its homological form, equivalent through Fournier-Facio--Zaremsky Theorem A
---

For every finite `n >= 1` and every finitely generated recursively presented
group `Q` there is a recursively presented group `H_n` of type `FP_n`
containing a copy of `Q`.

This is the homological form of the first part of Zaremsky Problem 1.1. It
gives `every-type-fn-group-embeds-in-a-type-fn-plus-1-group` through
`type-fn-plus-1-hosts-via-rp-fp-n-hosts`, and it follows from that claim
through `rp-fp-n-hosts-from-type-fn-plus-1-hosts`. The cycle records an
equivalence.

## Attempts

- Levels `n = 1, 2` hold: Higman's finitely presented hosts are recursively
  presented and of type `FP_2`. Level 3 is exactly the first half of Question
  1.3 of Fournier-Facio--Zaremsky (arXiv:2607.21727v1) in homological form,
  and it is open.
- The attempts recorded on
  `universal-fp-group-embeds-in-rp-fp-infinity-group` apply level by level:
  the rope trick, the host fence
  `universal-fp-group-hosts-have-unsolvable-word-problem`, and the
  Mayer--Vietoris defect criterion for HNN hosts.
