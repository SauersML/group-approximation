---
rg: 2
id: zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1
kind: claim
title: "Zaremsky Problem 1.1 resolved: does every group of type F_n (n >= 2) embed in a group of type F_{n+1}, and in a group of type F_infinity?"
root: true
distinct_from:
  every-type-fn-group-embeds-in-a-type-fn-plus-1-group: that is the affirmative answer to the first part only; this is the question, established only when both parts are answered
  every-finitely-presented-group-embeds-in-an-f-infinity-group: that is the affirmative answer to the second part, which also answers the first; this is the question itself
  some-type-fn-group-embeds-in-no-type-fn-plus-1-group: that is the negative answer to the first part, which also answers the second; this is the question itself
  some-finitely-presented-group-embeds-in-no-f-infinity-group: that is the negative answer to the second part only; this is the question, established only when both parts are answered
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 1, verbatim:
"Does every group of type F_n embed in a group of type F_{n+1}, for n ≥ 2?
What about in a group of type F_∞?"

This claim is the question. It is established only through an answer route
that settles both parts:

- **Yes to both**: `zaremsky-1-01-by-yes` requires
  `every-finitely-presented-group-embeds-in-an-f-infinity-group`. An `F_∞`
  host is an `F_{n+1}` host, so the first part follows.
- **No to both**: `zaremsky-1-01-by-no` requires
  `some-type-fn-group-embeds-in-no-type-fn-plus-1-group`. A group with no
  `F_{n+1}` host has no `F_∞` host.
- **Yes, then no**: `zaremsky-1-01-by-mixed` requires
  `every-type-fn-group-embeds-in-a-type-fn-plus-1-group` and
  `some-finitely-presented-group-embeds-in-no-f-infinity-group`.

The fourth combination (no, then yes) is impossible. Never write a
`requires: []` route into this claim.

**Precise reading.** A group is of type `F_n` if it has a `K(G,1)` with finite
`n`-skeleton, and of type `F_∞` if it is of type `F_n` for every `n`. "Embed"
means an injective homomorphism. For `n >= 2`, type `F_n` implies finite
presentability. So:

- Part 1 asks: for every `n >= 2` and every `G` of type `F_n`, is there `H` of
  type `F_{n+1}` containing a copy of `G`?
- Part 2 asks the same with `H` of type `F_∞`. Every finitely presented group
  is of type `F_2`, so Part 2 is equivalent to: does every finitely presented
  group embed in a group of type `F_∞`?

The case `n = 1` is excluded for a reason: a finitely generated group embeds in
a finitely presented group iff it is recursively presented (Higman, *Subgroups
of finitely presented groups*, Proc. Roy. Soc. London Ser. A 262 (1961)), and
there are uncountably many finitely generated groups but only countably many
finitely presented ones.

**Universal forms.** Higman (1961) gives a finitely presented group `U` that
contains a copy of every finitely generated recursively presented group. For
`m` in `{3, 4, ..., ∞}` write `E_m` for "every finitely presented group embeds
in a group of type `F_m`". Then `E_m` holds iff `U` embeds in a group of type
`F_m`. Part 2 is `E_∞`. Part 1 is equivalent to `E_m` for every finite
`m >= 3`: if Part 1 holds, induction gives `U <= K_3 <= K_4 <= ...` with `K_m`
of type `F_m`; conversely a group of type `F_n` is finitely presented, so
`E_{n+1}` gives it an `F_{n+1}` host. At `m = 3` and `m = ∞` these are
Question 1.3 of Fournier-Facio--Zaremsky, arXiv:2607.21727v1 (23 July 2026):
"Does every finitely generated recursively presented group embed in a group of
type F_3? In a group of type F_∞?"

**Status.** Open. Fournier-Facio--Zaremsky, arXiv:2607.21727v1, Introduction:
"A fundamental open question (see [Bes], Q 8.7, [KM], 21.146, [Zar], 1.1, and
the comments to [Ago]) is whether the theorems of Higman and Leary admit
higher-dimensional analogues." Here [Bes] is Bestvina's *Questions in
geometric group theory*, [KM] the Kourovka Notebook, [Zar] this list and [Ago]
MathOverflow question 60565. Their Theorem B
(`higman-rope-trick-group-is-never-fp3`) rules out Higman's rope trick above
`FP_2`. Their Theorem A reduces the affirmative statements to embedding
finitely generated recursively presented groups into recursively presented
groups of type `FP_n`.

## Attempts

- Positive side (lane z1-01-embed-pos): recorded on
  `every-type-fn-group-embeds-in-a-type-fn-plus-1-group` and
  `every-finitely-presented-group-embeds-in-an-f-infinity-group`.
- Negative side (lane z1-01-embed-neg): recorded on
  `some-type-fn-group-embeds-in-no-type-fn-plus-1-group`.
- Homological forms: `universal-fp-group-embeds-in-rp-fp-infinity-group`
  (Part 2) and `every-fg-rp-group-has-rp-fp-n-hosts-for-each-finite-n`
  (Part 1), both equivalent through Theorem A
  (`ffz-rp-fpn-embedding-gives-fp-fn-embedding`).
- Level three, `E_3` (lane z1-01-ffz-fp3):
  `every-finitely-presented-group-embeds-in-an-f3-group`, with its homological
  form `universal-fp-group-embeds-in-an-rp-fp3-group` and the live candidate
  `acyclic-host-twisted-rope-container-is-of-type-fp3`.
