---
rg: 2
id: amenability-of-finite-presentations-arithmetical-position
kind: claim
title: Amenable finite presentations are Pi-zero-two but not Pi-zero-one, and non-amenable ones are Sigma-zero-two but not recursively enumerable
distinct_from:
  amenability-two-generator-recursive-is-pi2-complete: that is the completeness theorem for recursive presentations; this is the finite-presentation placement, where completeness is open because amenability is incompatible with Higman-type compilers.
  finitely-presented-amenable-undecidable-word-problem: that is one fixed amenable group with undecidable word problem; this is the complexity of recognizing amenability across all finite presentations.
  sofic-recognition-finite-presentations-arithmetical-position: that places soficity in the same intervals using finite permutation models; this places amenability there using Kesten's return probabilities, and the two properties are neither comparable nor both local.
---

ESTABLISHED.  For the recursive coding of finite group presentations,

```text
AMENABLE_fp     in Pi^0_2    \ Pi^0_1,
NONAMENABLE_fp  in Sigma^0_2 \ Sigma^0_1.                             (AF1)
```

The upper bound is Kesten's criterion (AM2) of
[[amenability-two-generator-recursive-is-pi2-complete]] applied to the
finite relator list.  The lower bound is the Adian--Rabin theorem:
amenability is a Markov property (the trivial group is amenable; `F_2` is
finitely presented and embeds in no amenable group), so the word problem
of a fixed finitely presented group with unsolvable word problem
many-one reduces to `AMENABLE_fp` (`w = 1` gives the trivial witness
group, `w != 1` gives a group containing `F_2`).  A `Sigma^0_1`-hard set
is not `Pi^0_1` and its complement is not recursively enumerable.

Whether `AMENABLE_fp` is `Pi^0_2`-complete is
[[amenability-of-finite-presentations-is-pi2-complete]].
