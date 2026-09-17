---
rg: 2
id: clean-ck-cover-separates-trivial-words-from-normal-generators
kind: claim
title: Over a decidable marking the Steinberg marked cover maps onto a decidable elementary group, so its trivial words and its normal generators are recursively separable
distinct_from:
  ck-envelope-has-a-finitely-normally-generated-maximal-kernel: that is the open existence of a finitely normally generated maximal kernel; this establishes a necessary condition for it, recursive separability of trivial words from normal generators, for the specific cover built from a decidable marking.
  ck-steinberg-marked-cover: that constructs the cover Gamma ->> EL_4(U) for any finitely presented marking; this adds that when the marking has solvable word problem (with T chosen as in decidable-fp-group-embeds-in-decidable-derived-subgroup) the map to EL_4(U) has recursive kernel.
  simple-envelope-forces-solvable-word-problem: that deduces a decidable word problem from a finitely presented SIMPLE envelope; this uses that deduction only in the necessity remark, and its content is a decidable NON-simple quotient of the envelope.
  ck-maximal-kernel-four-regimes: that classifies where a maximal kernel can live by level ideal and congruence layer; this says nothing about individual maximal kernels, and only rules out the computability invariant that kills poisoned envelopes.
artifacts:
  - experiments/ck-clean-cover-poison-2026-09-17/sandwich_normal_form.py
---

**Setup.** Let `H` be a finitely presented group with solvable word problem
and `1 != g in H`. Choose `T` as in
[[decidable-fp-group-embeds-in-decidable-derived-subgroup]]: finitely
presented, solvable word problem, `H <= [T,T]`. Let `U` be the sandwich ring
over `Z[T]`, and let `rho : Gamma ->> Q = EL_4(U)` be the marked cover of
[[ck-steinberg-marked-cover]].

Fix a finite generating set of `Gamma`. Write `Z_Gamma` for the set of words
that are trivial in `Gamma`, and `NG_Gamma` for the set of words `w` with
`<<w>>_Gamma = Gamma`. Both sets are recursively enumerable.

**Theorem.** The set `ker rho` of words (words trivial in `EL_4(U)`) is
recursive. It contains `Z_Gamma` and is disjoint from `NG_Gamma`. Hence:

1. `Z_Gamma` and `NG_Gamma` are recursively separable.
2. No **poison** lives in `Gamma`. A poison is a computable sequence of
   words `w_n` and a recursively inseparable pair of r.e. sets `A, B` with
   `w_n = 1` for `n in A` and `<<w_n>> = Gamma` for `n in B`.
3. `Gamma` has a nontrivial quotient with solvable word problem, namely `Q`.

**Necessity remark.** If some maximal proper normal `M <| Gamma` has
`Gamma/M` recursively presented, then `M` itself separates `Z_Gamma` from
`NG_Gamma` recursively. That holds in particular when `M` is finitely
normally generated. So separability is a necessary condition for
[[ck-envelope-has-a-finitely-normally-generated-maximal-kernel]].

## Why it matters

A swarm lane on the live bus (c-ckmax, 2026-09-17, not yet landed in this
worktree) refutes the literal hole. It feeds Chatterji--Kassabov Theorem 3
an input that contains the simple core **and** a poison built from
recursively inseparable sets. The resulting finitely presented property
(T) envelope `Gamma = <<s>>` has no nontrivial quotient with solvable word
problem, so it has no finitely normally generated maximal kernel.

That lane left open whether the clean marking used by
`boone-higman-via-ck-maximal-kernel` can carry such a poison. This claim
answers **no**, once `T` is chosen with the central-twist construction:

- The poison invariant (inseparability of `Z_Gamma` and `NG_Gamma`) is
  decided by the decidable elementary image, and it vanishes there.
- The refutation therefore does not transfer. The tenable form of the hole
  names the decidable marking.
- Any further obstruction for the clean cover must be invisible to
  `rho`. It must live in the covering kernel `K = ker rho` (regime R1 of
  [[ck-maximal-kernel-four-regimes]]), or in quotients `Gamma/<<F>>` by
  finite sets `F` (second-level poison), not in `Gamma` itself.

The original Lemma-6 amalgam over `<x_i>` needs the power problem of `H`.
It is only because of the central twist that decidability of `T`, and
hence of `U`, is available.
