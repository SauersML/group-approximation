---
rg: 2
id: literal-group-not-stable-in-finite-actions
kind: claim
title: The literal group is sofic but not stable in permutations, in any standard sense
distinct_from:
  literal-mark-quotient-flexibly-stable: That asks about stability of the marked QUOTIENT `E/<w>`, which stays open; this is about `E` itself, and stability does not pass between a group and its central extension (Chapman--Dikstein--Lubotzky give a lamplighter counterexample).
  literal-group-sofic: That is soficity of `E`; this is the failure of stability that soficity plus non-residual-finiteness forces.
  finite-quotient-blindness: That is the mechanism making `E` non-residually-finite; this is the stability consequence drawn from it.
  sofic-stable-implies-residually-finite: That is the general literature principle, quantified over all groups; this applies it to one explicit finitely presented group whose soficity and non-residual-finiteness are proved in this repository.
  literal-stably-finite-non-mf-reduced-group-algebra: That concerns the reduced group C-star algebra of `E` and its trace; this concerns permutation approximations of the group itself.
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
  - non_mf_groups_exist.tex
---

The literal forty-one-relator group `E` is **not stable in finite actions**
(Gohla--Thom Definition 3.7), hence not stable in any stronger permutation
sense: not `rho`-stable, not flexibly stable, not weakly flexibly stable.

*Trust surface, split by conclusion.*  The first statement is internal end to
end.  The strengthening to "any stronger sense" uses Gohla--Thom Lemma 3.6 —
each standard notion implies stability in finite actions — which is external,
source-verified from the PDF and recorded in
`gohla-thom-stable-base-nonsofic-extension`.

`E` is sofic (`literal-group-sofic`) and not residually finite: the marked
involution `w != 1` is killed by every finite quotient, since a finite quotient
supplies an exact finite-dimensional unitary representation and
`literal-central-mark-corona-invisible` kills `w` in all of those.  A sofic
group stable in finite actions would be residually finite
(`sofic-stable-implies-residually-finite`).

**Two independent supports.**  (1) The general principle above, proved in
`notes/SOFIC_STABLE_IMPLIES_RESIDUALLY_FINITE_2026-08-14.md`, gives failure of
the weakest notion, hence of all of them.  (2) Independently, Glebsky--Rivera's
Theorem 2 (primary read by `cairn-scout`) says a sofic non-residually-finite
group has a defining system that is unstable in permutations in their strict
sense; `E` is finitely presented, so its forty-one-relator system is unstable
in that sense, on a primary citation alone.  The two routes share only the
inputs "sofic" and "not residually finite", both in-repo.

So `E` is an explicit finitely presented group that is sofic and provably
non-stable.  Contrast with the literature route this reverses: Gohla--Thom use
stability of a base to force non-soficity of a central extension, and here
soficity of the extension is proved first and forces non-stability instead.
