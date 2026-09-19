---
rg: 2
id: digit-edge-mf-is-a-free-entropy-model-uniqueness-question
kind: claim
title: MF of the digit-reading edge is a matrix-model conjugacy question governed by free entropy, and may fail
distinct_from:
  machine-free-digit-reading-group-is-mf: that asks whether Gamma^K is MF; this identifies the precise operator-algebra content of that question and records the free-entropy obstruction to a soft proof, hence the genuine possibility of a negative answer.
  fp-mf-completeness-wall-is-route-independent: that shows every engine meets this edge; this analyses the edge itself.
---

ESTABLISHED (as an identification of the analytic content; the reduction is
proved, the sign of the answer is left open).  Let `Gamma'` be the HNN tower
of [[machine-free-digit-reading-group-is-mf]] without `p`, with free
subgroup `F_0 = < t, a_1, ..., a_(2n) >` and its shifted copy `F_1 = < t d,
a_1, ..., a_(2n) >`, both free of rank `2n+1`, related by the
basis-to-basis isomorphism `iota : t -> t d`, `a_i -> a_i`.  `Gamma^K` is the
HNN extension `< Gamma', p | p F_0 p^-1 = F_1 >`.  Then:

```text
Gamma^K is operator-MF
  iff there is a matricial-regular realization Phi of Gamma' and a corona
      unitary U with U Phi(a_i) U^* = Phi(a_i), U Phi(t) U^* = Phi(t)Phi(d).   (FE1)
```

The "if" is Ueda's HNN corner plus Shulman's Theorem 20 with the regular
trace; the "only if" is restriction of a realization of `Gamma^K`.

## Why this is a free-entropy model-uniqueness question

The two tuples `(Phi(t), Phi(a_i))` and `(Phi(t)Phi(d), Phi(a_i))` have the
**same** `*`-distribution with respect to the regular limit trace `tr` of
`Gamma'`: both generate `F_0` resp. `F_1 ~= F_0`, and `tr` is the regular
character, so each is a free-Haar family of the same joint law.  A corona
unitary `U` implementing `(FE1)` is exactly an **approximate unitary
equivalence of two matrix models of the free group `F_(2n+1)` carrying the
regular trace**, subject to fixing the shared `a_i`-coordinates.

By Voiculescu's free entropy theory, matrix microstates for a free family do
**not** form a single approximate-unitary-equivalence class: the free
entropy dimension is maximal and the microstate spaces are large and
disconnected up to conjugacy.  Hence no soft distribution-matching argument
produces `U`; if one exists it must be built by hand from the specific
correlated microstates of `Gamma'`, and it is a genuine possibility that no
such `U` exists, i.e. that `Gamma^K` is **not** MF.

## Consequences either way

* If `Gamma^K` is MF by an explicit `U` compatible with the central machine
  letters, then [[mf-recognition-finite-presentations-is-pi2-complete]]
  holds (via [[fp-mf-completeness-wall-is-route-independent]]).

* If `Gamma^K` is **not** MF, then Cohen's `INF`-branch output is a finitely
  presented non-MF group, and the Higman compiler as usually built does not
  preserve MF.  This would not by itself refute
  `mf-recognition-finite-presentations-is-pi2-complete` (a different
  compiler might preserve MF), but combined with
  [[fp-mf-completeness-wall-is-route-independent]] it would make the
  finite-presentation completeness of MF a bona fide open problem tied to
  free-entropy model uniqueness for free-group HNN edges, on a par with the
  open residually-finite Higman embedding problem.

## Attempts

The exact-conjugacy attack fails by the free-entropy obstruction above.
The finite-quotient attacks fail by periodicity
([[c-free-aanderaa-rope-is-mf-with-fine-quotients]]).  The remaining
positive attack is a **structured microstate construction**: choose the
regular models of `Gamma'` from a self-similar (Bratteli / substitution)
tower on the digit space so that the shift `t -> t d` is implemented by a
partial-isometry-completed permutation of blocks, exactly as in the cyclic
case but with the digit refinement carried by the block structure.  Whether
the `a_i`-coordinates (`x -> x^m` scaling and `t -> x^-i t x^i` conjugation)
can be kept exactly commuting with that permutation on windows of growing
length is the open point; this is the operator-theoretic analogue of the
`(RPS2)` compatibility, now for approximate rather than finite models.
