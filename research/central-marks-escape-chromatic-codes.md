---
rg: 2
id: central-marks-escape-chromatic-codes
kind: claim
title: "Central marks escape both chromatic codes: a conjugacy-difference code needs a mark with infinite conjugacy class, and in the lifted Thompson group T-bar no commutator is a nontrivial central element, so no commutator code can mark z^k"
distinct_from:
  finite-quotients-bound-carmichael-conjugacy-chromatic-number: that bounds Carmichael conjugacy graphs through finite quotients and pushes the mark into the finite residual; this is an exact algebraic obstruction on the mark itself (finite conjugacy class, or central and not a commutator), with no finite quotient.
  torus-knot-k34-expander-pair-has-no-eigencorner: that kills the eigencorner leaf by an analytic expander pair; this kills the two combinatorial code criteria at their defining equation for central marks.
  lifted-thompson-t-is-not-mf: that is the open non-MF claim for T-bar; this only says which marks a chromatic-code proof of it may use.
---

**ESTABLISHED** by `central-marks-escape-chromatic-codes-proof`.

Area is finite only for words trivial in the group. So the defining
equations of the two established chromatic criteria must hold exactly in
`Gamma`:

```text
CCC1:  [c_v,h_v] = a_v x a_v^(-1)             (infinite-chromatic-commutator-code-kills-mf-mark)
CDC2:  b_v^(-1) b_w = a_(v,w) x a_(v,w)^(-1)   (bounded-area-conjugacy-difference-code-kills-mf-mark)
```

Here `x` is the mark.

**Statement.**

1. **(CDC needs an infinite conjugacy class.)**  Let `Gamma` be any group and
   `x != 1` a mark whose conjugacy class `C` is finite, for example a central
   mark.  Then every graph carrying data `b_v, a_(v,w)` that satisfies CDC2
   exactly has chromatic number at most `2|C|+1`.  For central `x` the bound
   is at most `3`.  If CDC2 is imposed on both orientations of each edge, as in
   the printed criterion, it moreover forces `x^2 = 1`.  So CDC never applies
   to a central mark, in any group.
2. **(Translation-number lemma.)**  Let `phi` be a homogeneous quasimorphism on a
   group `Gamma` and let `z` be central with `phi(z) != 0`.  If
   `[F,G] = z^m`, then `m = 0`.  In `T̄`, with `phi` the Poincaré translation
   number `tau`, which satisfies `tau(z) = 1`, this gives:
   `[F,G] in <z>` implies `[F,G] = 1`.
3. **(CCC cannot mark the centre of `T̄`.)**  Consequently no data satisfies
   CCC1 in `T̄` with mark `z^k` for `k != 0`, since `a_v z^k a_v^(-1) = z^k`.
   A chromatic-code proof of `lifted-thompson-t-is-not-mf` must therefore mark
   a non-central element.  This is enough, because
   `lifted-thompson-t-mf-radical-dichotomy` makes any nontrivial radical
   element give the full radical.
4. **(Exact T-tables lift.)**  Commuting pairs of `T` lift to commuting pairs
   of `T̄`.  An exact commutator table in `T`, with data `c_v, h_v, a_v`, mark
   `y` and graph of infinite chromatic number, lifts to an exact table in
   `T̄`.  The lift has mark `ỹ z^e` for one fixed integer `e` with
   `|e + tau(ỹ)| <= 2`, on an induced subgraph that still has infinite
   chromatic number.  Only the
   uniform area bound fails to transfer.

**Invariants and death steps.**

- Item 1: the invariant is the Cayley graph `Cay(Gamma, C u C^(-1))`, which
  has degree at most `2|C|`.  Proofs die at CDC2.
- Items 2 and 3: the invariant is the translation number, which is constant
  on conjugacy classes, shifts by `m` under `z^m` and is homogeneous.  Proofs
  die at CCC1.

DERIVATION
central-marks-escape-chromatic-codes-proof
