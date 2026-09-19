---
rg: 2
id: benign-witness-finite-quotients-refine-the-fold
kind: claim
title: The Higman benign witness has finite quotients refining the fold on its symmetric double
refuted_by: arbitrary-benign-witness-fold-refinement-counterexample
distinct_from:
  positive-rope-profinite-edge-synchronization: that asks for cofinal finite quotients of the whole product separating every element of the witness group, i.e. residual finiteness of the witness, which fails; this asks only for finite quotients of the witness that close S and refine the fold on S, which is all the twisted-edge theorem consumes.
  mf-safe-asymmetric-hnn-replacement: that asks for an MF-safe replacement of the rope edge; this is the purely group-theoretic profinite condition that, by the twisted-edge theorem, makes the original edge MF-safe without replacement.
  higman-half-row-has-regular-mf-benign-witness: that proves the half-row witness is regularly MF; this asks for finite quotients of the full witness, a different (profinite, not analytic) property.
---

**REFUTED AS STATED.**  Benignness alone does not imply either `(i)` or
`(ii)`: [[arbitrary-benign-witness-fold-refinement-counterexample]] takes a
rank-two free subgroup of Thompson's finitely presented infinite simple group
`V`, with `N=L=1`.  Every finite quotient of the resulting rope group kills
both copies of `F`, so it cannot refine any nontrivial finite quotient of the
fold; the same finite-quotient invisibility also makes `S` nonclosed.

The narrower construction problem for the *particular* benign witness chosen
by the compiler is not decided by this counterexample.  A repaired claim must
name that witness, or add the relative profinite hypotheses which are absent
from the universal statement below.

Let `F` be a free group of finite rank, `N` a normal subgroup with `F/N`
residually finite, `K` a finitely presented benign witness for `N` with
finitely generated `L <= K` and `L cap F = N`, `Gamma = < K, v | [v,L] = 1
>`, `S = < F, v F v^-1 > ~= F *_N F`, and `tau : S -> F/N` the fold (the
quotient on the first copy, trivial on the second).  Show:

```text
(i)   S is closed in the profinite topology of Gamma;
(ii)  for every finite-index normal F' >= N of F there is a finite quotient
      of Gamma whose restriction to S factors the fold modulo F', i.e.
      S cap ker <= << F'_1, F_2 >>_S.                                   (BW1)
```

A sufficient form of `(ii)`: a homomorphism `K -> (F/F') wr C_2 = (F/F' x
F/F') x| <sigma>` with `f -> (fbar,1)` for `f in F` and `L` mapped into the
centralizer of `sigma`; extend by `v -> sigma`.

This is required only on the `INF` branch of the compiler, where `F/N` is
the residually finite bridge value of
[[bidirectional-hnn-bridge-trivial-value-is-residually-finite]] and `N` is
closed in `F`.  Together with
[[twisted-rope-edge-is-mf-under-relative-profinite-compatibility]] it makes
the rope edge `(R1)` MF and closes
[[mf-safe-asymmetric-hnn-replacement]].

## Why it is plausible and where it is hard

Finite quotients of `Gamma` are finite `K`-sets together with a permutation
commuting with `L`; these exist in abundance (any element of the centralizer
of the image of `L` in a symmetric group), so `Gamma` is far from having few
finite quotients even though it is not residually finite.  The condition
asks that some of them distinguish the two copies of `F` in `S` exactly as
the fold does.  A necessary consequence is `F cap cl_K(L) = N`, where `cl_K`
is the profinite closure in `K`: the witness must not hide `N` behind
distortion in `K`.  Whether the standard benign-closure operations
(intersections, joins, preimages, the machine rope) preserve this relative
separability is the concrete question.

## Attempts

*Product quotients of `Gamma`.*  Finite quotients of the form `Gamma ->
Kbar x C`, with `v` central, identify the two copies of `F` in `S` and
therefore send `[f,v]` to `1` for every `f`, while `tau([f,v]) = fbar`.
So `(ii)` fails for every quotient in which `v` becomes central; the
quotient must move the `L`-cosets, which is why the wreath shape `(F/F') wr
C_2` with `v -> swap` is the natural target.

*The wreath target.*  `F -> (fbar,1)` and `v -> swap` satisfy every
relation of `Gamma` except those of `K` outside `F`; what is needed is that
`K`'s finite presentation admits an extension of this assignment with `L`
landing in the centralizer of the swap.  For `K` of the form `F *_N L` this
is the universal property; the real witness is a quotient of a group of
that shape by the machine relations, and the attack dies at the point where
those relations force additional identifications on `F`.  Deferred until
the standard benign-closure operations (intersection, join, preimage,
machine rope of Rotman Thm 12.18 / Chiodo Thm 2.2) are each checked for
the necessary consequence `F cap cl_K(L) = N`.
