---
rg: 2
id: invariant-output-automata-have-only-nonlinear-decoders
kind: claim
title: An injective automaton with output invariant under an even-order finite subgroup has no linear left inverse over a field of characteristic two
distinct_from:
  linear-invariant-output-automata-fail-augmentation: that excludes linear encoders with invariant output; this excludes linear decoders for arbitrary nonlinear encoders with invariant output, by comparing linear parts of the decoder identity.
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

Let `G` be any group, `H` a finite subgroup of even order, and `tau` a cellular
automaton on `F_2^G`. Suppose the local rule `f` is an arbitrary Boolean
function and the output is right-`H`-invariant. Then no **linear** automaton
`sigma(y)(g) = sum_s d_s y(gs)` satisfies `sigma tau = id`.

*Proof.* Write `f` in algebraic normal form and let `a in F_2[G]` collect its
degree-one coefficients, `a = sum_m a_m m`. Invariance for every input makes the
normal form invariant under the relabeling `m -> hm`, so `ha = a` for all `h` in
`H`. Hence the augmentation of `a` is `|H|` times a sum, which is `0`. The
composition `sigma tau` has algebraic normal form `sum_s d_s f_s`, where `f_s` is
`f` with its variables shifted by `s`. Its degree-one part is the normal form of
the linear automaton of `d a`. The identity `sigma tau = id` forces
`d a = 1` in `F_2[G]`, so `eps(d) eps(a) = 1`, a contradiction. QED

So every certificate for
`leavitt-units-carry-injective-invariant-output-automaton` with an involution
symmetry over `F_2` needs a genuinely nonlinear decoder. The decoder identity
must cancel nonlinear terms through product coincidences. It can never be
reduced to a group-ring one-sided inverse.
