---
rg: 2
id: synchronous-cores-in-out-v-have-order-at-most-two-proof
kind: route
title: A synchronous synchronizing core is a sliding block code with no anticipation, and so is its inverse, so time reversal makes it a one-sided shift automorphism
target: synchronous-cores-in-out-v-have-order-at-most-two
requires: []
artifacts:
  - research/artifacts/gq-gq-infinite-primes-out-v-reading.md
---

Let `T` be the core of `t`: strongly synchronizing at some level `k`, so the state reached
after reading any word `u` with `|u| ≥ k` depends only on the last `k` letters of `u`.

**Step 1 (a block code with memory only).** `T` is synchronous, so reading `x_i` in the state
determined by `x_(i-k) … x_(i-1)` outputs one letter. Hence there is `f : {0,1}^(k+1) → {0,1}`
with output `y_i = f(x_(i-k), …, x_i)`. On bi-infinite sequences this defines a sliding block
code `F : {0,1}^Z → {0,1}^Z` with window `[-k, 0]`, which commutes with the shift.

**Step 2 (the inverse is of the same kind).** `t^{-1}` is also bi-synchronizing, and its core
`T'` is the inverse transducer of `T`, read from outputs to inputs. It is synchronous because
each transition of `T` consumes and emits one letter. So `T'` gives a block code `G` with
window `[-K, 0]`. In `O_2` the product `T'T` is the core of the minimized product, and it is
the one-state identity. Every finite pattern occurs after synchronization, so the composite
block code `G∘F`, which has a finite window, is the identity on `{0,1}^Z`; likewise `F∘G`.
So `F` is an automorphism of the two-sided full 2-shift, and so is `F^{-1} = G`, both with
zero anticipation.

**Step 3 (time reversal).** Let `R(x)_i = x_(-i)`. Then `F^R = R F R` and `G^R = R G R` are
block codes with windows `[0, k]` and `[0, K]`. Block codes that read only coordinates at or
to the right of the output coordinate act on one-sided sequences `{0,1}^N`, commute with the
one-sided shift, and are mutually inverse there. So `F^R` restricts to an automorphism of the
one-sided full 2-shift. By Hedlund, `Aut({0,1}^N, σ) = {id, flip}` (reproved in BCO,
arXiv:2004.08478). So `f` is `x_i` or `1 - x_i`.

**Step 4.** The minimal core with this output function has one state, the identity or the
flip `c`. Since `c^2 = id`, the class of `t` in `O_2 ≅ Out(V)` has order at most 2. ∎
