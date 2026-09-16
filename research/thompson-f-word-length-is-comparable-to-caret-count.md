---
rg: 2
id: thompson-f-word-length-is-comparable-to-caret-count
kind: claim
title: Word length in Thompson's group F is linearly comparable to the caret count of the reduced tree pair diagram
---

Let `F` be Thompson's group with a finite generating set, `|f|` the word length,
and `N(f)` the number of carets in either tree of the reduced tree pair diagram
of `f`. Then there is a constant `K ≥ 1` with

`N(f)/K - K ≤ |f| ≤ K·N(f) + K` for all `f ∈ F`.

The statement is independent of the generating set, because any two word metrics
are bi-Lipschitz equivalent. It is imported from Burillo–Cleary–Stein (see the
citation route). The route that uses it is
`thompson-t-compression-one-half-via-cylinder-charts`, which needs only the
upper bound `|f| ≤ K·N(f) + K`.
