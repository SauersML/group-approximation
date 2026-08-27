---
rg: 2
id: dual-prefix-renyi2-critical-rate-proof
kind: route
title: Combine the cq Renyi ceiling with the exact rectangular dual-prefix model
target: dual-prefix-renyi2-rate-is-critical-under-rectangular-escape
requires:
  - iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart
  - whitehead-swap-copy-completion-retains-rectangular-escape
---

The cq entropy calculation `(RCR1)--(RCR7)` in the target claim proves the
universal ceiling `I~_2(X:E)<=log |X|`.  Lossless identification of all
addressed children and return maps needs at least `|X|` classical indices,
so its codebook rate is never strictly below that ceiling.

The two prerequisites show that this sharp information-theoretic boundary
is actually realized by the Leavitt data, rather than being an irrelevant
outer bound: the matrix chart gives the uniform `2^N` address register and
the exact finite Whitehead/rectangular chain realizes either an independent
spectator reservoir (`I~_2=0`) or a perfectly correlated label-augmented
reservoir (`I~_2=N`).  Hence no uniform positive rate slack is forced by the
canonical dual-prefix relations or moments.

Moreover, the exact chain has zero typed boundary energy but genuinely
changes the multiplicity reservoir.  Therefore any divergence comparison
which makes failure of covering pay positive boundary energy declares this
chain successfully covered, while the proposed successful-covering
conclusion falsely declares it same-reservoir.  This directly contradicts
the conjunction of the other two compiler clauses and rules out evading the
entropy ceiling by assigning an unrelated artificially small number to `R`.
