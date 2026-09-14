---
rg: 2
id: fp-intermediate-growth-truncation-proof
kind: route
title: Truncated presentations are finitely presented covers
target: fp-intermediate-growth-iff-subexponential-truncation
requires: []
---

Growth fact used: if `(Q, S)` is an `S`-marked quotient of `(P, S)`, the ball of radius `r` in
`Q` is the image of the ball of radius `r` in `P`, so `gamma_Q <= gamma_P`.

**Part 2.** Let `(Q, S)` be marked with every word of length `<= n_0` that is trivial in `G`
trivial in `Q`. Each relator in `R` is such a word, so the identity on `S` induces
`G = <S | R> -> Q`, onto. Hence `gamma_Q <= gamma_G`. The set of such marked groups contains the
cylinder set of marked groups whose trivial words of length `<= n_0` coincide with those of `G`,
which is an open neighbourhood of `G`. Groups of exponential growth have `gamma` not bounded by a
subexponential function, so none lies in it.

**Part 1, only if.** Let `G = <S | R>` be finitely presented of intermediate growth, relators of
length `<= n_0`, and `n >= n_0`. The relators of `P_n(G)` are trivial in `G`, so the identity on
`S` induces `P_n(G) -> G`. The relators `R` are among the relators of `P_n(G)`, so it also
induces `G -> P_n(G)`. These are mutually inverse on generators, so `P_n(G) = G`, which has
subexponential growth. Take `Q = G`.

**Part 1, if.** `P_n(Q)` is finitely presented, since there are finitely many words of length
`<= n` over `S`. The identity on `S` induces `P_n(Q) -> Q` onto, so `gamma_Q <= gamma_{P_n(Q)}`.
If `P_n(Q)` had polynomial growth, so would `Q`, contradicting intermediate growth. With the
hypothesis, `P_n(Q)` has subexponential but not polynomial growth, i.e. intermediate growth.
