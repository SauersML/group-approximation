---
rg: 2
id: fanizza-bcs-polynomial-doubling-tape
kind: claim
title: The computable BCS signal family contains a polynomial-cost projection-doubling tape
---

The particular `L`-family constructed by Fanizza--Kroell--Mehta--Paddock--
Rochette--Slofstra--Zhao has fixed named involutions defining projections
`P,Q`, a shift word `U`, and an involution `X_tilde`. Put

```text
P_tilde_n = Q U^n P U^(-n) Q,
X_tilde_n = U^n X_tilde U^(-n).
```

There are absolute positive integers `C,k` such that, whenever `m notin L`,

```text
P_tilde_n + X_tilde_n P_tilde_n X_tilde_n - P_tilde_(n+1)=0       (FDB1)
```

in the nested-conjugacy BCS algebra for every `n>=0`, and `(FDB1)` has a
decomposition over the finite defining relators of size at most

```text
C ((n+1)m)^k.                                                     (FDB2)
```

After the paper's quantitative embedding into an ordinary finite BCS algebra,
the same identity has polynomial decomposition cost, with a computable factor
depending on `m`. The distinguished projection satisfies `D=PQ`; their
weighted summation of `(FDB1)` yields

```text
||D||_phi <= C'_m sqrt(epsilon)                                  (FDB3)
```

for every `epsilon`-perfect strategy.

Thus the signal-collapse mechanism is literally a copying tape: in an exact
tracial representation, `(FDB1)` gives

```text
tau(P_tilde_(n+1))=2 tau(P_tilde_n),
```

so boundedness forces the initial mass to vanish. Quantitatively, the
geometric weight `2^(-n/2)` beats the polynomial certificate cost `(FDB2)`.

The original additive compiler and its synchronous-state strengthening are
recorded separately as `msz-polynomial-doubling-star-algebra-compiler` and
`msz-polynomial-doubling-survives-synchronous-states`.  The distinction is
load-bearing: the MSZ theorem already handles nontracial synchronous states,
while this node records the later finite-BCS packaging needed by Cairn's
predicate lanes.
