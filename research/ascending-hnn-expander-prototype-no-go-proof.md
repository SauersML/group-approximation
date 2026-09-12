---
rg: 2
id: ascending-hnn-expander-prototype-no-go-proof
kind: route
title: Conjugate a level edge back and compare the growing stabilizer index
target: ascending-hnn-expander-levels-do-not-have-fixed-prototype-edges
requires: []
---

The HNN relations give

```text
t^n K t^-n=phi^n(K).                                            (1)
```

From `[a,K]=1`, conjugation by `t^n` gives

```text
[a_n,phi^n(K)]=1.                                               (2)
```

For a base neighbor `s a s^-1`, its simultaneous `t^n`-translate is

```text
phi^n(s) a_n phi^n(s)^-1=a_n,                                  (3)
```

by `(2)`.  Hence conjugated prototype edges see only stabilizer loops.

Conversely the genuine fixed-scale level edge is

```text
(a_n, s a_n s^-1).
```

Conjugating both endpoints by `t^-n` gives

```text
(a, (t^-n s t^n) a (t^-n s^-1 t^n)),                           (4)
```

whose relative transporter depends on `n`.  It cannot lie in one fixed
finite word menu unless an additional relation supplies a bounded
scale-conversion theorem; `(HNE1)` supplies only the opposite-direction
words `t^n s t^-n=phi^n(s)`.

Finally, if the whole level incidence pair `(H_n,L_n)` were a simultaneous
conjugate of a fixed prototype `(H_0,L_0)`, then

```text
[H_n:L_n]=[H_0:L_0]                                             (5)
```

for every `n`.  Taking `(H_n,L_n)=(K,phi^n(K))` contradicts `(HNE2)`.

