---
rg: 2
id: central-marked-involution-zero-compression-proof
kind: route
title: Expand the marked grading covariance and construct its converse
target: central-marked-involution-zero-compression-cell
requires: []
---

Because `p` commutes with `w,z`, relation `(MZC1)` gives

```text
w q w=p(1-wzw)/2=p(1-yz)/2=p(1+z)/2=p-q.
```

The two projections `q` and `p-q` are orthogonal, so

```text
||q w q||_2=||q w q w||_2=||q(wqw)||_2=0.
```

For the converse, `(MZC4)` says `W(QH)` is orthogonal to `QH`; hence
`Q'=WQW` is orthogonal to `Q`.  The sum `P=Q+Q'` is `W`-invariant, so `Y`
commutes with `W`, and it plainly commutes with `Z`.  Finally

```text
WZW=1-2Q'=YZ,
```

where the last equality follows by expanding `(1-2Q-2Q')(1-2Q)` and using
`QQ'=0`.  This proves exact completeness.

For `(MZC6)`, the same calculation with defect gives

```text
||wqw-(p-q)||_2
 =1/2 ||p(wzw-yz)||_2 <=delta/2.
```

Multiplication by `q` and unitary invariance then give
`||qwq||_2<=delta/2`.

Finally, expanding `(MZC2)` gives

```text
tau(q)=1/4(1-tau(y)-tau(z)+tau(yz)).
```

Canonical trace separation of the three fixed nonidentity words proves
`(MZC7)`.
