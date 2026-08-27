---
rg: 2
id: finite-role-hybrid-row-no-go-proof
kind: route
title: Use regular-sector support to classify universal scalar rows
target: finite-role-packet-cannot-supply-hybrid-predicate-row
requires: []
---

For `chi in dual(A)` put

```text
p_chi=|A|^(-1) sum_(a in A) conjugate(chi(a))a,
p_-=(1-y)/2=sum_(chi(y)=-1)p_chi.
```

Apply the universal scalar hypothesis to the `y=-1` part of the left
regular representation.  On the `chi`-weight range it says
`e p_chi=epsilon_chi p_chi`.  Hence

```text
e p_-=sum_(chi(y)=-1) epsilon_chi p_chi in C[A].       (1)
```

But `e p_-=(e-ey)/2`.  If `e` were outside `A`, the two distinct group-basis
elements `e,ey` would both lie outside `A`, contradicting `(1)`.  Therefore
`e in A` and `epsilon_chi=chi(e)`.

Write marked characters as `(r,x)`, where `z` is the role bit.  The desired
hybrid table is `epsilon(0,x)=(-1)^{f(x)}` and `epsilon(1,x)=1`.  A character
which is one for every `(1,x)` has zero coefficient on the role and all
selector bits, so it is also one for every `(0,x)`.  Thus every nontrivial
predicate is excluded.

Quantitatively, let

```text
q_f=sum_(chi(y)=-1) epsilon(chi)p_chi.
```

If `e` is outside `A`, `ep_-` and `q_f` have disjoint group-basis support.
If `e in A`, Plancherel on `A` gives

```text
||p_-(e-q_f)||_2^2
 =4/|A| #{chi(y)=-1:chi(e)!=epsilon(chi)} >=4/|A|.
```

This proves the fixed gap.  Finally, the spectral sum
`p_(z,+)h_f+p_(z,-)` is directly a self-adjoint group-algebra involution
with the desired table, proving that the obstruction is specifically to a
single universally saturated group word.
