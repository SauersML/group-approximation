---
rg: 2
id: canonical-profile-tensor-power-one-window-proof
kind: route
title: Diagonalize failed profile windows and tensor the surviving canonical model
target: canonical-profile-word-collapse-one-window
requires: []
---

If the finite-window statement fails, diagonalize tuples over growing
relator and trace-word windows. The resulting ultraproduct homomorphism has
the full canonical character and keeps `w` at distance at least `alpha`,
contradicting the first clause.

Conversely let `theta` have the full canonical profile and choose generator
lifts `U_n`. For each fixed `k`, `U_n^(tensor k)` still satisfies every fixed
relator asymptotically. It also preserves the canonical trace side condition:

```text
tr(v(U_n)^(tensor k))=tr(v(U_n))^k -> chi(v)^k=chi(v),
```

because `chi(v)` is either zero or one. Applying the single finite-window
cutoff to every tensor power gives

```text
2-2 Re(tau(theta(w))^k)<=alpha^2<2
```

for every `k`. The same modulus-one and Cesaro argument as in
`tensor-powers-upgrade-one-cutoff-to-radical` forces `theta(w)=I`.

For an additive mark `p=sum_g c_g g`, this upgrade is unavailable:
`p(U^(tensor k))` is not `p(U)^(tensor k)` because the latter has cross
terms. Additive marks instead use qualitative collapse at every epsilon and
the faithful canonical norm of `p`, as in `canonical-profile-kleene-higman`.
