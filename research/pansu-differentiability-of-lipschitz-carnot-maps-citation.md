---
rg: 2
id: pansu-differentiability-of-lipschitz-carnot-maps-citation
kind: route
title: Import Pansu's differentiability theorem as stated by Pinamonti and Speight
target: pansu-differentiability-of-lipschitz-carnot-maps
requires: []
---

Citation import, not a reproof. A. Pinamonti, G. Speight, *Porosity,
Differentiability and Pansu's Theorem*, arXiv:1603.04818. The theorem is due
to P. Pansu (Ann. of Math. 129 (1989)). Text extracted from the arXiv PDF on
2026-09-18.

- Definition 2.1 (p. 4): "A simply connected finite dimensional Lie group G is
  said to be a Carnot group of step s if its Lie algebra g is stratified of
  step s".
- p. 5: "Identifying G with Rn, any Haar measure is simply a constant multiple
  of n dimensional Lebesgue measure Ln."
- p. 6, (2.5): "there exists c > 0 such that c−1‖x‖≤ d(x)≤ c‖x‖ for every
  x∈ G." Here `‖·‖` is the homogeneous norm (2.4).
- The same page states that the Carnot–Carathéodory distance "satisfies the
  relations d(zx, zy) = d(x, y) and d(δr(x), δr(y)) = rd(x, y)" and "induces
  on G the same topology as the Euclidean distance".
- Definition 2.5 (p. 7): "A map L : G→ ~G is group linear (or is a Carnot
  homomorphism) if L(xy) = L(x)L(y) and L(δr(x)) =~δr(L(x)) whenever x, y ∈ G
  and r > 0. A map f : G→~G is Pansu differentiable at x∈ G if there exists a
  group linear map L : G→~G such that lim_{h→0} ~d(f(x)^{-1}f(xh), L(h))/d(h)
  = 0."
- Theorem 2.6 (p. 7): "(Pansu's Theorem). Let f : G→~G be a Lipschitz map.
  Then f is Pansu differentiable almost everywhere."

`R^n` is the step-one Carnot group: its CC distance is the Euclidean distance
and its dilations are scalar multiplications.
