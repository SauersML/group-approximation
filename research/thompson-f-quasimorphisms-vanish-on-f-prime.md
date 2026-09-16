---
rg: 2
id: thompson-f-quasimorphisms-vanish-on-f-prime
kind: claim
title: The commutator subgroup of Thompson's group F is perfect and every homogeneous quasimorphism of F vanishes on it
---

Let `F` be Thompson's group, the piecewise-linear dyadic homeomorphisms of `[0,1]`, and let
`F' = [F,F]`. Then:

- `F'` is perfect, `[F',F'] = F'`;
- every homogeneous quasimorphism `β: F → R` vanishes on `F'`. Here "homogeneous
  quasimorphism" means `sup_{g,h} |β(gh) − β(g) − β(h)| < ∞` and `β(g^n) = nβ(g)` for all
  `n ∈ Z`. This is a "pseudocharacter" in arXiv:2406.12982, Definition 1.5.

Consequently every homogeneous quasimorphism of `F` is a homomorphism `F → R`, and it factors
through `F/F' ≅ Z^2`.

Proof: route `thompson-f-quasimorphisms-vanish-on-f-prime-proof`. It uses a disjoint-support
swindle and imports only the simplicity of `F'` (Dudko–Medynets, quoted verbatim) and
`thompson-f-has-no-free-subgroups`.

Prior art. arXiv:2406.12982v2 (read 2026-09-16) states as Citation 3.7, citing [Cal07, FFL23]:
"Every subgroup of F_n is agreeable". There `F = F_2`, and "agreeable" (their Definition 1.8)
means every pseudocharacter is a character. So for `F` itself the second item above is prior
art. The cited sources are D. Calegari, *Stable commutator length in subgroups of PL^+(I)*,
Pacific J. Math. 232 (2007) 257–262, and F. Fournier-Facio and Y. Lodha, Adv. Math. They were
not read, and this node does not depend on them.
