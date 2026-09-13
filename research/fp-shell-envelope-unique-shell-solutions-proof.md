---
rg: 2
id: fp-shell-envelope-unique-shell-solutions-proof
kind: route
title: Locality of letters, a double commutator and localized suffix elements force the unique shell solution
target: fp-shell-envelopes-are-unique-shell-solutions-of-their-relators
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
artifacts:
  - research/artifacts/shell-envelope-general-2026-09-13.md
---

Notation is as in the claim. Composition is right to left.

**0. `h(pi)` is a homeomorphism.**
- `h(pi)` is a bijection of `C` with inverse `h(pi^-1)`.
- At a point of `C_n` it is a prefix replacement on the clopen cone `C_n`,
  so it is continuous there.
- At `p`: the cones `0^m C` form a neighborhood basis of `p`, and
  `h(pi)(0^m C) = {p} union (union of C_(pi(n)) over n >= m)`. Since `pi` is
  a bijection, `pi(n) >= M` for all but finitely many `n`. Choosing `m` above
  that exception set puts the image inside `0^M C`, and the same argument
  works for `pi^-1`.

**1. Closedness.**
- Fix a word `r` and a point `x`. Evaluating `r` at `x` applies `|r|` letters
  in turn. A letter `y` in `Y` is a fixed homeomorphism. A letter `s^(+-1)`
  at an intermediate point of `C_n` uses only the single value
  `pi_s^(+-1)(n)`, and it fixes `p`.
- So whether `r(x) = x` depends on finitely many coordinates of
  `(pi_s, pi_s^-1)`, and `{pi : r(x) = x}` is clopen.
- `Sol(R)` is the intersection of these sets over all `r` in `R` and all
  `x` in `C`, so it is closed.

**2. A solution gives an injective homomorphism fixing V.**
- Let `pi` be in `Sol(R)`. By von Dyck's theorem, `y -> y`, `hat(s) -> h(pi_s)`
  defines a homomorphism `phi: E_nu -> Homeo(C)`. It is the identity on
  `V = <Y>`, so `ker(phi)` meets `V` trivially.
- Suppose `1 != l` is in `ker(phi)`. Pick `x` with `l(x) != x`, and a cone
  `U` containing `x` with `l(U)` disjoint from `U`, which exists by continuity.
- Pick `a, b` in `V` supported in `U` with `[a^-1, b] != 1`. The elements of
  `V` supported in a cone form a copy of `V`, which is nonabelian.
- Put `c = [l, a] = l a l^-1 a^-1`, which lies in `ker(phi)`. For `u` in `U`,
  `a^-1 u` is in `U`. Then `l^-1 a^-1 u` is in `l^-1(U)`, which is disjoint
  from `U`, so `a` fixes it and `c(u) = a^-1 u`. Hence `c` agrees with `a^-1`
  on `U` and `c(U) = U`.
- Therefore `c b c^-1 = a^-1 b a`: both are supported in `U` and agree there.
  So `[c, b] = a^-1 b a b^-1 = [a^-1, b]`. This is a nonidentity element of
  `V`, and it lies in `ker(phi)` because the kernel is normal. That
  contradicts `ker(phi) ∩ V = 1`, so `phi` is injective.

**3. Localized suffix elements read off `pi`.**
- Fix `1 != u` in `V` supported in the cone `1C`. For `n` in `N`, let `u_n`
  in `V` act by `0^n 1 z -> 0^n 1 u(z)` and fix everything else.
- For every permutation `pi`, `h(pi) u_n h(pi)^-1 = u_(pi(n))`. Check this on
  `x = 0^m 1 z`: `h(pi)^-1 x` lies in `C_(pi^-1(m))`, and `u_n` acts there
  exactly when `pi^-1(m) = n`. The point `p` is fixed by both sides.
- In particular `hat(s) u_n hat(s)^-1 = u_(rho_s(n))` holds in `E_nu`. Apply
  `phi`, which fixes `V` pointwise: `u_(pi_s(n)) = u_(rho_s(n))`.
- The `u_m` are nontrivial with pairwise disjoint supports, so
  `pi_s(n) = rho_s(n)` for all `n` and `s`. Also `rho` is in `Sol(R)` because
  `R` holds in `E_nu`. So `Sol(R) = {rho}`.

**4. The `A_1` variant.**
- Let `Y` generate `Fix_V(p)` and let `R` present `A_1` on `Y` and `hat(S)`.
  In step 2, choose `x != p` and a cone `U` not containing `p`. Such `x`
  exists because the moved set of `l` is open and nonempty, hence not `{p}`.
- Then `a`, `b` and `[a^-1, b]` fix `p` and lie in `Fix_V(p)`, where `phi` is
  the identity.
- The elements `u_n` fix `p`, so step 3 is unchanged.
