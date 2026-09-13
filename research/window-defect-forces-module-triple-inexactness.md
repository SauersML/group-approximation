---
rg: 2
id: window-defect-forces-module-triple-inexactness
kind: claim
title: A spectral gap on the boundary together with approximate kernels in configurations that look like the boundary on windows forces a non-exact crossed-product sequence
distinct_from:
  split-quotients-give-exact-reduced-crossed-products: that certifies exactness under splittings; this is a sufficient criterion for C*-non-exactness, in the form a module construction would have to meet.
  k-inexact-module-triple-refutes-trivial-coefficient-bc: that needs a K-theory defect; this produces only a C*-algebra defect, a necessary first step that does not by itself give a K-defect.
  reduced-group-algebras-contain-no-nonzero-ghosts: that shows ghost witnesses are invisible in the group algebra; this gives the non-ghost form of a non-exactness witness in a crossed product with coefficients.
---

**ESTABLISHED** by `window-defect-forces-module-triple-inexactness-proof`.

**Setting.**
- `G` is a countable group acting on a compact space `X`, with `Z ⊆ X` closed invariant and
  `U = X \ Z`.
- For `xi ∈ X`, `pi_xi` is the regular representation of `C(X) ⋊_r G` on `l^2(G)`:
  `pi_xi(a) delta_k = a(k^-1 xi) delta_k` and `pi_xi(u_g) = lambda_g`.
- The main case is `X = V^` and `Z = W^perp` for a module quotient.

**Hypotheses.**
- **(H1) Boundary gap.** There are `D = D^* = sum_(g ∈ T) a_g u_g` with `T` finite and
  `a_g ∈ C(X)`, and `eps > 0`, such that `spec(pi_zeta(D)) ∩ (-eps, eps) = ∅` for every
  `zeta ∈ Z`.
- **(H2) Window defect.** There are:
  - points `xi_n ∈ X`;
  - finite sets `R_n ⊆ G` and unit vectors `eta_n` supported in `R_n`;
  - finite sets `S_n` increasing to `G`;
  - neighborhoods `N_n` of `Z`, eventually inside every neighborhood of `Z`;

  such that
  - (a) `||pi_(xi_n)(D) eta_n|| -> 0`;
  - (b) `k^-1 xi_n ∈ N_n` for every `k ∈ S_n R_n`.

**Conclusion.** Let `f : R -> [0,1]` be continuous with `f(0) = 1` and `f = 0` off
`(-eps, eps)`. Then `f(D)` lies in the kernel of `C(X) ⋊_r G -> C(Z) ⋊_r G`, and its distance
to `C_0(U) ⋊_r G` is `1`. So the sequence is not exact.

**Reading.**
- Around every point of the support of `eta_n`, the configuration `xi_n` looks like a boundary
  configuration on a large window, yet `D` has an approximate kernel there, which no boundary
  configuration allows.
- So the windows cannot be glued into a single `zeta ∈ Z`: the witness is a
  **local-to-global gluing defect**.
- For finitely generated `W`, `Z` is cut out by finitely many linear local rules, an algebraic
  subshift of finite type. A module witness therefore needs patches that satisfy the local
  rules but do not extend to global solutions, at the places where `D` has approximate kernel.

**Model tests.**
- *Trivial model.* If `Z` is a single fixed point, (H2)(b) gives
  `||pi_zeta(D) eta_n - pi_(xi_n)(D) eta_n|| -> 0`. With (a) this contradicts (H1). So the
  criterion never applies to a quotient onto trivial coefficients, consistent with Ozawa's
  Lemma A.1.
- *Real object, not a module.* Take `X = βG` and `Z = ∂βG`. Suppose `G` contains an
  injective, separated embedding of a `k`-regular expander `⊔ X_n` with `k >= 3`, girth
  tending to infinity, and edges of bounded length (context, not imported). Take
  - `D` = the expander Laplacian plus the indicator of the complement of `⊔ X_n`;
  - `xi_n = e`, `eta_n` = normalized `1_(X_n)`, and `N_n` = complements of growing finite sets.

  Every boundary representation is then a direct sum of `k`-regular tree Laplacians and the
  identity. Its spectrum misses `(-eps, eps)` with `eps = min(1, k - 2 sqrt(k-1))`, while
  `eta_n` is an exact kernel vector. This is the ghost setting of
  Higson--Lafforgue--Skandalis and Roe--Willett, and the conclusion matches their
  non-exactness.

Only a C*-level defect follows. Detecting it in K-theory is the open step of
`some-nonexact-group-has-a-k-inexact-module-triple`.
