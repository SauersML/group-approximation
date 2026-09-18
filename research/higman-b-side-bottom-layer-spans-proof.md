---
rg: 2
id: higman-b-side-bottom-layer-spans-proof
kind: route
title: The bottom layer of the universal b-side group maps onto F^(k-1)/P^(k-1), which the Magnus embedding places in a free module over the domain Z[P/P^(k-2)], where conjugation by c^m is multiplication by an element of infinite order
target: higman-b-side-bottom-layer-spans-are-infinite
requires:
  - higman-b-side-derived-closure-stays-in-bottom-layer
---

Conventions: `x^y = y^-1 x y`, `[x,y] = x^-1 y^-1 x y`. Notation as in the requirement: `U_k = ncl_(G_b)(F^(k))`,
`Q_k = G_b/U_k`, `P` free on `c_j = a^j c a^-j` (`j in Z`).

## Step 1 (the bottom layer maps onto `F^(k-1)/P^(k-1)`)

- `A = F/(F ∩ U_k)`, so `A^(i) = F^(i)(F ∩ U_k)/(F ∩ U_k)`. Since `F^(k) <= U_k`, we get `A^(k) = 1`,
  so `A^(k-1)` is abelian.
- The requirement gives `F ∩ U_k <= P^(k-1) <= F^(k-1)`. So
  `A^(k-1) = F^(k-1)/(F ∩ U_k)`, and there is a surjection

  ```text
  q : A^(k-1) -> F^(k-1)/P^(k-1).
  ```

  Both `F^(k-1)` and `P^(k-1)` are normal in `F` (they are characteristic in normal subgroups), so `q`
  commutes with conjugation by `gamma = c^m`.
- If the `gamma`-span of `q(w)` in `(F^(k-1)/P^(k-1)) ⊗ Q` is infinite-dimensional, then so is the
  `gamma`-span of `w` in `A^(k-1) ⊗ Q`. (Tensoring the surjection with `Q` keeps it surjective, and a
  finite-dimensional span maps onto a finite-dimensional span.)

## Step 2 (Magnus embedding of the layer)

- `F' <= P` gives `F^(k-1) <= P^(k-2)`, so `F^(k-1)/P^(k-1) <= R/R'` with `R = P^(k-2)`.
- Let `G = P/R`. This is the free solvable group of derived length `k - 2 >= 1` on the `c_j`. It is
  torsion-free and elementary amenable, so `Q[G]` has no zero divisors (Kropholler--Linnell--Moody).
- **Magnus embedding.** `c_j -> (t_j, c_j R)` induces an injective homomorphism `P/R' -> M ⋊ G`,
  where `M = ⊕_j Z[G] t_j` is a free left `Z[G]`-module with product `(x, g)(y, h) = (x + g y, gh)`.
  It restricts to an injective `Z`-linear map `mu : R/R' -> M`, `mu(r) = Σ_j D_j(r) t_j`, where the
  `D_j` are the Fox derivatives reduced mod `R`.
- **Conjugation.** Let `g in P` with image `ḡ in G`. For `r in R`,
  `g r g^-1 -> (t_g, ḡ)(mu(r), 1)(t_g, ḡ)^-1 = (ḡ mu(r), 1)`. So `mu(r^(g^-1)) = ḡ mu(r)`.
  Apply this with `g = gamma = c_0^m in P`, whose image `ḡ` has infinite order in `G`: its image in
  `G/G' = ⊕_j Z` is `m e_0 ≠ 0`, and `G/G'` is torsion-free.
- **Infinite span.** Let `w in F^(k-1) \ P^(k-1) = F^(k-1) \ R'`, so `mu(w) ≠ 0`. Suppose
  `Σ_j lambda_j gamma^j w gamma^-j = 0` in `(R/R') ⊗ Q`, with finitely many `lambda_j in Q`. Applying
  `mu ⊗ Q` gives `(Σ_j lambda_j ḡ^j) mu(w) = 0` in `M ⊗ Q = ⊕ Q[G] t_j`.
  - `mu(w) ≠ 0`, and `Q[G]` has no zero divisors.
  - `ḡ` has infinite order, so the `ḡ^j` are distinct basis elements of `Q[G]`.

  Hence all `lambda_j = 0`. So the `gamma`-conjugates of `w` are linearly independent in
  `(F^(k-1)/P^(k-1)) ⊗ Q`. (Here `M ⊗ Q` is still free, and `mu ⊗ Q` is injective, because `Q` is
  flat over `Z`.) By Step 1 the `gamma`-span of `w` in `V_k` is infinite-dimensional. ∎

## Step 3 (the candidate `[z, z^alpha]` lies outside `P''`)

Let `k = 3`, so `G = P/P'` is free abelian on `x_j = c_j P'`, and `R = P'`.
- With `alpha = a^m`, `z = [c^m, a^m] = c^-m a^-m c^m a^m = c_0^-m c_(-m)^m`, since
  `a^-m c a^m = c_(-m)`. Then `u := z` and `v := z^alpha = a^-m z a^m = c_(-m)^-m c_(-2m)^m`.
- `w = [u, v] in F''`. Since `u, v in P`, Fox calculus gives, mod `P'`,

  ```text
  D_0(w) = ū^-1 v̄^-1 ( (1 - v̄) D_0(u) - (1 - ū) D_0(v) ).
  ```

  Here `D_0(v) = 0`, because `v` does not involve `c_0` (`m >= 1`). Also
  `D_0(u) = D_0(c_0^-m) = -(x_0^-1 + ... + x_0^-m) ≠ 0`, and `v̄ = x_(-m)^-m x_(-2m)^m ≠ 1`.
- `Z[G]` is a Laurent polynomial ring, a domain, so `D_0(w) ≠ 0`. Hence `mu(w) ≠ 0`, i.e.
  `w ∉ P''`. Step 2 applies. ∎

## Step 4 (consequences)

- **Hirsch length.** In `Q_3`, `A''` is abelian and `A'' ⊗ Q` is infinite-dimensional by Steps 2 and 3,
  so `h(A'') = ∞`. For `k >= 3`, `U_k <= U_3`, so `Q_k` maps onto `Q_3` compatibly with `a, c`. Then
  `A''` of `Q_k` maps onto `A''` of `Q_3`, and `h(A'') = ∞` in `Q_k` too, since Hirsch length does not
  increase under quotients. For `k >= 4`, Step 2 applies to every element of `F^(k-1) \ P^(k-1)`.
- **`d` side.** `theta^2 : a -> c, b -> d, c -> a, d -> b` exchanges the roles of `a` and `c`, and
  carries the statement to `alpha`-spans of elements outside `P_d^(k-1)`.
- **`k = 2`.** The argument needs `k - 2 >= 1`. For `k = 2`, `G = P/P` is trivial, `gamma` acts trivially
  on `F'/P'`, and there is no obstruction. This matches the landed metabelian collapse.
