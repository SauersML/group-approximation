---
rg: 2
id: nv-realizable-systems-closed-under-kakutani-equivalence
kind: claim
title: Brin-Thompson realizable Cantor systems are closed under factors, products, induced systems, towers (hence topological Kakutani equivalence), full-group elements and V-cocycle skew extensions
requires:
  - aperiodic-full-groups-lift-along-factor-maps
  - brin-thompson-groups-contain-full-groups-of-their-elements
distinct_from:
  decidable-minimal-subshifts-are-brin-thompson-factors: that asks whether every minimal subshift with decidable language is realizable and proves necessity plus three closure properties; this adds towers, full-group elements and skew extensions, and so invariance under topological Kakutani equivalence.
  smart-trace-full-group-embeds-in-brin-thompson-2v: that realizes one system; this is the calculus that multiplies it into a large class.
---

**ESTABLISHED** (lane proofs below, elementary; not reviewed; no novelty claimed).

## Definitions

An aperiodic homeomorphism `T` of a Cantor space `X` is **nV-realizable** if there are `g ∈ nV`, a
clopen `U ⊆ C^n` with `g(U) = U`, and a continuous surjection `π : U -> X` with `π ∘ g = T ∘ π`.
Then `[[T]]` embeds in `nV` (lift along `π`, then glue, by the two required nodes). So for every
realizable minimal subshift, Matui's `[[T]]'` is a finitely generated infinite simple amenable
subgroup of the finitely presented simple group `nV`.

## Statement

Let `(X, T)` be realized by `(U, g, π)` in `nV`.

1. **Factors.** Every aperiodic factor of `(X, T)` is realizable. (Compose the factor maps.)
2. **Products.** If `(X_i, T_i)` is realized in `n_i V`, then `(X_1 × X_2, T_1 × T_2)` is realized in
   `(n_1 + n_2)V` by `g_1 × g_2` on `U_1 × U_2`.
3. **Induced systems.** If `W ⊆ X` is clopen and the return time `r` of `T` to `W` is bounded
   (automatic when `T` is minimal), then `(W, T_W)` is realizable.
4. **Towers.** If `W ⊆ X` is clopen, `r` is bounded, `X = ∪_j T^j W`, and `(W, T_W)` is realizable,
   then `(X, T)` is realizable.
5. **Full-group elements.** If `h ∈ [[T]]` is aperiodic, then `(X, h)` is realizable.
6. **Skew extensions.** If `φ : U -> mV` is locally constant, then
   `G(u, z) = (g(u), φ_u(z))` on `U × C^m` lies in `(n+m)V`, and every aperiodic factor of it is
   realizable.

By 3 and 4, two minimal Cantor systems with conjugate induced systems on clopen sets (topological
Kakutani equivalence) are realizable together or not at all.

## Proofs

1. `ρ ∘ π` is a factor map from `(U, g)` whenever `ρ : (X,T) -> (X',T')` is one.
2. `g_1 × g_2` is a box map in `(n_1+n_2)V`, `U_1 × U_2` is clopen and invariant, and `π_1 × π_2`
   is a factor map. The product is aperiodic because its first coordinate is.
3. `U_W = π^-1(W)` is clopen, and the first return of `g` to `U_W` is `g^(r(π(u)))`. That is a piecewise
   power of `g` with finitely many exponents on clopen pieces, so it lies in `nV` by the gluing node,
   and `π` intertwines it with `T_W`.
4. Let `(U', g', π')` realize `(W, T_W)` in `nV`, and let `R = max r`. For `0 <= j < R` let `ι_j` be
   the box map `C^n -> B_j` that prefixes `1^j 0` to the first coordinate, and let
   `P_j = π'^-1{w : r(w) > j}`, which is clopen. Put `U'' = ⊔_j ι_j(P_j) ⊆ ⊔_j B_j` (clopen) and
   define `h` on `U''` by
   - `ι_j(u) -> ι_(j+1)(u)` if `r(π'(u)) > j + 1`,
   - `ι_j(u) -> ι_0(g'(u))` if `r(π'(u)) = j + 1`,
   and `h = id` off `U''`. Each case is a box map on a clopen piece. `h` is a bijection of `U''`,
   because levels `j >= 1` are hit from level `j - 1`, and level `0` is hit through the bijection
   `g'`. So `h ∈ nV`. The map `ρ(ι_j(u)) = T^j(π'(u))` is continuous, and `ρ ∘ h = T ∘ ρ`: at the top
   level, `π'(g' u) = T_W(π' u) = T^(j+1)(π' u)`. It is onto, because `X = ∪_j T^j{w : r(w) > j}`.
5. `h` has a continuous cocycle `m`, `h(x) = T^(m(x))(x)`. The lift `h~(u) = g^(m(π u))(u)` lies in
   `[[g|_U]] ≤ nV` (by the lifting and gluing nodes), and `π ∘ h~ = h ∘ π`.
6. On each clopen piece of `U` where `φ` is constant, `G` is the product of a box map of `C^n` and a
   box map of `C^m`, which is a box map of `C^(n+m)`. `G` is a bijection with inverse
   `(u, z) -> (g^-1 u, φ_(g^-1 u)^-1 (z))`. `U × C^m` is clopen and invariant, and `G` is aperiodic
   because `g` is.

## Consequence

Starting from the SMART trace subshift (`smart-trace-full-group-embeds-in-brin-thompson-2v`), every
minimal subshift that is topologically Kakutani equivalent to an aperiodic factor of a finite product
of `V`-cocycle skew extensions of SMART, or of such systems' minimal full-group elements, has its
Matui group `[[T]]'` inside some `nV`. Whether this reaches every minimal subshift with decidable
language is `decidable-minimal-subshifts-are-brin-thompson-factors`.
