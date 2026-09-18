---
rg: 2
id: kazhdan-profinite-untwisting-is-virtual-splitting-proof
kind: route
title: Double the phase field, make coset indicators almost invariant, project with (T), and split the translation symmetries by Peter--Weyl
target: kazhdan-profinite-untwisting-is-virtual-splitting
requires: []
---

**Imports.** These are standard statement-level facts, and there are no graph prerequisites:
- the definition of property (T);
- martingale convergence in `L^2`;
- Fubini;
- Steinhaus: `A A^{-1}` contains a neighbourhood of `e` when `A` has positive Haar measure;
- `L^0(K, T)` is a Polish group under convergence in measure, on which translation acts continuously;
- the open mapping theorem for continuous surjective homomorphisms of Polish groups;
- Peter--Weyl;
- a totally disconnected compact Lie group is finite;
- induction of characters.

**Notation.**
- `mu` is Haar measure on `K`, and `K = K_0 > K_1 > ...` are open normal subgroups forming a neighbourhood basis
  of `e`. These exist because `K` is second countable.
- `gx` means `pi(g)x`.
- `R_k f(x) = f(xk)`, and `c^k(g,x) = c(g,xk)`.
- Right translations commute with the action, so `c^k` again satisfies (U).
- Write `c ~_psi c'` if `c(g,x) = c'(g,x) psi(gx) conj(psi(x))` for all `g` and a.e. `x`, with `psi` in `L^0(K,T)`.
- Normalization: (U) with `g = h = 1` gives `c(1,.) = 1`.
- The action is ergodic, because an invariant `L^2` function is invariant under the closure `K` of `pi(Gamma)`.

## Item 1

1. **Doubling.**
   - Put `(V(g)f)(x) = c(g, g^{-1}x) f(g^{-1}x)` on `L^2(K)`. Substituting `y = (gh)^{-1}x` in (U) gives
     `V(g)V(h) = alpha(g,h) V(gh)`.
   - Hence `rho = V (x) conj(V)` is a genuine unitary representation on `L^2(K x K)`:
     `(rho(g)F)(x,y) = c(g,g^{-1}x) conj(c(g,g^{-1}y)) F(g^{-1}x, g^{-1}y)`.
   - `rho(g)F = F` means `F(gx,gy) = c(g,x) conj(c(g,y)) F(x,y)` a.e.
2. **Almost-invariant vectors.**
   - Let `m_n = [K:K_n]` and `F_n(x,y) = m_n^{1/2} 1[x^{-1}y in K_n]`. Then `||F_n|| = 1`, and `F_n` is invariant
     under the diagonal left translation.
   - Substituting `(x,y) -> (gx,gy)` gives
     `<rho(g)F_n, F_n> = m_n sum_C |int_C c(g,.) dmu|^2 = ||E_n c(g,.)||_2^2`. Here `C` runs over the cosets of
     `K_n`, and `E_n` is the conditional expectation onto the coset sigma-algebra.
   - These sigma-algebras increase and generate the Borel sets, so martingale convergence gives
     `E_n c(g,.) -> c(g,.)` in `L^2`.
   - Hence `||rho(g)F_n - F_n||^2 = 2 - 2||E_n c(g,.)||^2 -> 0` for every `g`.
3. **Property (T).**
   - Let `P` be the projection onto the `rho`-invariant vectors. The restriction of `rho` to `ran(1-P)` has no
     invariant vectors. By (T) it has a finite `Q` and `eps > 0` with no unit vector moved less than `eps` by
     every `q` in `Q`.
   - Since `rho(g)(1-P)F_n - (1-P)F_n = (1-P)(rho(g)F_n - F_n)`, vectors with `||(1-P)F_n||` bounded below would
     normalize to such vectors for large `n`.
   - Hence `||F - F_n|| -> 0` with `F = PF_n`. Fix `n` with `||F - F_n|| < 1/2`.
4. **Coordinates.**
   - Put `G(x,k) = F(x,xk)`. The map `(x,y) -> (x, x^{-1}y)` preserves `mu x mu`, so `G` is in `L^2`.
   - Invariance of `F`, together with Fubini over the countable `Gamma`, gives the following for a.e. `k`:
     `G_k(gx) = c(g,x) conj(c^k(g,x)) G_k(x)` for all `g` and a.e. `x`.
   - So `|G_k|` is invariant, and by ergodicity it equals the constant `a_k = ||G_k||_2`, which is measurable
     in `k`.
   - Where `a_k != 0`, put `phi_k = G_k / a_k`. This is `T`-valued, and `c ~_{phi_k} c^k`.
5. **Positive measure.**
   - `F_n(x,xk) = m_n^{1/2} 1_{K_n}(k)`, so `||F - F_n||^2 >= m_n mu(B)`, where `B = {k in K_n : a_k = 0}`.
   - Hence `mu(B) < mu(K_n)/4`, and the good set `A` (the `k` in `K_n` with `a_k != 0` for which step 4
     holds) has `mu(A) > 0`.
6. **An open subgroup of symmetries.**
   - Let `S = {k : c ~ c^k}`.
   - `S` is closed under products: if `c ~_psi c^k` and `c ~_psi' c^k'`, then applying `R_k` to the second
     relation gives `c^k ~_{R_k psi'} c^{kk'}`, so `c ~ c^{kk'}` via `psi (R_k psi')`.
   - `S` is closed under inverses: applying `R_{k^{-1}}` to `c ~_psi c^k` gives `c^{k^{-1}} ~ c`.
   - So `S` is a subgroup containing `A`, hence `A A^{-1}`, which by Steinhaus contains a neighbourhood of `e`.
     Therefore `S` is open, of finite index, and compact.
7. **The symmetry group is a compact central extension.**
   - Give `K x L^0(K,T)` the product `(k,psi)(k',psi') = (kk', psi (R_k psi'))`. This is the semidirect product
     for the left action `k . psi = R_k psi`, and it is a Polish group.
   - `S^ = {(k,psi) : c ~_psi c^k}` is a subgroup by step 6. It is closed, because each of the countably many
     defining equations is an equality of continuous maps into `L^0`.
   - `q(k,psi) = k` maps `S^` onto `S`. Its kernel consists of the `(e,psi)` with `psi` invariant, that is the
     constants `T`, and `T` is central.
   - By the open mapping theorem, `S^/T -> S` is a homeomorphism. With `T` compact, `S^` is compact.
8. **Splitting over an open subgroup.**
   - Extend the function `z` from the closed subgroup `T` to a continuous `f` on `S^` (Tietze). Then
     `f'(s) = int_T conj(z) f(zs) dz` is nonzero (`f'(e) = 1`) and satisfies `f'(zs) = z f'(s)`.
   - The space `L^2_1 = {h : h(zs) = z h(s)}` is invariant under right translation. By Peter--Weyl it contains a
     finite-dimensional irreducible subrepresentation `sigma`, and `sigma(z) = z I`.
   - `N = ker sigma` is closed and normal, with `N ∩ T = 1`, and `S^/N` is a compact Lie group.
   - `S/q(N)` is continuously isomorphic to `S^/NT`. That group is a compact Lie group and also a quotient of
     the profinite group `S`, hence totally disconnected, hence finite. So `U := q(N)` is open.
   - `q|N : N -> U` is a continuous bijection from a compact space, so its inverse is a continuous homomorphic
     section `u -> (u, psi_u)`. This gives `psi_{uu'} = psi_u (R_u psi_{u'})`.
9. **Jointly measurable version.**
   - Let `U_m` be open normal subgroups of `U` with trivial intersection, and fix finite sets `r_m(u)` of coset
     representatives.
   - Put `Psi_m(u,x) = psi_{r_m(u)}(x)`. By uniform continuity, pass to a subsequence with
     `sup_u mu{|Psi_m(u,.) - psi_u| > 2^{-m}} < 2^{-m}`.
   - By Borel--Cantelli, `Psi = lim Psi_m` (set to 1 where the limit does not exist) is jointly measurable, with
     `Psi(u,.) = psi_u` a.e. for every `u`.
   - By Fubini, `Psi(vu,x) = Psi(v,x) Psi(u,xv)` for a.e. `(v,u,x)`.
10. **Trivializing the symmetries.**
    - By Fubini, a.e. `y` satisfies the identity of step 9 at `x = y` for a.e. `(v,u)`. Each left coset of `U`
      has positive measure, so in each one pick such a representative `y_i`.
    - Put `beta(y_i v) = conj(Psi(v, y_i))` for `v` in `U`. The identity gives `beta(x) conj(beta(xu)) = Psi(u,x)`
      for a.e. `(x,u)`.
    - So for a.e. `u`, `psi_u = beta (R_u conj(beta))`.
    - Substituting into `c ~_{psi_u} c^u` and rearranging: `c~(g,x) := c(g,x) beta(x) conj(beta(gx))` satisfies
      `c~(g,.) = R_u c~(g,.)` for a.e. `u` in `U`.
    - `c~` again satisfies (U), since the factor is the coboundary of a 0-cochain.
    - For each `g`, the stabilizer of `c~(g,.)` under `R` is a closed subgroup of `U` that is conull in `U`, so it
      equals `U`: for any `u`, the conull sets `u U'^{-1}` and `U'` meet.
11. **Descent.**
    - `c~(g,.)` is a function on the finite set `Y = K/U` of left cosets. Each point of `Y` has positive
      measure, so (U) for `c~` holds at every point of `Y`.
    - `(W(g)f)(y) = c~(g, g^{-1}y) f(g^{-1}y)` on `l^2(Y)` satisfies `W(g)W(h) = alpha(g,h)W(gh)`, by the
      computation in step 1. This is an exact, monomial `alpha`-projective representation.
    - The image of `pi` is dense and `U` is open, so `Gamma` is transitive on `Y`. The stabilizer of `eU` is
      `Lambda = pi^{-1}(U)`, so `dim W = [Gamma : Lambda]`.
12. **Restriction splits.**
    - For `l, l'` in `Lambda`, (U) at `y = eU` reads `f(l) f(l') = alpha(l,l') f(ll')`, with `f(l) = c~(l, eU)`.
    - So `alpha|Lambda` is the coboundary of `f`, which proves item 1.

## Item 2 (converse)

- Let `alpha|Lambda = delta f` with `Lambda = pi^{-1}(U)`, where `U` is open.
- Let `E = T x_alpha Gamma` have the product `(z,g)(w,h) = (zw alpha(g,h), gh)`. Then `chi(z,l) = z f(l)` is a
  character of the subgroup `T x_alpha Lambda` with `chi|T = id`.
- `Ind chi` is monomial on the lines indexed by `E / (T x_alpha Lambda) = Gamma/Lambda = K/U`. The group `T` is
  central, so it acts by `chi|T`.
- So `W(g) = Ind chi (1,g)` satisfies `W(g)W(h) = alpha(g,h) W(gh)` and `W(g) delta_y = c(g,y) delta_{gy}`,
  and this `c` satisfies (U) on `K/U`.
- The composite `c(g, xU)` satisfies (U) on `K`.

## Item 3

If `c` solves (U) on `K/L`, then `c(g, xL)` solves (U) on `K`; now apply item 1.

## Remarks

- **Cohomological form.** The kernel statement combines items 1 and 2. Replacing `alpha` by `alpha delta b`
  replaces `c` by `c b`.
- **Crossed-product form.** With `a_g(x) = conj(c(g, g^{-1}x))`, (U) gives
  `a_g sigma_g(a_h) alpha(g,h) = a_{gh}`. So the elements `a_g u_g` are untwisted unitaries.
- **Where (T) enters.** Property (T) enters only in step 3.
- **Where coherence enters.** Step 2 is the only place where a single measurable `c` on the whole of `K` is used,
  through martingale approximation.
