---
rg: 2
id: component-space-sizes-miss-cover-defect-proof
kind: route
title: Block invariance fixes the component algebra pointwise, so compressors and host elements act on components only through the centralizer
target: component-space-sizes-miss-leavitt-cover-defect
requires:
  - kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient
  - realized-relative-twists-embed-in-outer-twist-group
  - conjugation-invariant-sizes-miss-relative-defect
  - finite-orbit-indices-miss-twists-without-finite-quotients
  - relative-defect-iff-surjective-compressor-endomorphisms
  - hyperbolic-kazhdan-cover-of-leavitt-unit-group
  - leavitt-cover-finite-quotients-split-over-the-kernel
  - leavitt-unit-group-carries-nontrivial-rigid-defect
  - binary-leavitt-unit-group-is-simple
  - openai-leavitt-unit-nonsofic
---

Notation as in the target. Commutators are `[a, b] = a b a^-1 b^-1`.

1. **Fixed algebras.** If `K <= K' <= G`, then `D^(K') <= D^K`. For a compressor
   `t`, `M = t M t^-1 <= t Gamma t^-1 <= Gamma <= G`, because `M` is normal in
   `G`. So

   ```text
   D^G  <=  D^Gamma  <=  D^(t Gamma t^-1)  <=  D^M .
   ```

   `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient` gives
   `D^G = D^M`, so all four algebras agree.
   - The refinement inclusion is an equality, and a factor map between equal
     algebras has fibre counts `1`.
   - Every `sigma(g)` commutes with every element of `D^G`, so `Ad(sigma(g))` is
     the identity on `D^Gamma`. In particular each transport `Ad(s)` is.

   This proves item 1.
2. **Realizers preserve the component algebra.** For `x in N_rel(sigma)` and
   `gamma in Gamma_s`, `x gamma x^-1 = [x, gamma] gamma` lies in `Gamma_s`, and
   the same holds for `x^-1`. So `x` normalizes `Gamma_s`. A permutation in `S_U`
   normalizes `D_U` and sends `sigma(Gamma)`-invariant elements to
   `x sigma(Gamma) x^-1`-invariant ones, which are `sigma(Gamma)`-invariant. So
   `Ad(x)` restricts to an automorphism of `D^Gamma`. The same argument applies
   to `C_s`, which commutes with `sigma(Gamma)`.
3. **Corner classes are read off `Act`.** Let `x in R(q)` have twist `phi_x`, and
   let `p` be a projection in `D^Gamma`. For `gamma in Gamma_s`,

   ```text
   x (gamma p) x^-1  =  phi_x(gamma) . (x p x^-1) .
   ```

   So conjugation by `x`, which carries the corner `p` onto the corner
   `x p x^-1`, intertwines `sigma|_Gamma p . phi_x^-1` with
   `sigma|_Gamma (x p x^-1)`. The precomposition action of `q` on corner classes
   therefore depends only on `Ad(x)|_(D^Gamma)`. It is a component-level
   quantity.
4. **Compressor invariance.** By step 1 of
   `conjugation-invariant-sizes-miss-defect-proof`, `R(eps_t(q)) = s^-1 R(q) s`.
   For `x in R(q)`,

   ```text
   Ad(s^-1 x s)|_(D^Gamma)  =  Ad(s)^-1 . Ad(x) . Ad(s)|_(D^Gamma)  =  Ad(x)|_(D^Gamma),
   ```

   because `Ad(s)` is the identity on `D^Gamma` (step 1) and `Ad(x)` preserves
   `D^Gamma` (step 2). So `Act(eps_t(q)) = Act(q)`. For `B <= Q_s`, the families
   `{Act(q) : q in eps_t(B)}` and `{Act(q) : q in B}` are equal, and the ambient
   data do not depend on `B`. This proves item 2 and the first half of item 4.
5. **Host twists.** Let `z in G` with `[z, Gamma] <= M`. The realizers of
   `[sigma(z)]` are `sigma(z) m c` with `m in M_s` and `c in C_s`. Both `sigma(z)`
   and `m` lie in `sigma(G)`, so they act trivially on `D^Gamma`, and
   `Ad(sigma(z) m c)|_(D^Gamma) = Ad(c)|_(D^Gamma)`. The trivial class has the
   realizers `m c`, with the same restrictions. So
   `Act([sigma(z)]) = Ad(C_s)|_(D^Gamma) = Act(1)`. This proves item 3 and the
   second half of item 4.
6. **The cover satisfies the hypotheses.**
   - `N` is infinite and Kazhdan, and `Gamma_hat <= G` is a rigid pair containing
     `N`: `hyperbolic-kazhdan-cover-of-leavitt-unit-group` and Theorem 3(a) of
     `research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md`.
   - `R^x` is simple (`binary-leavitt-unit-group-is-simple`) and not sofic
     (`openai-leavitt-unit-nonsofic`). A homomorphism `R^x -> S_U` is trivial or
     injective. An injective one would make `R^x` sofic, since countable
     subgroups of `S_U` are sofic. So every such homomorphism is trivial.
   - The host quotient is `Q = C_(R^x)(EL_alpha(R))`
     (`relative-defect-iff-surjective-compressor-endomorphisms`, Consequences),
     and `eps_u(A) <= A <= Q`
     (`finite-orbit-indices-miss-twists-without-finite-quotients`, item 4).

   So `A`, `eps_u(A)` and `1` are subgroups of `Q`, and by step 5 they have the
   component-level quantities of the trivial group.
7. **Outer twists as outer automorphisms of `N`.**
   - `C_G(N) = 1` (`leavitt-cover-finite-quotients-split-over-the-kernel`). So
     `Z(N) = 1`, and `g -> [Ad(g)|_N]` embeds `R^x = G/N` in `Out(N)`: if
     `Ad(g)|_N = Ad(n)|_N`, then `n^-1 g` centralizes `N`, so `g = n`.
   - A trace-zero `sigma` is injective. It identifies `N` with `M_s` and
     `Out(N)` with `Out(M_s)`. Write `gbar` for the class of `Ad(sigma(g))|_(M_s)`.
   - Let `phi in Aut_M(Gamma_s)`, so `phi(gamma) = n_gamma gamma` with
     `n_gamma in M_s`, and `phi(M_s) = M_s`. Suppose `phi|_(M_s) = Ad(m)|_(M_s)`.
     Then `phi' = Ad(m)^-1 . phi` lies in `Aut_M(Gamma_s)` and fixes `M_s`
     pointwise. For `n in M_s`, apply `phi'` to `gamma n gamma^-1 in M_s`, with
     `phi'(gamma) = n'_gamma gamma`:
     `gamma n gamma^-1 = n'_gamma gamma n gamma^-1 n'_gamma^-1`. So `n'_gamma` is
     central in `M_s`, hence `1`, and `phi' = id`. So `phi -> [phi|_(M_s)]`
     embeds `Out_M(Gamma_s)` in `Out(N)`.
   - For `g in Gamma_hat` and `gamma = sigma(g)`:
     `phi . Ad(gamma) . phi^-1 = Ad(n_gamma gamma)` on `M_s`. So `[phi|_(M_s)]`
     commutes with `gbar`, and the image lies in `C_Out(N)(EL_alpha(R))`.
   - `eps_u(phi)|_(M_s) = Ad(s)^-1 . phi|_(M_s) . Ad(s)`, with `s = sigma(u_hat)`.
     So `eps_u` is conjugation by `ubar^-1`.
8. **The witness is outside every compressed stabilizer.**
   - Let `z` be a lift of the defect element, so `[z, Gamma_hat] <= N`, but
     `[u_hat z u_hat^-1, Gamma_hat]` is not contained in `N` (Theorem 3(c) of
     the artifact). Suppose `[sigma(z)] = eps_u([phi])` with
     `phi in Aut_M(Gamma_s)`. By step 7, `[phi|_(M_s)] = ubar zbar ubar^-1`, the
     class of `u_hat z u_hat^-1`, commutes with `gbar` for every `g in Gamma_hat`.
     So `Ad([u_hat z u_hat^-1, g])|_N` is inner, and
     `[u_hat z u_hat^-1, g] in N . C_G(N) = N`. That contradicts Theorem 3(c).
     So `[sigma(z)]` is not in `eps_u(Out_M(Gamma_s))`.
   - Let `Q_s(p)` be the set of classes `[phi]` such that `sigma|_Gamma p . phi`
     is conjugate to `sigma|_Gamma p` in `S_U(p)`. It is a subgroup containing
     `Ad(M_s)`, and `Q_s(1) = Q_s`.
   - `sigma(z)` commutes with `p` (step 1), and conjugation by `sigma(z) p`
     carries `gamma p` to `phi_z(gamma) p`. So `[sigma(z)] in Q_s(p)`.
   - If `y in S_U(p)` satisfies `y (gamma p) y^-1 = phi(gamma) p` for all
     `gamma in Gamma_s`, then `s^-1 y s in S_U(p)`, because `s` commutes with `p`,
     and

     ```text
     (s^-1 y s) (gamma p) (s^-1 y s)^-1  =  s^-1 phi(s gamma s^-1) s . p  =  eps_u(phi)(gamma) . p .
     ```

     So `eps_u(Q_s(p)) <= Q_s(p)`, and the inclusion is strict because
     `[sigma(z)]` lies in `Q_s(p)` but not in `eps_u(Out_M(Gamma_s))`.
9. **Normalization would force central twists.** Suppose `sigma(G)` normalizes
   `N_rel(sigma)`.
   - For `x in N_rel(sigma)` and `g in G`,
     `[Ad(sigma(g) x sigma(g)^-1)|_(M_s)] = gbar [Ad(x)|_(M_s)] gbar^-1`. So the
     image of `Q_s` is invariant under conjugation by every `gbar`.
   - By step 7 it lies in `C_Out(N)(EL_alpha(R))`, hence in the centralizer of
     every conjugate of `EL_alpha(R)` in `R^x`.
   - These conjugates generate a nontrivial normal subgroup of the simple group
     `R^x`, i.e. all of `R^x`. So `Q_s <= C_Out(N)(R^x)`.
   - `R^x` embeds in `Out(N)` and is simple and nonabelian, so
     `R^x cap C_Out(N)(R^x) = Z(R^x) = 1`.
10. **No soficity is used.** Steps 1-5 use block invariance, which rests on
    property (T) of `M` and on the absence of sofic representations of `G/M`.
    Steps 6-9 are algebra in `Out(N)` and in the ultraproduct. The statement
    holds for every sofic representation, whether or not `G` is sofic, so it
    gives no nonsoficity.
