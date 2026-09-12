---
rg: 2
id: kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf-proof
kind: route
title: Ball markings form a commensurated set, and a transfixed copy gives finitely many marked pieces with stabilizers in H
target: kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf
requires: []
---

**Notation.**
- `X = {0,...,d-1}`; `X^*` is the set of finite words and `X^omega` is Cantor space.
- `H <= Aut(T_d)` is self-similar: for `h` in `H` and every word `w`, `h(w zeta) = h(w) h|_w(zeta)` with `h|_w` in `H`.
- An element `f` of `V_d(H)` is a homeomorphism given by complete finite prefix codes `u_1,...,u_k` and `v_1,...,v_k` and elements `h_1,...,h_k` of `H`, with `f(u_i zeta) = v_i h_i(zeta)`.
- Every word either extends some `u_i`, or is a proper prefix of one. Take any infinite extension of the word; its code prefix is either a prefix of the word or longer than it.

## 1. The marking set

Call `phi: X^omega -> X^omega` an *H-piece map* if it is injective and there are:
- a complete finite prefix code `w_1,...,w_m`;
- words `y_1,...,y_m`;
- elements `g_1,...,g_m` of `H`;

with `phi(w_j zeta) = y_j g_j(zeta)`. Let `S` be the set of classes
`[phi] = phi o H = {phi o h : h in H}`.

For `f` in `V_d(H)` put `f.[phi] = [f o phi]`. This is well defined and is an action, provided `f o phi` is again an H-piece map. To see that it is:
- Let `L = max |u_i|` and refine each piece `w_j` to the pieces `w_j z` with `|z| = L`.
- Then `y_j g_j(z)` has length at least `L`, so it equals `u_i t` for some `i` and word `t`.
- So `f(phi(w_j z zeta)) = v_i h_i(t) (h_i|_t g_j|_z)(zeta)`.

The image `im[phi] = phi(X^omega)` is a nonempty clopen set, and
`im(f.[phi]) = f(im[phi])`.

## 2. The ball markings are commensurated

For a word `u` let `beta_u(zeta) = u zeta`, and let `M = {[beta_u] : u in X^*}`.
Distinct words give distinct classes, because the images `u X^omega` differ.

- **Long words stay in `M`.** Fix `f` as above. If `u = u_i w`, then `f o beta_u = beta_(v_i h_i(w)) o h_i|_w`, so `f.[beta_u]` lies in `M`.
- **Short words are finitely many.** The remaining words are proper prefixes of code words, and there are finitely many of those.

So `f M \ M` is finite. The same holds for `f^-1`, so `M \ f M = f(f^-1 M \ M)` is finite. Hence `M` is a commensurated subset of the `V_d(H)`-set `S`, and so of `S` as a `G`-set for every subgroup `G`.

## 3. Property (T) transfixes M

Let `G <= V_d(H)` have property (T).
- For `g` in `G`, `c(g) = 1_(gM) - 1_M` is a finitely supported real function on `S`. It satisfies `c(g g') = pi(g) c(g') + c(g)`, where `pi` is the permutation representation on real `l^2(S)`.
- So `g . xi = pi(g) xi + c(g)` is an affine isometric action.
- By the Delorme--Guichardet theorem (Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Theorem 2.12.4), a countable discrete group with property (T) has property (FH). So this action fixes some real `xi` in `l^2(S)`, which gives `c(g) = xi - pi(g) xi`.
- Then `F = 1_M + xi` is `G`-invariant: `pi(g) F = 1_(gM) + xi - c(g) = F`.
- Let `M' = {s : F(s) > 1/2}`. It is `G`-invariant.
- `M` and `M'` differ only inside the set where `|xi(s)| >= 1/2`, which is finite because `xi` is in `l^2(S)`.

Property FW is exactly the conclusion of this step. The rest uses nothing more.

## 4. A finite invariant cover by marked pieces

Since `M \ M'` is finite, choose `N` with `[beta_u]` in `M'` for every `|u| >= N`.

Let `I` be the set of images of classes in `M'`. Let `P` be the set of classes in `M'` whose image is maximal in `I` for inclusion.

- **`G` permutes `P`.** `G` preserves `M'`, and `g` carries images to images and preserves inclusion.
- **`P` is finite.**
  - A ball `u X^omega` with `|u| > N` lies strictly inside its length-`N` prefix ball, which is in `I`, so it is not maximal.
  - So a class in `P` is either `[beta_u]` with `|u| <= N`, or one of the finitely many classes of `M' \ M`.
- **The images of `P` cover `X^omega`.**
  - Every point lies in some ball `u X^omega` with `|u| = N`, and that ball is in `I`.
  - Only finitely many members of `I` contain that ball: its prefix balls and images of classes of `M' \ M`.
  - Take one that is maximal among them. It is maximal in `I`, since anything strictly above it would also contain the ball.

## 5. Embedding a finite-index subgroup in H^P

Let `G_0` be the kernel of the permutation action of `G` on `P`; it has finite index in `G`. Fix a representative `phi` of each class in `P`.

- **The coordinate maps.** For `g` in `G_0`, `g.[phi] = [phi]` means `g o phi = phi o rho_phi(g)` for some `rho_phi(g)` in `H`. That element is unique because `phi` is injective.
- **Each coordinate is a homomorphism.** `(g g') o phi = g o phi o rho_phi(g') = phi o rho_phi(g) rho_phi(g')`.
- **The product map is injective.** If `rho_phi(g) = 1` for every class in `P`, then `g` fixes every `im phi` pointwise. These images cover `X^omega`, so `g = 1`.

Hence `g -> (rho_phi(g))` embeds `G_0` in `H^P`.

## 6. Residual finiteness

- `H <= Aut(T_d)` is residually finite: its level stabilizers are normal subgroups of finite index with trivial intersection.
- A finite direct power of a residually finite group is residually finite, and so is every subgroup of one. So `G_0` is residually finite.
- If `G_0` has finite index in `G`, then `G` is residually finite.
  - An element outside `G_0` is separated by the finite quotient `G/core_G(G_0)`.
  - An element of `G_0 \ {1}` avoids some finite-index normal subgroup `K` of `G_0`. The intersection of the finitely many `G`-conjugates of `K` is normal of finite index in `G` and avoids it.

## Multi-root groups

For `V_(d,r)(H)`, replace `X^omega` by `r` disjoint copies and let `M` be the set of balls in all copies. Steps 1--6 are unchanged.
