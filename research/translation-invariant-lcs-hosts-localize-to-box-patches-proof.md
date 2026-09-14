---
rg: 2
id: translation-invariant-lcs-hosts-localize-to-box-patches-proof
kind: route
title: Induce box models along the torus and restrict host models along ordered translations
target: translation-invariant-lcs-hosts-localize-to-box-patches
requires: []
---

Notation is as in the target. `||A||_2 = tr_n(A^*A)^(1/2)` with the normalized trace. This norm is unitarily invariant and satisfies `||AB||_2 <= ||A||_op ||B||_2`. For words in unitaries, the distance between two evaluations is at most the sum of the letterwise distances.

## Step 0. The host presentation and R^U-satisfiability

Generators: `x_v` (`v in V`), `j`, `t_1,...,t_d`. Relators, with `X_(v,y) = t^y x_v t^(-y)` and `t^y = t_1^(y_1)...t_d^(y_d)`:

```text
(H1) [t_i, t_k]                                   (i < k)
(H2) x_v^2
(H3) j^2,  [j, x_v],  [j, t_i]
(H4) (prod_((v,y) in S_c) X_(v,y)) j^(b_c)        (fixed order, each type c)
(H5) [X_(v,y), X_(w,y')]                          ((v,y) != (w,y') in S_c)
```

- **This presents `Sol(L) ⋊ Z^d`.** Modulo (H1), `t^a` is well defined. The translate by `a` of any placement relator of `Sol(L)` is the conjugate by `t^a` of the corresponding origin relator. Adjoining generators `X_(v,y)` for `y != 0`, defined as these conjugates, is a Tietze move. The resulting presentation is the standard one for the semidirect product, so `Sol(L)` embeds in `Gamma(L)`.
- **R^U.**
  - Given `(eps_k,J)`-models with `eps_k -> 0`, their ultraproduct is an ultraproduct of matrix algebras. It embeds trace-preservingly in `R^U`, satisfies the relators exactly and sends `J` to `-1`.
  - Conversely, lift the finitely many generator images of a *-homomorphism into `R^U` to unitaries of `R`. Approximate those in 2-norm by unitaries of a matrix subalgebra `M_(2^m) ⊂ R`. The relators and `J = -1` then hold up to any prescribed `eps` along the ultrafilter.

## Step 1. Item 1: induce along the torus

Let `xi_(v,y)` (`y in B_N`) and `iota` on `H = C^n` be an `(eps,J)`-model of `P_N`.

- **The model on `K`.** On `K = H ⊗ C^(Z_N^d)`, define:
  - `T_i = I ⊗ S_i`, where `S_i delta_a = delta_(a - e_i)`;
  - `jt = iota ⊗ I`;
  - `xt_v = sum_(a in Z_N^d) xi_(v, abar) ⊗ E_(aa)`, where `abar in B_N` is the representative of `a`.

  The `T_i` commute and `T_i^N = I` exactly, and `jt` commutes with every `T_i` exactly.
- **Conjugates.** `T^y xt_v T^(-y)` sends `h ⊗ delta_a` to `xi_(v, overline(a+y)) h ⊗ delta_a`. So every word in (H2)--(H5) is block diagonal, with block at `a` equal to the same word in the operators `xi_(v, overline(a+y))`.
- **Good copies.** If `a_i <= N - 1 - R` for all `i`, then no index wraps. Each placement `S_c + a` lies in `V × B_N`, so the block is a relator of `P_N` and has defect `<= eps`. This covers the blocks of (H2), `j^2` and `[j, x_v]` at every `a`, since those words involve one site.
- **Bad copies.** At most `d R N^(d-1)` copies have some `a_i >= N - R`. There a placement block is a unitary, hence within `2` of `I`.
- **Defect.** The squared normalized norm on `K` is the average over `a` of the squared normalized block norms. So every relator has defect at most

  ```text
  sqrt(eps^2 + 4 d R / N)  <=  eps + 2 sqrt(d R / N).
  ```

  (H1) and `[j, t_i]` hold exactly, and `||jt + I||_2 = ||iota + I||_2 <= eps`.

## Step 2. Item 2: restrict along ordered translations

Let `u_v`, `iota`, `tau_1,...,tau_d` be an `(eps,J)`-model of `Gamma(L)`. For `y in B_N`, put `xi_(v,y) = tau^y u_v tau^(-y)`.

- **Squares.** `xi_(v,y)^2` is a conjugate of `u_v^2`, so its defect is `<= eps`. The same holds for `iota^2`.
- **Centrality of `J`.** `tau^y` has at most `d(N-1)` letters. Each letter commutes with `iota` up to `eps`, since `||iota tau_i - tau_i iota||_2 = ||[iota, tau_i] - I||_2`. So `||iota tau^y - tau^y iota||_2 <= dN eps`.
  - Put `iota' = tau^(-y) iota tau^y`, so that `||iota' - iota||_2 <= dN eps`.
  - Then `[iota, xi_(v,y)] = tau^y [iota', u_v] tau^(-y)`.
  - Since `[iota', u_v]` is within `2 dN eps` of `[iota, u_v]`, the defect is `<= (1 + 2dN) eps`.
- **Placements.** Let `S_c + a ⊂ V × B_N` and `(v,y') in S_c`, so `y' in [0,R]^d`.
  - Rewriting `tau^(a+y')` as `tau^a tau^(y')` takes at most `(dR)(dN)` adjacent swaps `tau_k tau_l -> tau_l tau_k`. Each costs `<= eps` by (H1). So `||tau^(a+y') - tau^a tau^(y')||_2 <= d^2 N R eps`.
  - Hence `xi_(v,a+y')` is within `2 d^2 N R eps` of `tau^a X_(v,y') tau^(-a)`, where `X_(v,y') = tau^(y') u_v tau^(-y')`.
  - Also, `iota` is within `dN eps` of `tau^a iota tau^(-a)`.
  - So the placement relator is within `L_c (2 d^2 N R + dN) eps <= 3 L_c d^2 N R eps` of `tau^a (origin relator) tau^(-a)`, whose defect is `<= eps`.
- **Total.** Every relator of `P_N` has defect `<= (1 + 3 L_c d^2 N R) eps`, and `||iota + I||_2 <= eps`.

## Step 3. Item 3

- **(⇒)** Fix `N` and `delta > 0`. Choose an `(eps,J)`-model of `Gamma(L)` with `(1 + 3 L_c d^2 N R) eps <= delta`, and apply Step 2.
- **(⇐)** Given `eps' > 0`, choose `N >= 16 d R / eps'^2` and an `(eps'/2, J)`-model of `P_N`. Step 1 gives an `(eps', J)`-model of `Gamma(L)`.
- **Smaller boxes.** For `M <= N`, the generators and relators of `P_M`, on the corner box `B_M ⊂ B_N`, are among those of `P_N`. So restriction gives models of `P_M` at the same `eps`.

## Step 4. Item 4

- **`Gamma` and `Sol`.** By Step 0, `Sol(L)` embeds in `Gamma(L)`, so `J != 1` in one iff in the other.
- **`Sol` to `P_N`.** Every relator of `P_N` is a relator of `Sol(L)`. So `X_(v,y) |-> X_(v,y)`, `J |-> J` defines a homomorphism `P_N -> Sol(L)`, and `J != 1` in `Sol(L)` forces `J != 1` in `P_N`.
- **`P_N` to `Sol`.** Suppose `J = 1` in `Sol(L)`. The identity is a finite product of conjugates of relators, and it involves finitely many sites and placements. A translation is an automorphism of `Sol(L)` fixing `J`; apply one so that all these sites lie in `[0, infinity)^d`. They then lie in some box `B_N`, and the same identity holds in `P_N`.

## Step 5. Item 5

Combine Items 3 and 4. Item 3 says `Gamma(L)` fails R^U-satisfiability iff some `P_(N_0)` does. Monotonicity then gives failure for every `N >= N_0`. Item 4 turns `J != 1` in `Gamma(L)` into `J != 1` in every `P_N`.
