---
rg: 2
id: braid-non-self-similarity-via-geometric-injections
kind: route
title: Geometric rigidity of injective virtual endomorphisms of B_n mod center excludes faithful state-closed actions for n >= 4
target: braid-groups-on-four-or-more-strands-are-not-self-similar
requires:
  - finite-index-injections-into-braid-quotients-are-geometric
---

## Notation

- Fix `n >= 4` and write `G = B_n`.
- `z = Delta^2` generates `Z(G)` (Chow).
- `e : G -> Z` is the exponent sum. Since `e(z) = n(n-1) != 0`,
  `Z(G) ∩ ker e = 1`, and in particular `[G,G] ∩ Z(G) = 1`.
- `pi : G -> Q = G / Z(G)`. By Bell–Margalit (arXiv:math/0403145, §1, §3),
  `Q = Mod(D_n)`, which is a finite-index subgroup of
  `Gamma = Mod^±(S_(0,n+1))`: the orientation-preserving mapping classes fixing
  one puncture.
- `core_X(Y)` is the largest subgroup of `Y` normal in `X`.

## Lemma A (normal subgroups do not commute)

Let `Lambda <= Gamma` have finite index, and let `M, N` be nontrivial normal
subgroups of `Lambda`. Then `[M,N] != 1`. Hence, for nontrivial normal
subgroups `N_1, ..., N_r` of `Lambda`, the iterated commutator
`[...[N_1,N_2],...,N_r]` is nontrivial and lies in `∩ N_j`.

*Proof sketch; standard facts, cited.* `S = S_(0,n+1)` has at least 5
punctures.

1. **The centralizer of a finite-index subgroup of Gamma is trivial.** Such a
   centralizer fixes the stable laminations of every pseudo-Anosov of `Lambda`.
   These are dense in `PMF`, so it acts trivially on `PMF` and on the curve
   complex, and `Mod^±(S)` acts faithfully there when `S` has at least 5
   punctures (Korkmaz; Ivanov, *Subgroups of Teichmüller Modular Groups*, 1992).
2. **A nontrivial normal subgroup `N` of `Lambda` contains a pseudo-Anosov.**
   By Ivanov's trichotomy, `N` is finite, reducible, or contains a
   pseudo-Anosov.
   - If `N` is infinite and reducible, its canonical reduction system is
     nonempty and `Lambda`-invariant. That is impossible, since `Lambda`
     contains pseudo-Anosovs.
   - If `N` is finite and nontrivial, `C_Lambda(N)` has finite index and
     centralizes `N`, contradicting step 1.
3. **Two independent pseudo-Anosovs in `N`.** Take a pseudo-Anosov `g` in `N`
   and a pseudo-Anosov `h` in `Lambda` with laminations disjoint from those of
   `g`. For large `k`, `g' = h^k g h^-k` lies in `N` and has laminations
   disjoint from those of `g`.
4. **Conclusion.** If `[M,N] = 1`, every element of `M` preserves the lamination
   pairs of `g` and of `g'`. So `M` lies in `E(g) ∩ E(g')`. `E(g)` is virtually
   cyclic (McCarthy), and its infinite-order elements are pseudo-Anosovs with
   the laminations of `g`, which cannot fix those of `g'`. So `M` is a torsion
   subgroup of a virtually cyclic group, hence finite, normal and nontrivial,
   contradicting step 2.

For the iterated form: `[A,B] <= A ∩ B` for normal `A, B`, and each iterated
commutator is again normal and nontrivial. `∎`

## Lemma B (the two kinds of virtual endomorphism)

Let `H <= G` have finite index, let `f : H -> G` be a homomorphism, and put
`L = f^-1(Z(G))`, a normal subgroup of `H`.

**(a)** If `pi(L) != 1`, there is a normal subgroup `M_f` of `G` with
`pi(M_f) != 1` and `f(M_f) = 1`.

*Proof.* `f(L)` is central, so `[L,L] <= ker f`. Put `H_0 = core_G(H)` and
`X = [L,L] ∩ H_0`, which is normal in `H`. Its `G`-conjugates are finitely
many and each is normal in `H_0`. Let `M_f` be their intersection. It is normal in
`G`, and `f(M_f) = 1` because `M_f <= X <= [L,L]`. To see `pi(M_f) != 1`, argue
with subgroups:
- `pi(L)` and `pi(H_0)` are nontrivial normal subgroups of `pi(H)`, so
  `pi([[L,L],H_0]) = [[pi L, pi L], pi H_0] != 1` by Lemma A. Also
  `[[L,L],H_0] <= X`, so `pi(X) != 1`.
- Write the conjugates as `X_1, ..., X_m`. Each is normal in `H_0` with
  `pi(X_j) != 1`. The iterated commutator subgroup
  `C = [...[X_1,X_2],...,X_m]` lies in `M_f`, and
  `pi(C) = [...[pi X_1, pi X_2],...,pi X_m] != 1` by Lemma A inside `pi(H_0)`.

So `pi(M_f) != 1`. `∎`

**(b)** If `pi(L) = 1`, put `W = H ∩ ker e`. Then:
- `pi` is injective on `W`;
- `pi(W)` has finite index in `Q`, because `(ker e ∩ H) Z(G)` has finite index
  in `G`;
- `psi_f : pi(W) -> Q`, `pi(w) -> pi(f(w))`, is an injective homomorphism. If
  `pi f(w) = 1`, then `w` lies in `L`, which is central, and in `ker e`, so
  `w = 1`.

By `finite-index-injections-into-braid-quotients-are-geometric`, there is
`phi_f` in `Gamma` with `psi_f(x) = phi_f x phi_f^-1` for all `x` in `pi(W)`.

## Faithful state-closed actions give invariant normal subgroups

Suppose `G` acts faithfully on `T_d` with state-closed image.

**Setup.** Pick `x_1, ..., x_r` representing the first-level orbits. Put
`H_i = Stab_G(x_i)`, of finite index, and `f_i(h) = h|_(x_i)`. The section map
is a homomorphism on `H_i`, and it takes values in `G` because the image is
state-closed.

**The joint core acts trivially.** Let `K` be normal in `G`, contained in every
`H_i`, with `f_i(K) <= K` for all `i`.
- `K` fixes every first-level vertex `g x_i`, since `Stab(g x_i) = g H_i g^-1`
  contains `K`.
- For `k` in `K`, `k|_(g x_i) = g|_(x_i) · f_i(g^-1 k g) · (g|_(x_i))^-1` lies in
  `K`, using `g^-1|_(g x_i) = (g|_(x_i))^-1`.
- By induction on the level, `K` acts trivially, so faithfulness forces `K = 1`.

This is the Dantas–Santos–Sidki correspondence (arXiv:2004.08941).

**Building a nontrivial such K.** Split the indices by Lemma B into kinds (a)
and (b).
1. Put `H* = core_G(∩ H_i)`, and let `N_a` be the intersection of the `M_(f_i)`
   over `i` of kind (a), or `G` if there are none.
2. Put `M = [H*,H*] ∩ N_a`, a normal subgroup of `G`. To see `pi(M) != 1`,
   argue with subgroups. Put `X = [H*,H*]` and `Y = N_a ∩ H*`, both normal in
   `G`.
   - `pi(X) = [pi H*, pi H*] != 1` by Lemma A, since `pi(H*)` is a nontrivial
     normal subgroup of `Q`.
   - `pi(Y) != 1`. The iterated commutator subgroup
     `C = [...[H*, M_(f_1)],...,M_(f_r)]` over the kind-(a) indices lies in `Y`
     (or put `C = H*` if there are none), and
     `pi(C) = [...[pi H*, pi M_(f_1)],...,pi M_(f_r)] != 1` by Lemma A.
   - `[X,Y] <= X ∩ Y <= M`, and `pi([X,Y]) = [pi X, pi Y] != 1` by Lemma A.

   So `pi(M) != 1`. Since `M <= [G,G]`, `pi` is injective on `M`.
3. `A = pi(M)` is normal in `Q`. Put `Q_0 = core_Gamma(Q)`. The distinct
   `Gamma`-conjugates `gamma A gamma^-1` are finitely many. Each meets `Q_0` in
   a subgroup normal in `Q_0`, which is nontrivial by Lemma A, as it contains
   `[gamma A gamma^-1, Q_0]`.
4. `B = ∩_gamma (gamma A gamma^-1 ∩ Q_0)` is normal in `Gamma` and nontrivial
   (Lemma A), and `B <= A`.
5. Put `K = M ∩ pi^-1(B)`. Then `K` is normal in `G`, `pi(K) = B != 1`, and
   `K <= [H*,H*] <= ∩_i (H_i ∩ ker e)`.

**K is invariant under every f_i.**
- *Kind (a).* `K <= N_a <= M_(f_i) <= ker f_i`, so `f_i(K) = 1`.
- *Kind (b).* Let `k` be in `K`.
  - `k` is a product of commutators of elements of `H* <= H_i`, so `f_i(k)`
    lies in `[G,G]`.
  - `k` lies in `W_i`, so `pi(f_i(k)) = phi_i pi(k) phi_i^-1` lies in `B`,
    because `B` is normal in `Gamma`.
  - Pick `k'` in `K` with `pi(k') = pi(f_i(k))`. Then `f_i(k) = k' z^j`, and
    `z^j` lies in `[G,G] ∩ Z(G) = 1`, so `f_i(k) = k'` lies in `K`.

So `K != 1` lies in the joint core, contradicting faithfulness. Hence `B_n` is
not self-similar for `n >= 4`. `∎`

## Where each hypothesis is used

- **`n >= 4`.** At least 5 punctures, needed for Lemma A (trivial centralizers,
  faithful action on the curve complex) and for the rigidity claim. For `n = 3`,
  rigidity fails: conjugation by `diag(2,1)` on `PSL_2(Z)`.
- **The exponent sum.** It is only used to make `pi` injective on `W` and
  `[G,G] ∩ Z(G) = 1`.
- **Transitivity.** Never assumed.
