---
rg: 2
id: fp-simple-weak-soficity-is-finite-field-linear-soficity-proof
kind: route
title: Reduce to Q/Q_0, push the tuple into the socle product by words in the third derived subgroup, apply the finite simple templates, and pull back through Nikolov-Segal
target: fp-simple-weak-soficity-is-finite-field-linear-soficity
requires: [relator-width-bounded-by-almost-simple-quotients, simple-group-relator-templates-over-finite-simple-groups, simple-group-psl-width-is-finite-field-linear-soficity]
---

`Cons_k^H` is the set of products of at most `k` `H`-conjugates of elements `r(a)^(+-1)`, for a tuple `a` understood
from context. `F = F(X)` and `N = <<R>>`.

## 1. (i) => (ii)

Fix once, in `F`:
- **Derived words.** `G` is perfect, so `G = G^(3)`, and the image of `F^(3)` in `G` is `G^(3) = G`. For each `x` fix
  `w_x in F^(3)` with `x^-1 w_x in N`, and an expression `x = w_x rho_x` with `rho_x` a product of `k_0` conjugates
  of relators.
- **Substituted relators.** For each `r in R`, `r(w) := r((w_x)_x)` maps to `r(x) = 1` in `G`, so it lies in `N`. Fix an
  expression of `r(w)` as a product of `k_1` conjugates of relators.

Let `Q` be finite and `a in Q^X`. We may take `Q = <a>`. Let `B = Q/Q_0` and `b` the image of `a`.

**Step 1: the socle product.** `Q_0` is the intersection of the normal subgroups `T` with `Q/T` almost simple. So `B`
embeds in `prod_T B_T`, projecting onto each `B_T = Q/T`, with `S_T <= B_T <= Aut(S_T)` and `S_T` non-abelian simple.
Put `L = B ∩ prod_T S_T`, a normal subgroup of `B`.
- `B/L` embeds in `prod_T B_T/S_T <= prod_T Out(S_T)`. That product is soluble of derived length `<= 3` by the strong
  Schreier conjecture. So `B^(3) <= L`.
- The projection of `L` to `S_T` is normal in `B_T` and contains `B_T^(3) ⊇ S_T`, since `S_T` is perfect. So `L` is a
  subdirect product of the `S_T`.
- **Lemma.** A subdirect product `L` of non-abelian simple groups `S_1, ..., S_t` is isomorphic to a direct product of
  some of them. *Proof by induction on `t`.* Drop the last coordinate. The image `L'` is subdirect in
  `S_1 x ... x S_(t-1)`. The kernel `L ∩ S_t` is normal in `L`, and its projection is normal in `S_t`, so it is `1` or `S_t`.
  If it is `S_t`, then `L = L' x S_t`. Otherwise `L ≅ L'`.

**Step 2: the socle tuple.** Put `c_x = w_x(b)`. Then `c_x in B^(3) <= L`, so `c in L^X`.
- By `simple-group-relator-templates-over-finite-simple-groups` (Corollary), under (i), each `c_x` is a product of
  at most `K` `L`-conjugates of elements `r(c)^(+-1)`. `K = K(G)` does not depend on the number of factors.
- `r(c) = r(w)(b)` is a product of `k_1` `B`-conjugates of relator values `r'(b)^(+-1)`, by the fixed expression. So
  `c_x in Cons_(K k_1)^B`.
- `b_x = w_x(b) rho_x(b) = c_x rho_x(b) in Cons_(K k_1 + k_0)^B`.

So `w_B(b) <= K k_1 + k_0 =: K_B`, uniformly in `Q` and `a`.

**Step 3: pulling back.** By `relator-width-bounded-by-almost-simple-quotients`, items (a) and (b):
- `nu_0(a) <= |X| K_B`;
- `nu(a) <= r F_0(r)` with `r = 2(|X| K_B + |R|)`;
- `w_Q(a) <= N_0 + 4 nu F_1(2 nu)`.

This bound is uniform. Conjugators in `<a>` are conjugators in `Q`.

## 2. (ii) => (iii)

Suppose `G` is weakly sofic. Glebsky--Rivera Definition 4.1 (`glebsky-rivera-w-sofic-criterion-citation`) gives
`alpha > 0` and, for every finite `Phi` and `eps > 0`, a finite group `H` with a bi-invariant metric `d` and a
`(Phi, eps, alpha)`-homomorphism `phi`. Choose `x in X` with `x != 1` in `G`, and take `Phi` containing `X`, `x` and
all prefixes of the relators. Put `a_y = phi(y)` and `l(h) = d(h, 1)`.
- `l` is conjugation invariant and subadditive. The multiplicativity defect on prefixes gives `l(r(a)) <= C eps` for
  every `r`, with `C` depending on the relator lengths, as in item 3 of `perfect-group-relator-width-over-nilpotent-groups`.
- The separation condition gives `l(a_x) >= alpha - C eps`, since `phi(1)` has length `< eps`.
- By (ii), `l(a_x) <= K(G) C eps`.

That is impossible for `eps < alpha / ((K(G) + 1) C)`.

## 3. (iii) => (i)

`simple-group-psl-width-is-finite-field-linear-soficity` records that linear soficity over finite fields implies weak
soficity. The rank-metric ultraproduct gives weak models into `GL_n(F_q)` with the normalized rank length, which is
bi-invariant. Contrapositively, (iii) gives (i).

## 4. Remarks

- **What is used about `G`.** Step 1 needs no finite quotients, through item (b). Step 2 needs the simple-group
  templates, which need simplicity and (i). Section 2 needs nothing beyond finite presentation.
- **Constants.** `K_B` comes from the templates, and the pull-back constants come from Nikolov--Segal. Nothing is
  explicit, since `F_0` and `F_1` are not explicit on record.
