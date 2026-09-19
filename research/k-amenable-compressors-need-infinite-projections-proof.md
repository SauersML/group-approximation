---
rg: 2
id: k-amenable-compressors-need-infinite-projections-proof
kind: route
title: The regular trace kills the defect, Folner vectors lift that to the maximal algebra over amenable subgroups, and K-amenability plus the Grothendieck construction make the defect an infinite projection otherwise
target: k-amenable-compressors-need-infinite-projections
requires: []
---

Notation is as in the claim. `A = C*_max(L)`, `lambda = lambda_L`, and
`tau(x) = <lambda(x) delta_e, delta_e>` is the regular trace on `A`. It is a
tracial state, since it is the canonical trace of `C*_r(L)` composed with
`lambda`.

## 0. The ambient order (context for the claim, not used below)

Let `sigma : G -> U(B)` be a homomorphism and extend it to
`sigma : C*_max(G) -> B`. Write `iota : A -> C*_max(G)` for the map induced by
the inclusion. The two `*`-homomorphisms `Ad(sigma(u)) o sigma o iota` and
`sigma o iota o alpha_*` agree on group elements of `L`, because
`u l u^-1 = alpha(l)`. So they agree on `A`. Hence

```text
U P U* = sigma(iota(alpha_*(p))) >= sigma(iota(p)) = P,
```

since `*`-homomorphisms preserve the order of projections.

## 1. Regular invisibility

1. **`tau o alpha_* = tau`.** For `x = sum_g a_g g` in `C[L]`,
   `tau(alpha_*(x))` is the sum of `a_g` over all `g` with `alpha(g) = e`.
   Since `alpha` is injective, this is `a_e = tau(x)`. Both sides are states
   on `A`, and `C[L]` is dense in `A`, so they are equal.
2. **`tau(q) = 0`.** Indeed `tau(q) = tau(alpha_*(p)) - tau(p) = 0`.
3. **`lambda(q) = 0`.** Put `y = lambda(q)`, a projection. Then
   `||y delta_e||^2 = <y delta_e, delta_e> = tau(q) = 0`. The right regular
   unitaries `rho(g)` commute with `lambda(L)`, and `delta_g = rho(g^-1) delta_e`.
   So `y delta_g = rho(g^-1) y delta_e = 0` for every `g`, and `y = 0`.

## 2. Amenable subgroups

We use amenability in Folner form: there are finite nonempty `F_n` in `L`
with `|g F_n \ F_n| / |F_n| -> 0` for every `g`. Put
`xi_n = |F_n|^(-1/2) 1_(F_n)` in `l^2(L)`. Then
`||lambda(g) xi_n - xi_n|| -> 0` for every `g`.

**Claim.** `||pi(x)|| <= ||lambda(x)||` for every unitary representation
`pi` of `L` on a Hilbert space `H` and every `x` in `C[L]`. So `lambda` is
isometric on `C[L]`, hence injective on `A`.

*Proof.*

- **Fell absorption.** Define `W` on `H (x) l^2(L)` by
  `W(eta (x) delta_g) = pi(g) eta (x) delta_g`. It is unitary, and
  `W (1 (x) lambda(g)) W* = pi(g) (x) lambda(g)`. So
  `||(pi (x) lambda)(x)|| = ||lambda(x)||`, because `1 (x) lambda` is a
  multiple of `lambda`.
- **The estimate.** Let `x = sum_(g in S) a_g g` with `S` finite, and let
  `eta` be a unit vector. Then

  ```text
  || (pi (x) lambda)(x)(eta (x) xi_n) - pi(x) eta (x) xi_n ||
      <= sum_(g in S) |a_g| ||lambda(g) xi_n - xi_n||  ->  0.
  ```

  So `||pi(x) eta|| <= ||(pi (x) lambda)(x)|| + o(1) = ||lambda(x)|| + o(1)`.
  Take the supremum over `eta`. ∎

By definition of the maximal norm, `||x||_A` is the supremum of `||pi(x)||`
over all such `pi`, and `lambda` is one of them. So the claim gives
`||x||_A = ||lambda(x)||` on `C[L]`, and by continuity on all of `A`. Hence
`lambda` is isometric, so injective, and `lambda(q) = 0` gives `q = 0`.

Then `alpha_*(p) = p` in `A`. By Section 0, `U P U* = P` for every
representation of every ambient group.

## 3. The K-theoretic dichotomy

We use the standard picture of `K_0` of a unital C*-algebra.

- `P_n(A)` is the set of projections in `M_n(A)`.
- `e ~_0 f`, for `e` in `P_n(A)` and `f` in `P_m(A)`, means that `v*v = e`
  and `v v* = f` for some `v` in `M_(m,n)(A)`.
- `D(A)` is the set of classes of all projections under `~_0`, and it is an
  abelian semigroup under `[e] + [f] = [e (+) f]`.
- `K_0(A)` is its Grothendieck group.

Two facts about the Grothendieck construction are used.

- **(G1)** Equality of classes. In the Grothendieck group, `[a] = [b]` holds
  iff `a + c = b + c` for some `c` in `D(A)`.
- **(G2)** Orthogonal sums. If `e` and `f` are orthogonal projections in
  `M_n(A)`, then `e + f ~_0 e (+) f`.

The proof has four steps.

1. **The class of the defect.**
   - `p` and `q` are orthogonal, and `p + q = alpha_*(p)`. By (G2),
     `[p] + [q] = [alpha_*(p)] = alpha_*[p]`, so `x = [q] = alpha_*[p] - [p]`.
   - By naturality of `K_0`, `(lambda)_*(x) = [lambda(q)] = [0] = 0`, using
     Section 1.
2. **Injectivity gives `x = 0`.** If `(lambda)_*` is injective on `K_0`,
   then `x = 0` follows from the previous step.
3. **An infinite projection when `q != 0`.**
   - Suppose `x = 0`, that is, `[q] = [0_1]`. By (G1) there is `r` in
     `P_k(A)` with `q (+) r ~_0 0_1 (+) r`, and both sides lie in
     `P_(1+k)(A)`.
   - Let `v` implement `q (+) r ~_0 0_1 (+) r`. Put `s = 0_1 (+) (1_k - r)`.
     Then `s` is orthogonal to both `q (+) r` and `0_1 (+) r`.
   - Since `v = v (q (+) r) = (0_1 (+) r) v`, both `v s` and `s v` vanish, as
     do their adjoints. So `(v + s)*(v + s) = (q (+) r) + s` and
     `(v + s)(v + s)* = (0_1 (+) r) + s`. Hence

     ```text
     e := q (+) 1_k   ~   f := 0_1 (+) 1_k      in M_(1+k)(A),
     ```

     with `f <= e`, and `f != e` exactly when `q != 0`.
4. **Stable finiteness forces `q = 0`.**
   - Let `B = M_(1+k)(A)` be finite, and let `w` in `B` satisfy `w*w = e`
     and `w w* = f`, with `f <= e`. This is the argument at the end of the
     proof of the corona finiteness lemma in `non_mf_groups_exist.tex`,
     reproduced here.
   - `w = w w* w = f w = e f w = e w`, and `w = w e`.
   - Put `v = w + (1 - e)`. Then `w*(1 - e) = w* e (1 - e) = 0` and
     `(1 - e) w = (1 - e) e w = 0`, so `v* v = e + (1 - e) = 1`.
   - `B` is finite, so `v` is unitary. Hence `1 = v v* = f + (1 - e)`, which
     gives `f = e` and `q = 0`.

## 4. Imports for a-T-menable subgroups

These are needed only for item 4 of the claim and for the Haagerup
corollary. Items 1 to 3 use none of them.

**(I1)** Lück--Reich, *The Baum--Connes and the Farrell--Jones Conjectures in
K- and L-Theory*, arXiv:math/0402405, Section 5.1.1. It is quoted verbatim,
apart from typesetting, in `research/artifacts/bc-gap-label-subgroup-support-2026-09-12.md`
(item (I2) there):

> Theorem 5.1. (Baum-Connes Conjecture with Coefficients and a-T-menable
> Groups). The discrete group G satisfies the Baum-Connes Conjecture with
> Coefficients 4.3 and is K-amenable provided that G is a-T-menable.
> This theorem is proved in Higson-Kasparov [149, Theorem 1.1] [...]

**(I2)** L. Guo, H. Wang, X. Yao, *The K-theory of maximal and reduced Roe
algebras for Hecke pairs with equivariant coarse embeddings*,
arXiv:2601.14682, Section 1. The HTML was fetched on 2026-09-19, and math was
rendered from its alttext. It reads, verbatim:

> Question 1 . Let $\Gamma$ be a countable discrete group. When does the
> canonical quotient map induce an isomorphism in $K$ -theory
> $\lambda_{*}:K_{*}(B\rtimes\Gamma)\to K_{*}(B\rtimes_{r}\Gamma)$ for any
> $\Gamma$ - $C^{*}$ -algebra $B$ ?

> Remarkably, J. Cuntz [ 4 ] showed that for free groups, the map $\lambda$
> still induces an isomorphism in $K$ -theory, despite not being an
> isomorphism at the level of $C^{*}$ -algebras. Motivated by this, Cuntz
> introduced K-amenability for discrete groups as a sufficient condition
> ensuring Question 1 , i.e., $\lambda_{*}$ is an isomorphism.

Here [4] is J. Cuntz, *K-theoretic amenability for discrete groups*,
J. Reine Angew. Math. 344 (1983), 180--195. The same introduction also says:

> A major milestone was achieved by Higson and Kasparov [ 12 ] , who applied
> this technique to establish the Baum–Connes conjecture with coefficients
> together with their $K$ -amenability for a-T-menable groups.

**Specialization.** Take `B = C` with the trivial action. Then
`C ⋊ Gamma = C*_max(Gamma)`, `C ⋊_r Gamma = C*_r(Gamma)`, and `lambda` is
the regular representation. So (I1) and (I2) give:

> for a-T-menable `L`, `(lambda_L)_* : K_0(C*_max L) -> K_0(C*_r L)` is an
> isomorphism.

With Section 3 this proves item 4 of the claim.

**Cross-check.** Amenable `L` are a-T-menable, and Section 2 proves the
stronger statement `q = 0` for them directly, with no import.

## 5. Why a vanishing defect makes the criterion idle

- **What the criterion uses.** In `thm:transport` the only input that
  distinguishes asymptotic matrix representations from arbitrary unitary
  representations is the stable finiteness of the norm matrix corona
  `\mathcal B`. That input is used exactly to upgrade `P <= U P U*` (the
  equivalent form of `U* P U <= P`) to `P = U P U*`.
- **When `q = 0`.** Then `alpha_*(p) = p` in `C*_max(L)`, and Section 0 gives
  `U P U* = P` in every unitary representation of every group containing
  `(L, u)`. This holds on every Hilbert space, including representations
  that are not weakly contained in any MF family.
- **Consequence.** Whatever the proof deduces afterwards from `P = U P U*`,
  it deduces for all unitary representations. So it cannot separate MF images
  of `G` from arbitrary ones.

Sections 2 and 3 show that `q = 0` in two cases:

- when `L` is amenable;
- when `L` is K-amenable, for instance a-T-menable, and `C*_max(L)` is stably
  finite.

## 6. Scope, and what is not covered

- **Model-specific projections.** A projection of the corona that is not the
  image of a fixed element of `C*_max(L)` is not covered. Examples are
  projections built from the particular asymptotic representation, such as
  spectral projections of `sum a_l sigma(l)` at a gap that exists only in the
  model. The w9 attempt on `jacobson-regular-character-not-mf-without-property-t`
  reached the same boundary: only model-specific arguments remain.
- **Certificates drawn from the ambient algebra.** A projection `p` of
  `C*_max(G)` itself with `u* p u <= p` has defect
  `d = p - u* p u`. Here `[d] = 0` in `K_0(C*_max G)` automatically, because
  `u* p u` is unitarily equivalent to `p`. And `lambda_G(d) = 0` by the
  argument of Section 1 with the regular trace of `G`. So the defect is always
  a `K_0`-trivial infinite projection of `C*_max(G)` when it is nonzero. That
  is the content of `maximal-group-cstar-infinite-under-strict-compression` in
  the Kazhdan case.
- **What the subgroup-intrinsic hypothesis adds.** With `p` in `C*_max(L)` and
  `alpha` acting on `L`, the infiniteness must already be present in the
  subgroup's own maximal algebra when `L` is K-amenable. If `L` is not
  K-amenable, it may instead be carried by a nonzero class in
  `ker (lambda_L)_*`.
- **Consistency with the Kazhdan template.**
  - For infinite Kazhdan `L`, the class `[e_L]` is a nonzero element of
    `ker (lambda_L)_*`: the trivial character maps it to `1` in
    `K_0(C) = Z`, while `lambda_L(e_L) = 0` because `lambda_L` has no nonzero
    invariant vectors.
  - So Kazhdan groups are not K-amenable, as (I1) also records, and the
    theorem places no restriction on them.
- **Where the injectivity of `alpha` is used.** It is used only in Section 1.
  A conjugation `Ad(u)` restricted to `L` is always injective.

## 7. Use for the Kazhdan-free goal (context, not load-bearing)

Inside `Delta ~= R^x`, with `R = L_(F_2)(1,2)` (`leavitt-st20-t-free-holes-hold-via-kazhdan`):

- **Thompson's group `V`.** `V` sits in the elementary group of `R`
  (`leavitt-cylinder-swaps-generate-thompson-in-el`) and has the Haagerup
  property (`thompson-v-has-haagerup-property`).
- **Consequence.** By item 4, a non-idle certificate for `V` exists only if
  `C*_max(V)` is not stably finite, and then the defect is a `K_0`-trivial
  infinite projection lying in `ker lambda_V`.
- **Other a-T-menable subgroups.** The same holds for every a-T-menable
  subgroup: free subgroups, Thompson's `F` and `T`, and the lamplighter
  subgroups of the `EL` blocks.
- **Amenable subgroups.** No certificate over an amenable subgroup is non-idle.
- **What remains.** A subgroup-intrinsic proof of the goal therefore needs
  either a non-K-amenable `L` whose `K_0` ghost `ker (lambda_L)_*` carries the
  defect (the relative-rigidity regime), or a Haagerup `L` with an infinite
  projection in `M_(k+1)(C*_max L)`.
