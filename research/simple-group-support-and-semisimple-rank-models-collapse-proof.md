---
rg: 2
id: simple-group-support-and-semisimple-rank-models-collapse-proof
kind: route
title: Normalize on the moved set or moved subspace, then use simplicity to make the ultraproduct homomorphism injective
target: simple-group-support-and-semisimple-rank-models-collapse
requires: []
---

Throughout, `G = <X | R>` is infinite, finitely presented and simple, `g_0 != 1`,
and `f` is nondecreasing and subadditive with `f(0) = 0`.

## 0. Weak soficity of a simple group needs one separated element

- **Models give weak soficity.** Given models `a^(n)` in `(H_n, l_n)` with parameter
  `eps_n -> 0`, put `Q = prod_omega H_n / N_omega`, with `N_omega` the sequences of
  length tending to `0` along `omega`. Here `H_n` is restricted to sequences of
  bounded length, which contain the generator images.
  - `x -> [(a_x^(n))]` kills every relator, so it defines a homomorphism `G -> Q`.
  - `g_0` has limit length at least `1`, so the homomorphism is nontrivial.
  - Its kernel is normal and `G` is simple, so it is injective.
  - A countable subgroup of a metric ultraproduct of finite groups is weakly sofic
    (`metric-ultraproduct-surjunctivity-from-weak-sofic-case`, second bullet).
- **Weak soficity gives models.** Pick a weakly sofic approximation on a finite set
  containing `X`, `g_0` and the prefixes of all relators. For a finitely presented
  group, small multiplicative defect on that set bounds the relator lengths by a
  constant times the defect. Rescale the length so that `g_0` has length at least `1`.

## 1. Support type

**Lemma 1.1 (moved set).** Let `a in Sym(Omega)^X` and
`Omega_0 = union_x supp(a_x)`.
- Every word in the `a_x` fixes `Omega \ Omega_0` pointwise.
- `Omega_0` is invariant.
- `|Omega_0| <= sum_x |supp a_x|`.

*Proof.* A point fixed by every generator is fixed by every word. The complement of
an invariant set is invariant. The last item is the union bound.

**Lemma 1.2 (dichotomy).** If `G` is not sofic, there is `eps_0 > 0` such that every
finite `Omega` and every `a in Sym(Omega)^X` satisfy
`max_(r in R) |supp r(a)| >= eps_0 |Omega_0|`.

*Proof.* Suppose not. Then there are tuples `a^(n)` with `Omega_0^(n)` nonempty and
`max_r |supp r(a^(n))| < |Omega_0^(n)|/n`.
- **Restrict and normalize.** Restrict to `Omega_0^(n)`. This is allowed by Lemma 1.1,
  and it changes no support of any word. Use the normalized Hamming distance on
  `Sym(Omega_0^(n))`. Relator values then have distance `< 1/n` from `1`.
- **One generator stays far.** By Lemma 1.1 some generator `x_n` has
  `|supp a_(x_n)| >= |Omega_0^(n)|/|X|`. Passing to a subsequence, `x_n = x` is
  constant.
- **The homomorphism.** Along `omega` we get a homomorphism
  `psi : G -> prod_omega Sym(Omega_0^(n)) / N_omega`, with the normalized Hamming
  metric, and `psi(x) != 1`.
- **Contradiction.** Simplicity makes `psi` injective. A countable group embedding
  in a Hamming metric ultraproduct of finite symmetric groups is sofic (Elek--Szabo's
  characterization of soficity). This contradicts the hypothesis.

**Proof of Theorem item 1, forward direction, with the constant.** Let `G` be nonsofic
and `(H, Omega, f, a)` a support-type model with parameter `eps`.
- **Transfer.** The action gives permutations of `Omega`, and supports agree with
  those in `H`.
- **Setup.** Put `t = |supp g_0(a)| >= 1`. Then `t <= |Omega_0|`, so by Lemma 1.2 some
  relator satisfies `|supp r(a)| >= eps_0 t`. Being an integer, `|supp r(a)|` is at
  least `ceil(eps_0 t)`.
- **Estimate.** With `k = ceil(1/eps_0)` we have `k ceil(eps_0 t) >= t`. Monotonicity
  and subadditivity give
  ```text
  1 <= f(t) <= f(k ceil(eps_0 t)) <= k f(ceil(eps_0 t)) <= k f(|supp r(a)|) <= k eps.
  ```
- **Conclusion.** So `eps >= 1/k`, and models with smaller parameter do not exist.

**Converse.** A sofic group has permutation models with normalized Hamming defect
tending to `0` and `g_0` moving at least half the points. Take `f(s) = 2s/|Omega|`.

## 2. Semisimple rank type

**Lemma 2.1 (moved subspace).** Let `rho : H -> GL(V)` with `char F` not dividing
`|H|`, let `h_x in H` for `x in X`, and let `P = <h_x>`. Put
`W = sum_x im(rho(h_x) - 1)`.
1. `W = sum_(g in P) im(rho(g) - 1)`, and `W` is `P`-invariant.
2. `V = V^P (+) W`.
3. For `g in P`, `rk(rho(g) - 1) = rk((rho(g) - 1)|_W)`.
4. `dim W <= sum_x rk((rho(h_x) - 1)|_W)`.

*Proof.*
1. `gh - 1 = (g - 1)h + (h - 1)`, and `im((g-1)h) = im(g - 1)`. Also
   `g^-1 - 1 = -(g - 1)g^-1`. So images of words lie in `W`, by induction on length.
   Invariance: `gw = w + (g-1)w`.
2. `e = |P|^-1 sum_(g in P) rho(g)` is an idempotent with image `V^P`. It kills `W`,
   since `e(rho(g) - 1) = 0`. And `1 - e = |P|^-1 sum_g (1 - rho(g))` maps `V` into
   `W`. So `W = (1 - e)V` and `V = eV (+) (1 - e)V`.
3. `rho(g) - 1` vanishes on `V^P`, so by item 2 its image is `(rho(g) - 1)W`.
4. By items 1 and 3, `dim W <= sum_x dim im(rho(h_x) - 1) = sum_x rk((rho(h_x)-1)|_W)`.

**Lemma 2.2 (dichotomy).** If `G` is not `F`-linear sofic, there is `eps_0 > 0` such
that every such `rho` and tuple satisfy `max_r rk(rho(r(h)) - 1) >= eps_0 dim W`.

*Proof.* This is the proof of Lemma 1.2, with the following changes.
- Restrict to `W`. This is invariant, and by Lemma 2.1(3) it keeps all ranks.
- Use the normalized rank `rk/dim W`. By Lemma 2.1(4) some generator has normalized
  rank at least `1/|X|`.
- The ultraproduct is the rank metric ultraproduct of `GL_(dim W_n)(F)`. A countable
  group embedding in it is `F`-linear sofic, by the ultraproduct form of
  Arzhantseva--Paunescu's definition (arXiv:1212.6780).

**Theorem item 2** follows from Lemma 2.2 exactly as in Section 1, with `t = rk(rho(g_0(a)) - 1)`.
The bound `t <= dim W` holds by Lemma 2.1(3).

## 3. Why the defining characteristic escapes

In characteristic `p` dividing `|P|`, item 2 of Lemma 2.1 fails. Take `V = U (+) V'` and
`h - 1 = [[0, N], [0, 0]]`. Then `W = im N` lies inside `U = V^P`, the moved part is not
a complement, and the rank `rk N` is invisible on every subquotient where `P` acts
semisimply. A class-two refinement is recorded as an attempt on
`binary-leavitt-unit-group-is-weakly-sofic`. It handles one unipotent layer, using
`G = gamma_3(G)`, but not unbounded depth.
