---
rg: 2
id: aff-q-forces-distortion-in-abelian-kernels-proof
kind: route
target: aff-q-forces-distortion-in-abelian-kernels
requires: []
---

Direct elementary proof. Notation as in the target. Identify `Aff_K(Q)` with its
image under `iota`.

**Step 1 (derived subgroup).** For `a != 1` and `b in Q`,
`D_a T_b D_a^-1 T_b^-1 = T_(ab) T_(-b) = T_((a-1)b)`. Since `K` is not finitely
generated it contains some `a != 1`, and `(a-1)Q = Q`. So `Q <= Aff_K(Q)'`. The
quotient `Aff_K(Q)/Q = K` is abelian, hence `Aff_K(Q)' = Q` and
`Aff_K(Q)^ab = K`.

**Step 2 (a dilation in the kernel).** `phi` restricted to `Aff_K(Q)` factors
through `Aff_K(Q)^ab = K`; call the induced map `psi: K -> A`. Its image is a
subgroup of `phi(Gamma)`. `phi(Gamma)` is a finitely generated abelian group,
because `Gamma` is finitely generated, and subgroups of finitely generated abelian
groups are finitely generated. So `psi(K)` is finitely generated. `K` is a subgroup
of the free abelian group `Q^x_{>0}` (basis: the primes), so `K` is free abelian.
It is not finitely generated, so it has infinite rank. A free abelian group of
infinite rank has no injective map to a finitely generated abelian group. So
`ker psi` contains some `a != 1`, and `phi(D_a) = 0`. By Step 1,
`phi(T_b) = 0` for every `b in Q`. This proves 1.

**Step 3 (distortion).** Replacing `a` by `a^-1` if needed, `a = p/q` in lowest
terms with `p > q >= 1`. Put `T = T_1` and `D = D_a`. Then
`D T^(qj) D^-1 = T_(aqj) = T^(pj)` for every integer `j`. Let
`L_k = l_{H_a}(T^(p^k))` for the generating set `{T, D}`.
- `T^(p^k) = D (T^(p^(k-1)))^q D^-1`, so `L_k <= q L_(k-1) + 2`, and `L_0 = 1`.
- If `q = 1` this gives `L_k <= 2k + 1`.
- If `q >= 2`, induction gives `L_k <= q^k + 2(q^k - 1)/(q - 1) <= 3 q^k`.

`T` has infinite order, since `T^N = T_N != id` for `N != 0`, and `iota` is
injective. With `N = p^k`, `L_k / N <= 3 (q/p)^k -> 0` when `q >= 2`, and
`(2k+1)/p^k -> 0` when `q = 1`. So `N -> l_{H_a}(T^N)` is not bounded below by
`cN`, for any `c > 0`, and `<T>` is distorted in `H_a`. This proves 2.

**Corollary (i).** Apply 1–2 to the abelianization map `Gamma -> Gamma^ab`, whose
kernel is `Gamma'`.

**Corollary (ii).**
- For `g in Gamma` choose nonzero `m, n` with `g z^m g^-1 = z^n`, and put
  `delta(g) = n/m in Q^x`.
- **Well defined.** If also `g z^(m') g^-1 = z^(n')`, then
  `z^(n m') = g z^(m m') g^-1 = z^(n' m)`, so `n m' = n' m` because `z` has
  infinite order.
- **Homomorphism.** If `h z^(m') h^-1 = z^(n')`, then
  `(gh) z^(m m') (gh)^-1 = g z^(n' m) g^-1 = z^(n n')`, so
  `delta(gh) = delta(g) delta(h)`.
- **Kernel.** `ker delta` is the set of `g` with `g z^m g^-1 = z^m` for some
  `m != 0`, which equals `U_{m>=1} C_Gamma(z^m)`.
- **Conclusion.** Suppose `Aff_K(Q) <= Gamma`. By 1–2 applied to `delta`, the
  finitely generated subgroup `H_a` lies in `ker delta`. Each of its two
  generators centralizes some `z^(m_i)`, so `H_a <= C_Gamma(z^M)` with
  `M = m_1 m_2`. That contradicts the hypothesis, because `<T>` is distorted in
  `H_a` by 2.

**Corollary (iii).**
- For `a > 0`, `[[a,b],[0,a^-1]] [[1,c],[0,1]] [[a,b],[0,a^-1]]^-1 = [[1,a^2 c],[0,1]]`.
  So the group `{[[a,b],[0,a^-1]] : a > 0, b in Q}` is `Q x| K` with
  `K = {a^2 : a in Q^x_{>0}}` acting by multiplication.
- **Model.** Concretely, `[[a,b],[0,a^-1]] -> (x -> a^2 x + ab)`. This is an
  isomorphism onto `Aff_K(Q)`, because the kernel of the affine action of the
  Borel on `Q = P^1(Q) - {inf}` is `{+-I}`, and `-I` has `a < 0`.
- **Rank.** `K` is free abelian on the squares of the primes, so it is not
  finitely generated.
- **PSL_2(Q).** The subgroup contains no `-I`, so it maps injectively to
  `PSL_2(Q)`.
- **Aff(Q).** `Aff^+(Q)` is the case `K = Q^x_{>0}`, and
  `x -> ax + b` is the matrix `[[a,b],[0,1]]` in `GL_2(Q)`.
