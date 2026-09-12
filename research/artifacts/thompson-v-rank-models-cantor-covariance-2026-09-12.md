# Rank models of Thompson's V and covariance with the Cantor system

Lane `w3-gate-v`, 2026-09-12. This artifact supports
`thompson-v-cantor-system-has-no-covariant-rank-model`. Later sections record the V rank gate.

## 1. Setting

- `X = {0,1}^N` is the Cantor space. `[a]` is the cylinder of a finite word `a`, and clopen sets
  are finite unions of cylinders.
- `V = G_(2,1)` acts on `X` by prefix replacement. For complete prefix codes `(a_1,...,a_q)` and
  `(b_1,...,b_q)`, the element sends `a_i x` to `b_i x`.
- `F` is any field, and `LC(X,F)` is the algebra of locally constant functions `X -> F`, spanned by
  the cylinder indicators `1_[a]`.
- `M = prod_(k->omega) M_(n_k)(F) / N_rk` is a rank ultraproduct. Here `N_rk` is the ideal of
  sequences with `rank(x_k)/n_k -> 0` along `omega`, and `rk(x) = lim_omega rank(x_k)/n_k`.

**Definition.** A *covariant rank model* of the Cantor system `V ↷ X` over `F` is a pair
`(sigma, rho)`:
- a group homomorphism `sigma : V -> M^x`;
- a unital ring homomorphism `rho : LC(X,F) -> M`;

such that

```text
sigma(g) rho(f) sigma(g)^(-1) = rho(f o g^(-1))        for all g in V, f in LC(X,F).
```

## 2. No covariant rank model

**Lemma 2.1.**
(a) If `u` is a unit of `M`, then `rk(u x u^(-1)) = rk(x)`.
(b) If `e, f` are idempotents of `M` with `ef = fe = 0`, then `rk(e + f) = rk(e) + rk(f)`.

*Proof.*
(a) `rk` is submultiplicative on both sides, `rk(axb) <= rk(x)`. Apply this to `u x u^(-1)` and
back to `x = u^(-1) (u x u^(-1)) u`.

(b) Choose representatives `e_k, f_k` with
`rank(e_k^2 - e_k) + rank(f_k^2 - f_k) + rank(e_k f_k) + rank(f_k e_k) = o(n_k)`.
- If `v = e_k x = f_k y`, then `v - e_k v = (e_k - e_k^2) x` and `e_k v = e_k f_k y`. So `v` lies in
  `im(e_k - e_k^2) + im(e_k f_k)`, and `dim(im e_k ∩ im f_k) = o(n_k)`.
- `(e_k + f_k) e_k = e_k^2 + f_k e_k`, so `im e_k ⊆ im(e_k + f_k) + im(e_k^2 - e_k) + im(f_k e_k)`.
  Likewise `im f_k ⊆ im(e_k + f_k) + im(f_k^2 - f_k) + im(e_k f_k)`.
- Hence `rank(e_k + f_k) >= rank e_k + rank f_k - o(n_k)`. The reverse inequality always holds. QED

**Lemma 2.2.** `V` acts transitively on the proper nonempty clopen subsets of `X`.

*Proof.* Let `A, B` be proper nonempty clopens.
- Write `A` and `X \ A` as disjoint unions of `p` and `q` cylinders, and `B` and `X \ B` as unions
  of `p'` and `q'` cylinders, all counts at least one.
- Splitting a cylinder `[a] = [a0] ⊔ [a1]` raises a count by one. So refine until `p = p'` and
  `q = q'`.
- The cylinders of `A` and `X \ A` together form a complete prefix code, and so do those of `B`
  and `X \ B`.
- The prefix replacement sending the cylinders of `A` to those of `B`, and the cylinders of
  `X \ A` to those of `X \ B`, is an element `g in V` with `gA = B`. QED

**Theorem 2.3.** No covariant rank model of `V ↷ X` exists, over any field `F` and any rank
ultraproduct `M`.

*Proof.* For a clopen set `A` put `e_A = rho(1_A)` and `mu(A) = rk(e_A)`.
- The `e_A` are idempotents, and `e_A e_B = rho(1_(A ∩ B)) = 0` for disjoint `A, B`. So Lemma
  2.1(b) gives `mu(A ⊔ B) = mu(A) + mu(B)`, and `mu(X) = rk(1) = 1`.
- By covariance and Lemma 2.1(a), `mu(gA) = rk(sigma(g) e_A sigma(g)^(-1)) = mu(A)`.
- By Lemma 2.2, `mu` takes one value `c` on all proper nonempty clopens.
- Then `mu([0]) = mu([00]) + mu([01])` reads `c = 2c`, so `c = 0`. But `mu([0]) + mu([1]) = 1`. QED

**Proposition 2.4 (finite stage, explicit constant).** Let `W` be a finite-dimensional `F`-space,
and `e_00, e_01, e_10, e_11` orthogonal idempotents in `End(W)` summing to `1`. Put
`e_[0] = e_00 + e_01` and `e_[1] = e_10 + e_11`. Let `A_1, ..., A_4 in GL(W)` model the prefix
replacements

```text
h_1 : (0, 10, 11) -> (00, 01, 1)       h_1[0] = [00]
h_2 : (0, 10, 11) -> (01, 00, 1)       h_2[0] = [01]
h_3 : (1, 00, 01) -> (10, 0, 11)       h_3[1] = [10]
h_4 : (1, 00, 01) -> (11, 0, 10)       h_4[1] = [11]
```

Suppose each covariance defect is small:

```text
rank(A_i e_[0] A_i^(-1) - e_(h_i[0])) <= eps dim W   (i = 1, 2)
rank(A_i e_[1] A_i^(-1) - e_(h_i[1])) <= eps dim W   (i = 3, 4)
```

Then `eps >= 1/4`.

*Proof.* Put `m(C) = rank(e_C)/dim W`. It is exactly additive on unions of depth-two cylinders,
since these idempotents are orthogonal.
- Conjugation preserves rank, so `|m(h_i C) - m(C)| <= eps`.
- Hence `m([0]) = m([00]) + m([01]) >= 2 m([0]) - 2 eps`, so `m([0]) <= 2 eps`.
- In the same way, `m([1]) <= 2 eps`.
- So `1 = m([0]) + m([1]) <= 4 eps`. QED

The map `sigma` need not be almost multiplicative for Proposition 2.4. Only the covariance
defect of four elements matters.

## 3. Consequences

**3.1. Truncations of the Cantor action.** Let `U` be a covariant linear representation of `V`
and `LC(X,F)`, for instance `LC(X,F)` itself, or any module over the crossed product
`LC(X,F) ⋊ V`. Compress it to a finite-dimensional subspace that is almost invariant under the
four elements `h_i` and the four depth-two idempotents. The induced data meet the hypotheses of
Proposition 2.4, with `eps` bounded by the boundary sizes. So every such compression has
covariance defect at least `1/4`. No rank model of `V` arises as a covariant truncation of the
Cantor action.

**3.2. Dyadic permutation models do not extend covariantly.** The dyadic constant subgroup
`D = colim Sym(2^n)` has the natural permutation modules `F^(2^(n+j))`. These are covariant for
the depth-`n` cylinder idempotents. By Theorem 2.3 no extension of such data to `V` can stay
covariant. Any extension must move the images of the cylinder idempotents away from their
covariant positions, by rank at least `1/4` at depth two.

**3.3. Relation to the tracial statement.** `thompson-v-covariant-cantor-representations-are-not-amenable`
proves the unitary analogue with the trace, `tau(P rho(1_A) P)`, which is linear. In rank the
functional has to be the rank of an honest idempotent, so covariance with the idempotents, not
only with `sigma`, is part of the hypothesis. Without it the statement fails: the constants
`span(1)` are an exactly `V`-invariant line.

**3.4. Transfer to the Leavitt units.** In `R = L_(F_2)(1,2)` the diagonal idempotents
`e_a = S[a]T[a]` span a unital copy of `LC(X,F_2)`. A prefix-replacement unit `g` satisfies
`g e_a g^(-1) = e_(g[a])`. So for any characteristic-two rank model `sigma` of `R^x`, and any
unital ring homomorphism `rho` of the diagonal subalgebra into the same `M`, covariance under
`sigma|_V` is impossible. The diagonal subalgebra alone has rank models (its dyadic "Haar" model),
so this is a filter specific to covariance. It is weaker than `leavitt-algebra-has-no-unital-rank-model`
in what it represents, and it uses only `V`.
