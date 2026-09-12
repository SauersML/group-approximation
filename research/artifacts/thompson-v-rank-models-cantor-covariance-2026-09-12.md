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

**3.5. What the theorem uses: halving, not only covariance.** The proof needs elements that map a
clopen set onto a proper clopen subset of itself, as `h_1` maps `[0]` onto `[00]`. Measure-preserving
Cantor systems admit covariant rank models. For instance a `Z`-subshift with its Haar or uniform measure
has dyadic covariant models, since the cylinder idempotent ranks can follow the invariant measure.
`w3-gate-bridge-b` noted the case `EL_3(C(X,F_2) ⋊ Z)`. So the obstruction comes from the
paradoxical, non-measure-preserving part of `V`, the same part behind
`thompson-v-cantor-orbits-have-no-folner-sets`.

## 4. The V rank gate

**4.1. Nodes.**
- `thompson-v-is-f2-linear-sofic` (open): `V` embeds in a characteristic-two matrix rank ultraproduct.
- `thompson-v-has-no-nontrivial-f2-rank-model` (open): every homomorphism from `V` into such an
  ultraproduct is trivial.

Each refutes the other. `V` is simple, so a nontrivial homomorphism is injective.

**4.2. Soficity feeds the positive side.** If `V` is sofic, then `sofic-implies-linear-sofic-over-every-field`
gives an injective homomorphism into a characteristic-two rank ultraproduct. The route is
`thompson-v-f2-linear-sofic-from-soficity`.

**4.3. The negative side feeds `non-linear-sofic-group`.** If every characteristic-two rank model of `V`
is trivial, `V` is not `F_2`-linear sofic. The route is `non-linear-sofic-via-thompson-v-rank-triviality`.

**4.4. Restriction from the Leavitt units.** `V <= R^x = L_(F_2)(1,2)^x` by
`leavitt-cylinder-swaps-generate-thompson-in-el`, and `R^x` is simple by `binary-leavitt-unit-group-is-simple`.
- Any nontrivial homomorphism `phi` from `R^x` into any group has trivial kernel, so it restricts
  injectively to `V`.
- Hence: `V` rank-trivial in characteristic two implies `R^x` rank-trivial in characteristic two, which
  implies `R^x` is not `F_2`-linear sofic.
- The converse direction is not available. `R^x` rank-trivial says nothing about homomorphisms of `V` that
  do not extend.
- The graph's instance claim `leavitt-el3-rank-models-over-finite-fields-are-trivial` quantifies over every
  characteristic and arity. This gives only its binary characteristic-two case, so no route into it is landed.

**4.5. Scope in the characteristic.** `thompson-v-linear-witness-supports-kill-g-in-rank-models` needs a rank
target of the same characteristic as the group algebra (`w3-v-linear`). So a nontrivial `F_2` rank model of `V`
refutes only the binary target `thompson-v-order-three-averaging-idempotent-is-full`. The ternary swap target
`thompson-v-ternary-swap-idempotent-is-full` needs a characteristic-three model of `V`.

## 5. Where each direction stops

**5.1. Constraints on any rank model of `V`.**
- **Not covariant.** It carries no covariant copy of the cylinder algebra (Theorem 2.3).
- **Not monomial.** Monomial models are Hamming models (`monomial-rank-models-are-hamming-models`), so a
  monomial model would make `V` sofic. That is open, and it is the harder question.
- **Not built from the algebra.** It is not multiplicative on the Leavitt algebra
  (`leavitt-algebra-has-no-unital-rank-model`, applied to the prefix-replacement units).
- **No finite shortcut.** It does not factor through any finite group or finite-dimensional
  representation, since `V` is infinite and simple.

**5.2. Involution calculus in characteristic two (heuristic, not a claim).**
- For a cylinder swap `pi = pi_(a<->b)`, `N = pi - 1` has `N^2 = 0`.
- Swaps whose union is not all of `X` are conjugate in `V`.
- `pi = pi_0 pi_1` with `pi_i = pi_(ai<->bi)` commuting and conjugate to `pi`. So
  `N = N_0 + N_1 + N_0 N_1`, all three have one rank `r`, and `r <= 2r + rk(N_0 N_1)`.
- Trivial-plus-free displacement data satisfy all of this, so displacement alone decides nothing, as for
  the Leavitt roots (`dyadic-root-displacement-data-admit-trivial-plus-free-models`).
- **Untested.** Whether the conjugating element `h` with `h pi_0 h^(-1) = pi`, together with the
  commutation, forces `rk(N_0 N_1) = 0`. If it did, `rk(N) = rk(N_0 + N_1)`. Even then additivity would
  need independence of the images of `N_0` and `N_1`, which is exactly what covariance would supply and
  Theorem 2.3 forbids.

**5.3. Positive direction.** No construction is known. What survives Section 5.1: non-monomial,
non-covariant models whose cylinder swaps displace a positive rank uniformly on each conjugacy class.
