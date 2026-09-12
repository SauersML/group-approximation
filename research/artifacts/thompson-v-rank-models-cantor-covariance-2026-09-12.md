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

**3.1. Truncations of the Cantor action.** Let `E` carry a covariant linear representation
`(sigma, rho)` of `V` and `LC(X,F)`: for instance `LC(X,F)` itself, or any module over the
crossed product `LC(X,F) ⋊ V`. For a finite-dimensional subspace `W ⊆ E`, fix a projection `P`
onto `W` and put `T_W = P T|_W`.
- **Boundary.** Put `d_T(W) = dim(TW + W) - dim W`. Let `beta` be the largest `d_T(W)/dim W` over
  the eight operators `sigma(h_i)` and `rho(1_C)` for depth-two `C`.
- **Compression errors.** `(ST)_W - S_W T_W = P S (1-P) T|_W` has rank at most `d_T(W)`.

This subsection carries out the rounding step that the original prose left implicit
(`w3-vf-linear`, Section 7). The step keeps the idempotents as they are and rounds only the units.

**Lemma 3.1a (almost-idempotent additivity).** For `e, f` in `End(W)`,
`rank(e + f) >= rank e + rank f - 2 rank(e^2-e) - rank(f^2-f) - 2 rank(ef) - rank(fe)`.

*Proof.* The proof of Lemma 2.1(b) gives two facts:
- `dim(im e ∩ im f) <= rank(e-e^2) + rank(ef)`;
- `im e + im f ⊆ im(e+f) + im(e^2-e) + im(fe) + im(f^2-f) + im(ef)`.

Subtract the first from `rank e + rank f`. QED

**Proposition 3.1b.** With `beta` as above, `beta >= 1/32`. So no sequence of subspaces with
`beta -> 0` exists, and no rank model of `V` arises as a covariant truncation of the Cantor action.

*Proof.* Put `e_C = rho(1_C)_W` for the four depth-two cylinders.
- **Exact sum.** `sum e_C = 1_W` exactly.
- **Defects.** `e_C^2 - e_C = -P rho(1_C)(1-P) rho(1_C)|_W` and `e_C e_D = -P rho(1_C)(1-P) rho(1_D)|_W`,
  so both have rank at most `beta dim W`.
- **Rounding the units.** `S_i = sigma(h_i)_W` has corank at most `d_(h_i)(W)`, because
  `ker S_i` embeds in `(sigma(h_i)W + W)/W`. Keep `S_i` on a complement of `ker S_i`, and on `ker S_i`
  replace it with a linear bijection onto a complement of `im S_i`. This gives `A_i in GL(W)` with
  `rank(A_i - S_i) <= dim ker S_i <= beta dim W`.
- **Covariance defect.** For `C = [0]` or `[1]`, `rank(A_i e_C A_i^(-1) - e_(h_i C)) = rank(A_i e_C - e_(h_i C) A_i)`.
  - Replacing `A_i` by `S_i` costs `2 beta dim W`.
  - The exact terms cancel by covariance.
  - The compression errors cost `d_(rho(1_C))(W) + d_(h_i)(W) <= 3 beta dim W`, since `d` of `rho(1_[0])` is at most the sum over `[00], [01]`.
  - So `eps <= 5 beta`.
- **Counting.** Run the proof of Proposition 2.4 with Lemma 3.1a in place of exact additivity:
  - `m([0]) >= m([00]) + m([01]) - 6 beta >= 2 m([0]) - 2 eps - 6 beta`, so `m([0]) <= 2 eps + 6 beta`;
  - likewise `m([1]) <= 2 eps + 6 beta`;
  - `1 <= m([0]) + m([1])`, by subadditivity of rank and the exact sum.
  - So `1 <= 4 eps + 12 beta <= 32 beta`. QED

With exact idempotents, the counting step reads `1 <= 4 eps`, which is Proposition 2.4. Only the
eight boundaries matter; neither multiplicativity of `sigma` nor invariance under other elements
is used.

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
- **Calibrated: these relations do not force `rk(N_0 N_1) = 0`.** Take the regular Klein four-group
  inside `Sym(4)`: `x = (12)(34)`, `y = (13)(24)`, `xy = (14)(23)`.
  - All three are conjugate in `Sym(4)`, `x` and `y` commute, and each permutation matrix minus `1`
    has rank 2 over `F_2`.
  - `(x - 1)(y - 1) = xy - x - y + 1` is nonzero.
  - So conjugacy, commutation, `N^2 = 0` and equal displacement are all consistent with
    `N_0 N_1 != 0`, already in a finite group.
  - A proof has to use more of `V`: the infinite-order elements that change depth, whose covariant use
    Theorem 2.3 forbids.

**5.3. Positive direction.** No construction is known. What survives Section 5.1: non-monomial,
non-covariant models whose cylinder swaps displace a positive rank uniformly on each conjugacy class.
