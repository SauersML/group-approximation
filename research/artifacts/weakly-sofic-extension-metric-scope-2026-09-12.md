# How far the nonsoficity argument reaches across metric approximation classes

Lane `weakly-sofic-extension`, 2026-09-12. The question: does the argument proving
`L_(F_2)(1,2)^x` nonsofic also prove it not weakly sofic (Glebsky--Rivera), or not
linear sofic (Arzhantseva--Paunescu)?

## 0. Summary

- **The argument proves nonsoficity and nothing stronger.** It is the OpenAI criterion,
  or Kun--Thom Theorem 4.1 through the rigid compression defect criterion
  (`rigid-compression-defect-normalization-dichotomy`). By monotonicity it gives
  consequences only for classes *inside* the sofic class.
- **Weakly sofic (finite groups, any bi-invariant metrics).** The conclusion itself is
  false in this class. The Kun--Thom wreath `W` is weakly sofic and carries a nontrivial
  rigid defect (`weakly-sofic-groups-can-carry-rigid-defects`). No proof step can be
  repaired: a rigid defect never obstructs weak soficity.
- **Normalized rank, over any field.** Both permutation-specific steps of the Hamming
  proof fail.
  - Step (T1), one-piece transport, fails at the configuration level over every field
    (`research/artifacts/rank-row-compression-audit-2026-09-12.md`, Section 3).
  - Step (K), rounding into expanding pieces, was shown to fail over `F_2`
    (`kazhdan-group-rank-models-admit-no-expander-decomposition`). **New here
    (Theorem A):** it fails over every field, including `Q` and `C`, for one fixed
    Kazhdan group with genuine representations. So property (T) gives no rank rounding
    in the `C`-linear row either; the ladder table had marked that entry "missing".
- **No theorem follows.** Neither "`L^x` is not linear sofic" nor "`L^x` is not weakly
  sofic" can be obtained by transcribing the nonsoficity proof. The live routes to
  `non-linear-sofic-group` are the ring-rigidity routes in characteristic two, owned by
  the Gottschalk team, and the open rank rows of the criterion.
- **Cross characteristic (Section 5).** For `F_2`-algebra groups over fields of
  characteristic other than two, root subgroups act semisimply and abelian pieces are
  canonical. Theorem A does not reach those models, so step (K) is open there.

## 1. The two steps that use permutations

These are the steps of Kun--Thom Theorem 4.1 as transcribed in Section 3 of the
rank-row audit:

- **(K)** Kun's decomposition rounds the almost-action of the Kazhdan group `Gamma`
  into expanding components with `o(n)` leakage, using the spectral gap on `l^2`.
- **(T1)** A transported component expands for `t Gamma t^-1 <= Gamma`, so it lies
  almost inside a single `Gamma`-component.

The remaining steps (no room to drift, collision, conclusion) transfer to rank.

## 2. Theorem A: no rank rounding from property (T), over every field

**Setting.**
- `Gamma = EL_3(Z[t])` with `S = { x_ij(1), x_ij(t) : i != j }`.
- `S` generates `Gamma`: `[x_ik(t^a), x_kj(t^b)] = x_ij(t^(a+b))` for distinct
  `i, k, j`, and root subgroups are additive.
- `Gamma` has property (T) (Ershov--Jaikin-Zapirain, arXiv:0809.4095, Theorem 1.1: `EL_n(R)`
  for `n >= 3` and any finitely generated unital associative ring `R`; see Section 5).
  Every finite generating set of a Kazhdan group is a Kazhdan set.

**Models.**
- Fix a field `F`, an integer `N >= 2`, and a monic `f` in `F[x]` of degree `N`.
- Put `A = F[x]/(f)`, with basis `1, x, ..., x^(N-1)`.
- The ring map `Z[t] -> A`, `t -> x`, gives a homomorphism
  `rho : Gamma -> GL_3(A) <= GL_(3N)(F)` acting on `A^3`, of dimension `n = 3N`.
- `rho(x_ij(t^k)) = 1 + E_ij (x) x^k`, the operator adding `x^k a_j` to coordinate `i`.

Boundary and distance, as in the `F_2` artifact:

```text
e_s(W) = dim(W + rho(s) W) - dim W,        b(W) = sum_(s in S) e_s(W),
d(X, Y) = dim X + dim Y - 2 dim(X n Y).
```

**Lemma 2.1 (invariant subspaces).** The `rho(Gamma)`-invariant subspaces of `A^3` are
exactly the `I^3`, for ideals `I` of `A`. The ideals of `A` are the `gA` with `g` a monic
divisor of `f`, and `dim gA = N - deg g`.

*Proof.*
1. If `V` is invariant, then `(rho(g) - 1)V <= V` for all `g`, so `V` is invariant under
   every `E_ij (x) x^k` with `i != j`.
2. Products `(E_ij (x) x^k)(E_ji (x) 1) = E_ii (x) x^k` give the diagonal units.
3. `V` is an `F`-subspace, so it is invariant under the `F`-algebra these generate, which
   is `M_3(A)` acting by matrix multiplication.
4. Let `I = { a : a e_1 in V }`. It is closed under `E_11 (x) x`, so it is an ideal.
5. `E_i1 (x) 1` and `E_1i (x) 1` identify `V n A e_i` with `I e_i`, and `v = sum_i E_ii v`.
   So `V = I^3`.
6. Conversely `GL_3(A)` preserves `I^3`, because `I` is an ideal.
7. Ideals of `F[x]/(f)` are the images of `(g)` for `g | f`.

No separability or irreducibility of `f` is used. ∎

**Lemma 2.2 (almost invariance).** Let `m <= N - 1`, `S_m = span{1, ..., x^(m-1)}`, and
`W_m = S_m^3`. Then `e_s(W_m) = 0` for `s = x_ij(1)` and `e_s(W_m) <= 1` for `s = x_ij(t)`.
So `b(W_m) <= 6`.

*Proof.* `x_ij(1)` preserves `W_m`. `x_ij(t)` maps `W_m` into `W_m + F x^m e_i`, since
`x S_m <= S_(m+1)` when `m <= N - 1`. ∎

**Lemma 2.3 (distance).** Every invariant subspace `V` has `d(W_m, V) >= 3 min(m, N - m)`.

*Proof.*
1. Write `V = (gA)^3` with `D = deg g`.
2. A polynomial `p` of degree `< m <= N-1` lies in `gA` iff `g | p`, because `g | f`. So
   `dim(S_m n gA) = max(0, m - D)`.
3. Then `d(W_m, V) = 3 (m + N - D - 2 max(0, m - D))`.
4. If `D >= m` this is `3(m + N - D) >= 3m`. If `D < m` it is `3(N - m + D) >= 3(N - m)`. ∎

**Theorem A.** For every field `F`:

1. **No rounding modulus.**
   - With `m = floor(N/2)`, `W_m` has `e_s(W_m) <= 1` for all `s`, but is at distance
     `>= 3 floor(N/2) >= (1/2 - 1/(2N)) n` from every invariant subspace.
   - So no `delta(eps) -> 0` places `eps n`-almost-invariant subspaces of genuine
     `F`-representations of the Kazhdan group `Gamma` within `delta(eps) n` of invariant
     subspaces.
2. **Irreducible models over `Q` (and every field with irreducible polynomials of every
   degree).** For `f = x^N - 2` over `Q`, `A` is a field, so `rho` is irreducible.
   `b(W_m)/dim W_m <= 2/m -> 0`, so irreducible `Q`-representations of `Gamma` are not
   uniform dimension expanders.
3. **Every normalized dimension.** For `beta` in `[0,1]`, `W_(round(beta N))` has
   `b <= 6`.

*Proof.* Lemmas 2.1-2.3. Eisenstein at `2` gives irreducibility of `x^N - 2`. ∎

**What this adds.**
- `kazhdan-group-rank-models-admit-no-expander-decomposition` proves the same shape over
  `F_2`, for `EL_3(F_2[t])` and finite field extensions.
- Remark 2.2 of `research/artifacts/kazhdan-rank-rounding-counterexample-2026-09-12.md`
  proves that irreducible *unitary* complex representations of a Kazhdan group are
  dimension expanders.
- Theorem A separates the two: the models over `Q` and `C` here are genuine and
  irreducible over `Q`, but not unitary. What property (T) needs is the Hilbert
  structure, not characteristic zero.
- Rank models over `C` are arbitrary invertible matrices, and `C`-linear soficity equals
  `Q`-linear soficity (Arzhantseva--Paunescu, Theorem 6.5, as recorded on
  `non-linear-sofic-group`). So step (K) has no form from property (T) in the `C`-linear
  row.

**Generating sets.** A generating set whose elements have word length at most `L` in `S`
changes the boundaries by at most a factor `L`, because
`e_(st)(W) <= e_s(W) + e_t(W)`.

## 3. Diffuse relative commutants over every field

Let `pi_m : A -> A` be the projection onto `S_m` along `span{x^m, ..., x^(N-1)}`, and put
`P_m = pi_m (x) 1_3`.

- `P_m` commutes with `rho(x_ij(1))`.
- For `s = x_ij(t)`, `[P_m, rho(s)] = E_ij (x) [pi_m, x]`. On the basis, `[pi_m, x]` is
  nonzero only at `x^(m-1)`, which goes to `-x^m`, and at `x^(N-1)`, where `x^N` is reduced
  modulo `f`. So `rank [P_m, rho(s)] <= 2`.

In the rank ultraproduct over `F` of the `rho = rho_N`, for `N -> infinity`, the classes
`p_beta = [P_(floor(beta N))]` are idempotents in the relative commutant of the image of
`Gamma`, with `rk p_beta = beta` and `p_beta p_gamma = p_min(beta, gamma)`. This extends
`kazhdan-rank-ultraproducts-can-have-diffuse-commutants` from `F_2` to every field. Over
`C` it contrasts with the tracial ultraproduct, where property (T) makes relative
commutants of ultraproducts of irreducible unitary representations scalar.

## 4. Class by class

| class | (K) rounding | (T1) transport | rigid defect criterion | evidence |
| --- | --- | --- | --- | --- |
| sofic (Hamming) | holds | holds | holds | Kun--Thom 4.1, `sofic-groups-kill-rigid-compression-defects` |
| `F_2`-linear sofic | fails | fails (configuration) | OPEN | `kazhdan-group-rank-models-admit-no-expander-decomposition`; audit Section 3 |
| `k`-linear sofic, any field, incl. `Q`, `C` | fails (Theorem A) | fails (configuration) | OPEN | this file; audit Section 3 |
| hyperlinear (HS) | holds | fails for exact models | OPEN | `nonmonomial-multiplicity-obstructs-hs-compressor-transport` |
| weakly sofic | none | none | fails | `weakly-sofic-groups-can-carry-rigid-defects` |

"Fails" in columns (K) and (T1) means the proof step has no transcription. It does not
decide the criterion, which stays a win--win in every rank row:

- if it holds over `k`, `W` and `L^x` are not `k`-linear sofic;
- if it fails, some `k`-linear sofic group is nonsofic.

## 5. Characteristic other than two, for the binary Leavitt units

Let `char F != 2`, `R` an `F_2`-algebra, and `sigma : EL_3(R) -> M^x` a homomorphism into a
rank ultraproduct over `F`.

- **Root subgroups are spectral.**
  - Each `sigma(x_ij(a))` is an involution, so `q_ij(a) = (1 - sigma(x_ij(a)))/2` is an
    idempotent.
  - Within a root subgroup the `q_ij(a)` commute and satisfy
    `q(a+b) = q(a) + q(b) - 2 q(a) q(b)`: symmetric difference.
  - The rank is finitely additive on orthogonal idempotents, so each root subgroup
    carries a measure on the Boolean algebra its idempotents generate.
- **Abelian pieces are canonical.**
  - For a finite subgroup `X <= x_ij(R)` with basis `a_1, ..., a_r`, the joint eigenspace
    idempotents are `E_chi = prod_l c_l`, with `c_l = q(a_l)` if `chi(a_l) = 1` and
    `c_l = 1 - q(a_l)` otherwise.
  - If `sigma(g)` conjugates `sigma(X)` to itself, then
    `sigma(g) E_chi sigma(g)^-1 = E_(chi o Ad_g^-1)` exactly in `M`.
  - So the (T1) failure mode (a graph between two multiplicity copies) cannot occur for
    pieces cut out by abelian root 2-subgroups.
- **No obstruction at the measure level.** In the parabolic `R^2 x| EL_2(R)`, the measure
  on the dual `Hom(R^2, F_2)` must be `EL_2(R)`-invariant. Haar measure always is, so
  spectral data alone forces nothing.
- **Theorem A does not reach these models.** It needs a ring map from the coefficient
  ring into an `F`-algebra, and `F_2[t]` has none into an algebra of characteristic other
  than two.
- **The sharp open sub-question for the `C`-row on `L^x`.** For `Gamma = EL_3(F_2[t])`,
  or the nine-leaf `EL_alpha(L_(F_2)(1,2))`, do rank-almost-invariant subspaces of rank
  models over `C` round to invariant ones? The companion-shift mechanism has no
  counterpart there.

This section opens no graph node. It is orientation for the `C`-linear row of the
binary units, parallel to the characteristic-two instance
`leavitt-el3-rank-models-over-finite-fields-are-trivial`.

## 6. Sources

Both PDFs were fetched from arXiv on MSI on 2026-09-12 and extracted with ghostscript
`txtwrite`.

**Ershov--Jaikin-Zapirain, arXiv:0809.4095v2, Theorem 1.1**, verbatim:

> Let R be a finitely generated (associative) ring with 1 and n ≥ 3. Let G = EL_n(R),
> that is, the subgroup of GL_n(R) generated by elementary matrices. Then G has
> Kazhdan's property (T).

With `R = Z[t]` this is the input of Section 2.

**Arzhantseva--Paunescu, arXiv:1212.6780**, verbatim:

> Theorem 1.3. Sofic groups are linear sofic, while linear sofic groups are weakly sofic.

> The following result shows that linear soficity is a priori weaker than soficity.
> Observe that the converse is open.
> Proposition 4.5. Sofic groups are linear sofic.

> Question 8.5. Are all linear sofic groups indeed sofic?

> Question 8.6. Let G be a linear sofic group and F a finite field. Does there exist an
> [...]

**The red flag in the lane brief does not apply.** The brief asked to verify that
hyperlinear groups are linear sofic. In this source "hyperlinear" occurs in the
introduction, as motivation and in the remark that amplification "[is] easy in the
sofic and hyperlinear cases. In the rank metric case, both properties are highly
non-trivial", once more at text line 1228, and in the references. No implication
between hyperlinearity and linear soficity is stated. So a non-linear-sofic group would
not thereby be non-hyperlinear, consistent with the `distinct_from` of
`linear-sofic-nonsofic-group`. The context at line 1228 is recorded after a re-read below.
