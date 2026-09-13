# Rung (Σ⇒) of the unification ladder: exact reduction, famous-level firewall, and where the fp-cover method stops

Lane `un-sigma-converse`, 2026-09-13. Everything is **unreviewed**. Target: the open claim
`linear-sofic-el-groups-force-rank-model`. For a finite field `k` and a simple unital `k`-algebra `R` with
centre `k`, if every `S_N = EL_N(R)/(EL_N(R) ∩ k^x 1_N)` is `k`-linear sofic, does `R` have a unital rank model
over `k`?

**Verdict.** Not decided. Three results:
1. **Exact lift (§1).** A projective linear sofic model of `S_N` lifts to an exact general-linear rank model of
   `EL_N(R)` with kernel exactly the scalars. So (Σ⇒) reduces to an algebraic ring-rigidity statement, and no
   metric stability input enters.
2. **Famous-level firewall (§3).** (Σ⇒) implies the root `non-linear-sofic-group`, through `L_(F_2)(1,2)`.
3. **Where the fp-cover method stops (§2).** One rung up, the method un-lef-converse used for (L⇒) supplies
   nothing new. What is missing is a frame, not approximate relators.

## 1. The exact lift (`linear-sofic-projective-el-lifts-to-gl-rank-models`)

Setting: `iota : S_N -> P = prod_omega PGL_(n_i)(k)/d`, injective, with
`d((A_i),(B_i)) = lim_omega min_(λ ∈ k^x) rk(A_i − λB_i)/n_i`. Put `Ad(A) = A ⊗ (A^(-1))^T` and
`U = prod_omega GL_(n_i^2)(k)/d_rank`.

- **Lipschitz.** `rk(Ad A − Ad B) <= 2n min_λ rk(A − λB)`, since `Ad(λB) = Ad(B)` and
  `A^(-1) − λ^(-1)B^(-1) = −A^(-1)(A − λB)(λB)^(-1)`. So `Ad : P -> U` is a well-defined homomorphism.
- **Separation.** `rk(Ad A − 1)/n^2 >= min_(μ ∈ k̄) rk(A − μ)/n`, from `dim C(A) <= n max_μ dim ker(A − μ)`.
  For `μ ∉ k`, and `k` perfect (finite fields are), `μ` has a distinct conjugate with a kernel of equal
  dimension, so `dim ker(A − μ) <= n/2`. So `Ad` is injective on `P`.
- **Result.** `sigma = Ad ∘ iota ∘ q : EL_N(R) -> U` is a homomorphism with `ker sigma = Z_N`.

The estimates are those of `rank-modelled-simple-rings-give-linear-sofic-projective-el-proof`, steps 2–3,
which passed review (un-verify-3). They are used here in the group-to-group direction.

**Reduction.** (Σ⇒) follows from:

> (RR_k) If `R` is simple with centre `k` and, for all `N >= 2`, some homomorphism `EL_N(R) -> U_N` into a
> general-linear rank ultraproduct over `k` has kernel exactly `Z_N`, then `R` has a unital rank model over `k`.

`el3-rank-models-factor-through-ring-rank-models` (open) is the `N = 3` characteristic-`p` form. Its conclusion
allows a rank model over any field of characteristic `p`, not necessarily over `k`. So it gives (Σ⇒) only with
the field of the model relaxed.

## 2. The fp-cover method one rung up: what it gives and where it stops

**What (L⇒) used.** A finite model of a ball of `St_N(A)`, over a finitely presented free cover `A` of a window,
extends to a genuine homomorphism `rho : St_N(A) -> Q` into a finite group. The root kernels
`K_ij = {a : rho(x_ij(a)) = 1}` coincide and form a finite-index ideal `K`, and the window embeds exactly in `A/K`.

**At rank level the metric step is vacuous.** Linear soficity already gives an exact homomorphism into the
ultraproduct `U` (§1). Every relator of `St_N(A)` holds exactly in `U`, so finite presentation adds no information.

**The level-ideal step has no rank analogue.**
- The analogue of `K` is `{a : sigma(x_ij(a)) = 1}`, which is `0` by faithfulness.
- The root images `X_ij = sigma(x_ij(R))` are abelian subgroups of `U^x`, of exponent `p` when `char k = p`.
  Writing `n_ij(a) = sigma(x_ij(a)) − 1`: `n_ij(a)^p = 0` exactly (established in the el3 artifact), and
  `n_ij(a + b) = n_ij(a) + n_ij(b) + n_ij(a) n_ij(b)`.
- The commutator pairing `X_12 × X_23 -> X_13` is a group commutator, not a product in `M`. So the root images
  carry no ring structure isomorphic to a subring of `M = prod_omega M_(n_i^2)(k)/d_rank`.
- The ring structure appears only after a **frame**: idempotents `e_1, e_2, e_3` with `n_ij(a) ∈ e_i M e_j`.
  Then `u_ij = n_ij(1)` are matrix units, and `phi(a) = n_12(a) u_21` is a unital ring homomorphism into
  `p_1 M p_1` (`block-unipotent-rank-models-of-leavitt-el3-are-trivial`; the extraction there uses only the
  Steinberg relations and works for any ring).
- In the finite-group case of (L⇒) the level ideal plays the role of the frame. In the ultraproduct no such
  ideal exists, so the frame must be built from `sigma` itself. That is the open core of (Σ⇒).

**Torus attempt, `q >= 3`. It stops, and at `q = 2` it is empty.**
- The diagonal torus `T` of `SL_N(k) = EL_N(k) ⊆ EL_N(R)` has order prime to `p`.
- So `k[T]` is split semisimple, and `sigma(T)` gives weight idempotents `f_χ` (`χ ∈ T^`), `sum_χ f_χ = 1`,
  exactly in `M`.
- The averages `N^c_ij(a) = sum_(μ ∈ k^x) c(μ)^(-1) sigma(x_ij(μ a))`, for characters `c` of `k^x`, satisfy
  `sigma(h) N^c_ij(a) sigma(h)^(-1) = c(α_ij(h)) N^c_ij(a)`, so they shift weights by `c ∘ α_ij`.
- Where it stops: `sigma(x_ij(a)) − 1` is a sum over all `c` of these shifts, not a single corner. The
  commutator of two such sums is not the average of the product.
- So the weight grading gives candidate frame idempotents but no corner support. Over `F_2`, where `k^x` is
  trivial, there is no torus at all, and that is the Leavitt case.

## 3. Famous-level firewall (`non-linear-sofic-via-sigma-converse-at-leavitt`)

`L_(F_2)(1,2)` is simple with centre `F_2` and has no unital rank model over any field. If (Σ⇒) holds, some
`S_N = EL_N(L_(F_2)(1,2))` (the scalars are trivial over `F_2`) is not `F_2`-linear sofic. That closes the root
`non-linear-sofic-group`, which is open. No group is known that fails linear soficity over any field; the root
node records the Arzhantseva–Păunescu background.

- **Proving (Σ⇒):** at least as hard as exhibiting a non-linear-sofic group.
- **Refuting (Σ⇒):** needs a simple rankless `k`-algebra whose projective elementary groups are all `k`-linear
  sofic. At the Leavitt algebra that is `binary-leavitt-unit-group-is-f2-linear-sofic`, also open.
- Either way the rung is famous-level. It is the same wall as `el3-rank-models-factor-through-ring-rank-models`
  and the rank row `f2-linear-sofic-groups-kill-rigid-compression-defects`.

## 4. Model tests

- **Pestov ring `LC(X,F_q) ⋊ Z`.** It has a rank model (towers, or growth per un-open-4), `S_N` is linear sofic,
  and §1 gives GL models. Consistent with (Σ⇐).
- **`L_(F_2)(1,2)`.** It has no rank model. (Σ⇒) predicts a non-linear-sofic `EL_N`, which is open. That is the
  firewall.
- **`F_q[Γ]`, `Γ` amenable and not LEF (calibration F3).** Not simple, because of the augmentation ideal, so it
  lies outside (Σ⇒). It has a faithful rank model (Følner) and linear sofic `EL_n`, but no LEF. The (Σ) and (L)
  rungs genuinely differ here, and nothing refutes (Σ⇒).
- **Lift lemma over `F_2`.** `k^x = {1}`, `P = U` up to `Ad`. The kernel statement reduces to faithfulness.

## 5. Bounds

- Unreviewed: all of §1–§3. The matrix estimates repeat reviewed computations.
- Recalled, not imported: the commutant dimension formula via Jordan partitions; split semisimplicity of `k[T]`
  for `|T|` prime to `p` with `k` containing the needed roots of unity (here `k^x` itself).
- No literature search. Arzhantseva–Păunescu Question 8.6 is quoted from the existing root node.
