# EX review, wave 2, part 8: the coordinator's review requests, subsumption scans, and the weak-soficity dichotomy (2026-09-13)

Lane `ex-verify2-groups`. Index: `ex-review2-groups-2026-09-13.md`. Read at tips `66b3f0952` to current.

## 1. Requested items and verdicts

| request | verdict | where |
|---|---|---|
| `strict-one-sided-compression-forces-infinite-bi-index-proof` (ex-complexity-sofic-amplifier, 6a80e95f35) | PASS: (SCI1)--(SCI5), re-derived | part 5 §2 |
| node body versus route | Scoped (f5dbceab4f). The review line now says the route certifies (SCI1)--(SCI5) only, and (SCI6) rests on the review's source check of arXiv:2608.02025v2 p. 3. No other body sentence goes beyond (SCI5). | this part |
| ex2-weak-sofic-affine-targets, part 2 (near-scalar): Lemma 2.1, Lemma 3.1, Lemma 4.2(ii), Lemma 4.3 | PASS, re-derived | part 7 §1 |
| ex2-free-wreath-amenable-sofic: the counterexample pair and the induction theorem | PASS, re-derived | part 5 §3 |

The near-scalar details, for the record:
- **Lemma 2.1.** `ψ(gg') = ψ(g)ψ(g') + C_g B_(g')`, and `C_g` leaves the free rank-`d_0` summand.
- **Lemma 3.1.**
  - The conjugators `diag(det d_i^(-1), 1, ...) ⊕ d_i` lie in `SL_n(R)`, reduce to 1, and are block diagonal.
  - The Teichmueller scalars cancel through the exponent sum `e_u`.
- **Lemma 4.2(ii).** The `(U_b, U_b)` block is `1 + γ(z-1)β'`, from `γβ' + δδ' = 1`. The rows into `U_a` and the
  block out of `U_a` each have rank at most `2d_0`.
- **Lemma 4.3.**
  - The common kernel is a free summand of corank `<= f`, and the image lies in a summand of rank `<= 2f`, both by
    Smith normal form.
  - `Ã = C_0 ⊕ (Ã ∩ U_0)` by the modular law. Then `B̃ = M' ∩ U_0` gives `R^n = Ã ⊕ B̃`.

## 2. Subsumption scans, without truncation

**Free-wreath claims.** 402 nodes mention co-amenability, amenable or sofic actions, or generalized or free wreath
products. I read every ESTABLISHED or REFUTED hit.
- **Nothing implies or refutes the counterexample pair or the induction theorem.**
  - `groups-containing-kun-thom-pair-have-nonsofic-actions` and the refuted
    `sofic-groups-in-paunescu-sofic-action-class` concern p.m.p. actions (Păunescu), not GKP set actions.
  - `paunescu-class-closed-under-amenable-extensions` is the p.m.p. analogue for normal subgroups with amenable quotient.
    It is a different statement.
  - `gkp-free-wreath-permanence` assumes a sofic action, so it is consistent with the counterexample.
- **One duplication, not an error.** Item (C1) of `separating-sofic-quotient-sets-make-an-action-sofic` (separable
  stabilizers give sofic coset actions) is item 1 of the older `sofic-coset-actions-pass-to-marked-colimits`. The
  newer node carries no `distinct_from` for it.
- **No remaining use of the false principle "amenable actions are sofic".**
  - `mikhailova-coset-action-two-sided-proof` quotes it only inside its correction note, and justifies the step by GKP
    Theorem 2.17, since the actor there is amenable.
  - `finite-phase-pauli-dilation-is-twisted-group-factor-compiler` line 73 is about p.m.p. actions of the amenable
    group `Z`, which is true.
  - The Lean module `Sofic/CoAmenableActionSofic` proves soficity only for strongly co-amenable subgroups
    (`G/core(K)` amenable), which matches (C2).

**Congruence and affine width claims.** 294 nodes mention chain rings, congruence targets, Singer elements, Hensel,
or affine targets. I read every ESTABLISHED hit.
- Nothing older implies or refutes them.
- A **later** node, `fp-simple-weak-soficity-is-finite-field-linear-soficity` (ex2-weak-sofic-bounded-factors, 10:33,
  after the part 7 census), contains item 2 (i) => (ii) of `simple-group-width-over-congruence-targets`, and Corollary 1
  of `relator-width-over-transitive-abelian-extensions`, as special cases. §3 reviews it.
- Item 1 of the congruence theorem (bounded rank, no hypothesis on `G`) is not subsumed.

**Displayed formulas.** I recomputed every bound displayed on the claim and route nodes against the artifacts, and they
agree:
- `max(K + 2, 2JLK + J')`;
- `K <= Cons_(2sm)(S)`;
- `SL_n(R) = Z_T Cons_(5k_0)(h)`;
- `A <= Cons_4`, hence `K(G) + 4`;
- the co-amenable equivalence;
- (C1)--(C3).

## 3. `fp-simple-weak-soficity-is-finite-field-linear-soficity`: PASS on both routes

**Route `fp-simple-weak-soficity-via-nst-psl-approximation`.**
- **(i) => (iii).**
  - A simple weakly sofic `G` is **PSL**-approximable by NST Theorem 4.
  - With `S` containing `X` and the relator prefixes, `a_x = φ(x)` has `l(r(a)) <= Cε` and `l(a_x) >= δ_x` for a
    nontrivial generator. These are weak models in `PSL_n(q)`, so the PASSed PSL dichotomy gives linear soficity.
- **(iii) => (i).** The rank metric is bi-invariant on finite groups.
- **(ii) => (iii).** `l(a_x) <= K(G) C ε` contradicts `l(a_x) >= α`.
- **(iii) => (ii).**
  - Glebsky's capped conjugation length is bi-invariant, and pigeonholing fixes the generator `x`.
  - The ultraproduct homomorphism has a kernel missing `x`, so by simplicity it is injective.
  - The uniform α comes from rescaling the length on each finite window, as NST remark after their Definition 1.

**Route `fp-simple-weak-soficity-is-finite-field-linear-soficity-proof`.**
- **Step 1.**
  - `B/L` embeds in `Π Out(S_T)`, of derived length `<= 3` (strong Schreier), so `B^(3) <= L`.
  - The projection of `L` to `S_T` contains `B_T^(3) ⊇ S_T`.
  - A subdirect product of nonabelian simple groups is a direct product of some of them, by induction.
- **Step 2.**
  - `c_x = w_x(b) in L`.
  - The templates (PASSed in backlog part 7 §33) cover direct products with any number of factors.
  - `r(c) = r(w)(b)` costs `k_1` conjugates.
- **Step 3.** Pull back through `relator-width-bounded-by-almost-simple-quotients`, below.

**`relator-width-bounded-by-almost-simple-quotients`**: PASS at the checked steps.
- *(a).*
  - Theorem 1.2 with the symmetric set of relator conjugates puts `Q'` in `Cons_(4νF_1(2ν))`, because
    `[x, y] = (x^(-1)y^(-1)x)·y`.
  - Equal exponent sums give `a_x ≡ Π r(a)^(n_(x,r))` mod `Q'`.
- *(b).* Theorem 1.1 with `K = Q_0` and `Y = {s_i^(±1)} ∪ R(a)^(±1)`.
- *(c).* The kernels over the locally finite variety `𝒱_M` are finitely many, and `<<R>>U = F` because `G` has no
  finite quotients.
- *Note.* `F_1` should be taken monotone in `r`, since `|Y|` may be less than `2ν`. This is harmless.

**Sources, checked in the PDFs.**
- **NST, arXiv:1703.06092v2.** Definition 1 (p. 4) and Example 1 (p. 5) as quoted. Theorem 4, verbatim: "Any
  non-trivial finitely generated Fin-approximable group has a non-trivial PSL-approximable quotient. In particular,
  every simple Fin-approximable group is PSL-approximable."
- **Nikolov--Segal, arXiv:1102.3037v6.** Theorems 1.1 and 1.2 as quoted on `nikolov-segal-generation-by-conjugates`.

**Scope, as the node says.**
- (i) => (iii) is a reduction: no finitely presented simple group is known to be non-linear-sofic over finite fields.
- Nothing is decided about `non-weakly-sofic-group-exists` or `fg-simple-weakly-sofic-groups-are-sofic`. Both stay OPEN.

## 4. Verdicts

| claim | verdict |
|---|---|
| `strict-one-sided-compression-forces-infinite-bi-index` (route and body) | PASS; body scoped to the route |
| near-scalar Lemmas 2.1, 3.1, 4.2(ii), 4.3 | PASS |
| free-wreath counterexample pair and induction theorem | PASS |
| `fp-simple-weak-soficity-is-finite-field-linear-soficity` | PASS on both routes |
| `relator-width-bounded-by-almost-simple-quotients` | PASS at the checked steps |
| `nst-simple-weakly-sofic-groups-are-psl-approximable`, `nikolov-segal-generation-by-conjugates` | PASS: citations match the PDFs |
