# UN review, part 1 (lane un-verify-3, 2026-09-13)

Scope: the established claims landed by `un-tarski` (991380d00d), `un-converse` (417904a22b, 68dfcddab5) and
`un-architect` (2e5fbbeafb, 886b11bd39), plus the wiring of the UN root and flagship. Method for each claim:
independent re-derivation, a verbatim quote check of every load-bearing citation against its source, model tests
on `L_k(1,2)` and `LC(X,F_q) ⋊ Z`, an untruncated title-level subsumption scan of `research/*.md`, and a check
of the formulas displayed in the node.

**Summary.** 11 PASS, 1 GAP, 0 FAIL. Wiring PASS: nothing fires early.

| § | Node | Verdict |
|---|---|---|
| 1 | `algebraic-tarski-for-steinberg-algebras` | PASS |
| 2 | `invariant-measure-gives-rank-function-in-char-zero` | PASS |
| 3 | `unperforated-paradox-makes-steinberg-purely-infinite` | **GAP** (exclusivity in char p; rank-two requires) |
| 4 | `full-defect-in-m-by-m-kills-mf-quotients-of-el-2m` | PASS (duplicate content, see §4) |
| 5 | `mf-elementary-groups-force-stably-finite-simple-rings` | PASS |
| 6 | `exactly-matricial-rings-have-lef-general-linear-groups` | PASS |
| 7 | `weyl-algebra-is-exactly-matricial` | PASS |
| 8 | `exactly-matricial-rings-are-lef-rings` | PASS (FOLKLORE credit added) |
| 9 | `leavitt-path-algebras-are-steinberg-algebras` (import) | PASS |
| 10 | `rank-modelled-simple-rings-give-linear-sofic-projective-el` | PASS |
| 11 | `crossed-products-are-transformation-steinberg-algebras` | PASS (PRIOR: Beuter–Gonçalves; citation route added) |
| 12 | root `kazhdan-elementary-approximation-type-mirrors-ring-type`, flagship | wiring PASS |

## Quote checks (arXiv TeX sources fetched on MSI, `/projects/standard/hsiehph/sauer354/ex/un-verify-3/`)

- **Rainone–Sims arXiv:1707.04516v2**, `\begin{theorem}\label{Tarski}` (TeX l.1103–1110). The statement matches
  `rainone-sims-tarski-alternative-for-monoids-citation` verbatim.
- **ABBL arXiv:2001.00376**, `\begin{lem}\label{lem:RS-forgroupoids}` (TeX l.459–464). It matches
  `abbl-type-semigroup-states-extend-to-invariant-measures-citation` verbatim.
- **Clark–Sims arXiv:1311.3701**, `\begin{example}\label{ex:lpa}` (TeX l.285–299). It matches
  `leavitt-path-algebras-are-steinberg-algebras-citation` verbatim.
- **Beuter–Gonçalves arXiv:1706.00127**, `\begin{theorem}\label{theorisomortransfgrou}` (TeX l.442–444) and the
  standing assumption at l.394. Quoted in the new route `crossed-products-are-transformation-steinberg-algebras-citation`.
- **Larki arXiv:1901.07094** Thm 3.4, used in §3: the import's statement was read. Its definitions of "strongly
  effective" and "properly purely infinite" were not re-read; see §3.

## §1 algebraic-tarski-for-steinberg-algebras: PASS

- **Lemma 2.1.** For a nonzero Sylvester matrix rank function on simple `R`, the rank-zero set in each `M_n(R)` is a
  two-sided ideal: `rk(xy) ≤ min`, and subadditivity from `x+y = [1 1] diag(x,y) [1 1]^T`. Since `rk(I_n) = n`, it
  is proper, hence zero.
- **Lemma 2.2.** From `AB = I_n` we get `rk B = n`, and `B = (BA)B` gives `rk(BA) = n`. For the idempotent `e = BA`,
  `diag(e, 1−e)` is equivalent to `I_n ⊕ 0` through invertible matrices, so `rk(e) + rk(1−e) = n`. This needs no
  Malcolmson–Schofield input. Faithfulness gives `BA = 1`.
- **The map `ι : S(𝒢) → V(R)`.** On the ABBL presentation it is well defined: `[∅] ↦ 0`; disjoint unions go to
  orthogonal sums; `1_(s(V)) = 1_(V^(-1)) 1_V` and `1_(r(V)) = 1_V 1_(V^(-1))` are MvN-equivalent idempotents. So it
  is a monoid homomorphism and order-preserving.
- **Theorem 2.3.** Suppose `(n+1)θ ≤ nθ`. Then there are `x ∈ M_(n+1,n)`, `y ∈ M_(n,n+1)` with `xy = I_(n+1)` and
  `yx = p`. Padding gives `x̃ỹ = I_(n+1)` and `ỹx̃ = diag(p,0) ≠ I_(n+1)`.
- **Theorem 2.4.** (⟸) An invariant measure defines a normalized state on generators, and the relations hold by
  invariance. (⟹) Tarski gives a state; minimality gives `θ ≤ m[U]` through finitely many bisections with sources
  in `U`, so the state is finite and faithful on `K(X)`; ABBL extends it with `μ(X) = ν(θ) = 1`.
- **Display check:** items 1–3 of the node match the artifact.
- **Subsumption:** consistent with `rainone-sims-type-semigroup-dichotomy` (C*), `simple-ring-stably-finite-iff-unit-not-paradoxical`
  (ring level) and `char-zero-steinberg-stably-finite-iff-invariant-measure` (char 0). No refuting node found.

## §2 invariant-measure-gives-rank-function-in-char-zero: PASS

- **Trace.** `BC ∩ X = r(B ∩ C^(-1))` and `CB ∩ X = s(B ∩ C^(-1))`, and `B ∩ C^(-1)` is a compact open bisection.
- **Positivity.** For `f = Σ c_i 1_(B_i)` over disjoint bisections, `τ(f*f) = Σ |c_i|² μ(s(B_i))`. Minimality
  gives full support, so `τ(f*f) > 0`.
- **Boundedness.** `τ(x* 1_(s(B)) x) ≤ τ(x*x)`, since `τ(((1−p)x)*((1−p)x)) ≥ 0`.
- **Faithfulness on `M`.** The GNS vector of a trace is separating, because right multiplication is bounded by
  trace symmetry.
- **Rank function.** `rk(A) = (τ⊗Tr)(LP(A))`. `LP(AB) ≤ LP(A)` and `LP(AB) ~ RP(AB) ≤ RP(B) ~ LP(B)` in a finite
  algebra. The triangular inequality for the MvN dimension is standard and recalled, not imported.
- **Overlap.** `char-zero-steinberg-stably-finite-iff-invariant-measure` (un-paradox, via `C*_r`) gives the
  stable-finiteness consequence. This node is strictly stronger, since it gives a rank function. Its `distinct_from`
  should name that node (sent to un-tarski).

## §3 unperforated-paradox-makes-steinberg-purely-infinite: GAP

- **Correct.**
  - Lemmas 6.1–6.3: `(n+1)(2θ) ≤ nθ` gives `2θ ≤ θ`; then `(m+1)·2[V] ≤ m[V]` gives `2[V] ≤ [V]`.
  - Branch 2 whenever `θ` is paradoxical: `ι` makes every `1_V` properly infinite. Minimal plus effective means the
    only closed invariant sets are `∅` and `X`, hence strongly effective, and Larki Thm 3.4 (2)⇒(1) applies.
    `V = X` gives `ts = 1 ≠ st`, and Cor l.1016 applies.
  - Exhaustiveness.
- **Gap 1 (exclusivity).** The node says "exactly one of" and "exclusive and exhaustive by step 3". Step 3 makes an
  invariant measure exclusive with paradox of `θ` in `S(𝒢)`. To exclude branch 2's *ring* properties when a
  measure exists, one needs *invariant measure ⟹ A_k(𝒢) stably finite*.
  - For `k ⊆ ℂ` this follows from §2.
  - In characteristic `p` it is open and at least Kaplansky-hard: `measure-side-stable-finiteness-contains-char-p-kaplansky`,
    and the reflection claim `type-semigroup-reflects-paradox-of-steinberg-algebra`.
  - Repair: "at least one holds; branch 2 holds whenever `X` has no invariant measure; the branches are exclusive
    for `k ⊆ ℂ`".
- **Gap 2 (requires).** The statement covers `n ≥ 2`, but the route requires only the rank-four node
  `simple-dedekind-infinite-ring-elementary-full-mf-radical`. It should require `full-defect-ring-non-mf-at-rank-two`
  (established), which gives rank two for a full defect.
- Owner notified. If the owner has finished, this lane applies both repairs on the live blobs.

## §4 full-defect-in-m-by-m-kills-mf-quotients-of-el-2m: PASS

- Lemma 1 (block identification) re-derived: same-block generators
  `e_((i,a),(i,b))(r) = [e_((i,a),(k,1))(r), e_((k,1),(i,b))(1)]` on three distinct coordinates.
- Lemma 2: `w_pq` conjugates `X_kl` onto `X_(τk,τl)`.
- The required node `full-defect-ring-non-mf-at-rank-two` is established on main (route `full-defect-ring-rank-two-proof`).
- **Subsumption.** At `m = n` the content coincides with `stably-infinite-ring-elementary-groups-have-no-mf-quotient`
  (un-paradox) and `paradoxical-ring-el-n-full-mf-radical-from-twice-level` (un-middle). All three `distinct_from`
  blocks record the overlap. Choosing one canonical node is with un-architect.

## §5 mf-elementary-groups-force-stably-finite-simple-rings: PASS

- `e = 1 − st` is idempotent (`e² = 1 − 2st + s(ts)t`), nonzero, and full by simplicity of `M_m(R)`.
- Item 2 is the contrapositive, and item 3 follows for infinitely many `N`.
- If `EL_N(R)` is MF, the identity is nontrivial, since `e_12(1) ≠ 1`.

## §6 exactly-matricial-rings-have-lef-general-linear-groups: PASS

- Units of an algebraic ultraproduct are coordinatewise units.
- A finite window lives in one coordinate. Malcev (recalled) gives a finite quotient separating it.
- LEF ⟹ MF: regular permutation unitaries, exactly multiplicative on growing windows, `‖V_n(g) − 1‖ ≥ √2`.
- No conflicting node. `cohn-elementary-group-is-not-lef` concerns a ring that is not directly finite.

## §7 weyl-algebra-is-exactly-matricial: PASS

- `[D_p, T_p] t^j = t^j` for `j < p−1`, and for `t^(p−1)`: `0 − (p−1)t^(p−1) = t^(p−1)`.
- The ultraproduct of the `F_p` over the primes is a field of characteristic 0 containing the image of `Q`.
- `A_1(Q)` is simple, so the map is injective.
- This duplicates `weyl-algebra-over-q-is-lef-ring-not-matricial-over-q` in substance, as `distinct_from` records.

## §8 exactly-matricial-rings-are-lef-rings: PASS, FOLKLORE

- Łoś handles finitely many atomic facts in one coordinate.
- The entry ring `A ⊆ F_k` is a finitely generated Jacobson domain. Some maximal ideal avoids each `c_(ab)`, and
  residue fields of finitely generated rings are finite.
- Credit FOLKLORE (a Malcev-type argument), per un-novelty.

## §9 leavitt-path-algebras-are-steinberg-algebras: PASS

- The quote matches. The rose specialization (CK1) `t_i s_j = δ_ij`, (CK2) `Σ s_i t_i = 1` at the single vertex gives
  `L_k(1,2) = L_k(R_2)`.

## §10 rank-modelled-simple-rings-give-linear-sofic-projective-el: PASS

- `A⊗A^(−T) − B⊗B^(−T) = (A−B)⊗A^(−T) + B⊗(A^(−T) − B^(−T))`, and `A^(-1) − B^(-1) = A^(-1)(B−A)B^(-1)`. This gives
  `rk(Ad A − Ad B) ≤ 2N rk(A−B)`.
- `dim C(A) = Σ_λ Σ_j (p'_j)² ≤ Σ_λ k_λ d_λ ≤ N max k_λ`, where `p'` is the conjugate partition.
- For `λ ∉ k` (k finite), the Galois conjugates have equal kernels, so `k_λ ≤ N/2`.
- Separation: `min_λ rk(A−λ)/N ≥ min(δ, 1/2) > 0`.
- Invertible representatives exist in rank ultraproducts.
- Model test: `L_k(1,2)` has no unital rank model (`leavitt-algebra-has-no-unital-rank-model`), so the statement is
  vacuous there.

## §11 crossed-products-are-transformation-steinberg-algebras: PASS, PRIOR

- Re-derived the sheetwise bijection and `(F*G)(γδ,x) = f(γδx) g(δx) = Ψ(f·(g∘γ^(-1)) u_(γδ))(γδ,x)`.
- **PRIOR.** Beuter–Gonçalves Theorem `theorisomortransfgrou`, the partial-action generalization, which the source
  attributes to folklore. Added citation route `crossed-products-are-transformation-steinberg-algebras-citation`,
  kept the lane's proof as a second route, and added a credit paragraph to the node.

## §12 Root and flagship wiring: PASS

- Route `kazhdan-approximation-ladder-from-three-converses` requires `lef-el-groups-force-exactly-matricial-simple-ring`,
  `linear-sofic-el-groups-force-rank-model` and `stably-finite-simple-rings-have-mf-elementary-groups`. All three exist
  and have no incoming route, so the route cannot fire, and it is the only route into the root.
- The flagship `free-group-cantor-elementary-group-lef-iff-invariant-measure` has no route and stays OPEN.
- Display check: the root's established halves name existing established nodes.

## Subsumption scan

- An untruncated title scan (`git grep "^title:"` over `research/*.md` at tip 762b8af60f) was run for these themes:
  - invariant measure, rank function, matricial, Weyl, Steinberg;
  - stably or directly finite together with elementary groups;
  - paradox, properly infinite, purely infinite.
- Relevant hits read: `cohn-elementary-group-is-not-lef`, `matricial-aperiodic-sft-rings-are-not-quantum-rigid`,
  `non-lef-kazhdan-el-group-from-fp-rank-modelled-simple-algebra`, `leavitt-algebra-has-no-unital-rank-model`,
  `char-zero-steinberg-stably-finite-iff-invariant-measure`, and the paradox-side stabilization nodes.
- None refutes or already subsumes a reviewed claim, apart from the duplicates recorded in §§2, 4, 7 and 11.
