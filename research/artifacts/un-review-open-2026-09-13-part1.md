# UN review (un-verify-open), part 1: un-open-5, un-open-4, Labbé complexity

Lane `un-verify-open`, 2026-09-13. Independent re-derivation, quote checks against source PDFs, model tests, and an
untruncated subsumption scan of `research/*.md` at main's tip. Scope changes from main: un-open-1 and un-open-8 moved
to `un-verify` (§4 records what was handed over).

Verdict legend: PASS (proof re-derived, statement faithful), PRIOR / FOLKLORE / SUBSUMED (credit or overlap, the
mathematics still passes), GAP (proof incomplete as landed), FAIL (false).

## 1. un-open-5 (bec8c05389, 7e6f1c8002)

**Subsumption scan.** Terms `continuum many|continuum of|turing degree|word.problem degree|every degree|sturmian`
over every `research/*.md`, no truncation (≈190 hits). Three older nodes bear directly:
- `subshift-elementary-group-word-problem-degree` (lane ex-kazhdan-simple-hyperlinear, 2026-09-12, reviewed PASS in
  `ex-review-groups-2026-09-12-part11.md` §11.4). Statement: `WP(G_X) ≡_T L(X)`, "the same holds for the word
  problem of `G_X / Z(G_X)`", `L(X_α) ≡_T α`, every Turing degree realized, uncountably many isomorphism classes.
- `binary-subshifts-embed-in-three-marked-kazhdan-groups` (root, 2026-09-13): over `F_2`, `X ↦ (G_X; c,t,w)` is a
  topological embedding and `X ⊂ Y` iff there is a marked epimorphism, so the marking determines `X`.
- `fixed-mf-quotient-kazhdan-extensions-realize-all-word-degrees`: non-simple extensions (already a `distinct_from`).

None of the un-open-5 nodes named the first two. Their `distinct_from` blocks now do.

### 1.1 `marked-subshift-elementary-group-determines-language`: PASS (overlap over F_2)
- Lemma 1.1: `(1+aE_ij)(1+bE_jk)(1−aE_ij)(1−bE_jk) = 1 + abE_ik` for distinct `i,j,k`, entries multiplied in order.
- Lemma 2.1: the recursion `ω_ik(s m') = [ω_ij(s), ω_jk(m')]` evaluates to `e_ik(ev(s)ev(m'))`.
- Lemma 2.2: `u f u^(-1) = f∘T^(-1)` (the Pestov artifact convention), so `u^(-t) χ_a u^t = χ_a∘T^t = χ_[x_t=a]`.
- Theorem 1: `Z(G_X) ⊆ F_q^× I_3` (`subshift-elementary-group-is-simple-modulo-centre`), and `e_12(f)` is scalar iff
  `f = 0`; `LC(X) → R_X` is injective; the cylinder at 0 is nonempty iff `w ∈ L(X)`, by shift invariance.
- Model test: for a periodic subshift the centre is larger, and the note in §6 of the lane artifact says so.
- Display check: the node formula `W_w(σ_X) = 1` iff `w ∉ L(X)` matches the artifact.

### 1.2 `continuum-many-simple-kazhdan-lef-groups`: PASS, SUBSUMED in substance
- The map `X ↦ φ(σ_X) ∈ H^I` is injective on `{X : S_X ≅ H}`: equal tuples give equal languages. `H` is countable,
  so each isomorphism class holds countably many `X`, and a continuum of subshifts gives a continuum of classes.
- Already on main through the Turing-degree node, whose artifact records `WP(S_X) ≡_T L(X)`. The counting proof
  through markings is the new part.

### 1.3 `subshift-elementary-group-word-problem-equals-language`: PASS (truth-table refinement)
- Full-shift normal form `Σ f_j u^j` with window tables. The product `(fu^i)(gu^j) = f·(g∘T^(−i)) u^(i+j)` is local.
- `π : R_full → R_X` is a ring homomorphism, since restriction is `T`-equivariant. `π(Σ f_j u^j) = 0` iff every table
  vanishes on `L_(2m+1)(X)`.
- `g = 1` in `S_X` iff `π(M_g)` is a scalar `cI_3`: off-diagonal vanishing plus a finite disjunction over `c ∈ F_q`.
  All queries are computed from `g` in advance, so the reduction is truth-table.
- The Turing form is on main; the truth-table refinement is new (bounded).

### 1.4 `sturmian-language-is-turing-equivalent-to-angle`: PASS, FOLKLORE
- `α ≤_T L(X_α)`: every legal length-`n` word has `k ∈ {⌊nα⌋, ⌊nα⌋+1}` ones, so `|k/n − α| < 1/n`.
- `L(X_α) ≤_T α`: for `y` in an open gap of `{−tα mod 1 : 0 ≤ t ≤ n}`, `y+tα ≢ 0` and `y+tα ≢ 1−α` for `t < n`
  (else `y = p_t` or `y = p_(t+1)`). Nonempty cylinders are unions of half-open arcs with endpoints among the
  `p_t`, so they contain a gap.
- Classical for Sturmian words, and already stated in the Turing-degree node.

### 1.5 `every-turing-degree-is-a-simple-kazhdan-lef-word-problem`: PASS, SUBSUMED in substance
- For `d ≠ 0` and `B ∈ d`, `α = 0.1 b_0 1 b_1 1 …` is not eventually periodic (else `B` computable), so `α` is
  irrational and `α ≡_T B`.
- Then `WP(S_(X_α)) ≡_tt L(X_α) ≡_T α`. Word-problem degree is invariant under change of finite generating set.
- Already on main through the Turing-degree node.

### 1.6 `continuum-many-infinite-minimal-binary-subshifts`: PASS, classical
- Cylinders are finite intersections of half-open arcs, so nonempty ones have positive length. Orbit segments become
  `ℓ`-dense, so legal words recur with bounded gaps, and that closed property passes to `X_α`: minimality.
- Counting identity: `{z} ∈ [1−α,1)` iff `⌊z+α⌋ = ⌊z⌋+1`, telescoping to `⌊y+nα⌋ − ⌊y⌋ ∈ {⌊nα⌋, ⌊nα⌋+1}`.

## 2. un-open-4 (dc5fe60cca, 4d7f0d1db7, a7955b459f)

**Quote check.** Arzhantseva–Păunescu, *Linear sofic groups and algebras*, arXiv:1212.6780v1, read from the PDF
(`un/lanes/un-verify-open/lit/ap-1212.6780.txt`).
- Definition 4.2: "A countably generated algebra A over a field F is linear sofic if there exist an injective morphism
  Θ : A → Πk→ω Mnk (F )/Kerρω . Moreover, if A is a unital algebra we require that this morphism is unital."
- Corollary 11.15: "A simple unital algebra with almost finite dimensional representations is linear sofic."
- After Proposition 11.16: "We can construct a unital morphism Θ for any amenable algebra. Therefore, amenable
  algebras have almost finite dimensional representations. [...] In particular, any amenable or LEF algebra that is
  also simple is linear sofic."

**Subsumption scan.** Terms `linear sofic|amenable algebra|algebraic amenab|rank model|rank-metric ultraproduct|
Arzhantseva–Păunescu` over `research/*.md` (≈390 claim nodes). Bearing directly:
`free-minimal-crossed-products-are-simple-with-rank-models` (every free minimal `Z^d` Cantor crossed product over a
finite field is simple with an injective unital Følner rank model), and `minimal-subshift-algebra-is-simple-lef-ring`
(exact models for `d = 1`).

### 2.1 `simple-amenable-affine-algebras-have-unital-rank-models`: PASS, PRIOR
- (a) `1 ∈ B_n` gives `Q_n ⊆ B_n Q_n`, so `dim(rQ_n + Q_n) ≤ (1+1/n)d_n` once `r ∈ B_n`.
- (c) `φ_n(rs) − φ_n(r)φ_n(s) = P_n λ(r)(1−P_n)λ(s)|_(Q_n)`. For `W ⊇ Q_n`, `W = Q_n ⊕ (W ∩ T_n)`, so the rank is at
  most `dim(sQ_n+Q_n) − d_n ≤ d_n/n`.
- (d) `dim(rQ_n) − d_n/n ≤ rank φ_n(r) ≤ dim(rQ_n)`.
- (e) `N = {rk = 0}` is a two-sided ideal. (f) `rk(1) = 1` and simplicity give `N = 0`, hence injectivity. Rank-metric
  ultraproducts are stably finite (AP Proposition 2.8).
- The statement is Arzhantseva–Păunescu's (quotes above). The node's credit paragraph claimed the single-sequence
  upgrade as new content; that paragraph is replaced with the AP credit.

### 2.2 `subexponential-growth-simple-algebras-have-rank-models`: PASS
- Elek, arXiv:math/0203261 Proposition 4.1 (subexponential growth ⇒ amenable), then 2.1.

### 2.3 `zero-entropy-subshift-pestov-ring-has-rank-model-by-growth`: PASS
- Words of length `≤ m` in `{χ_[a], u^(±1)}` normalize to `f u^j`, `|j| ≤ m`, `f` in the span of cylinders on
  `[−m,m]`: `dim R_m ≤ (2m+1)p(2m+1)`.
- GK dimension exactly 2 for Sturmian `X`: `≤ 2` from the bound; no value in `(1,2)` (Bergman's gap theorem); GK
  dimension 1 affine algebras are PI (Small–Stafford–Warfield), and simple affine PI algebras are finite dimensional
  (Kaplansky).
- As a rank model it is subsumed by the exact models of `minimal-subshift-algebra-is-simple-lef-ring`; the growth
  proof is the content. `distinct_from` added.

### 2.4 `subexponential-complexity-zd-subshift-rings-have-rank-models`: GAP → repaired; SUBSUMED in the free case
- The ball bound `dim R_m ≤ |B_m(Z^d)|·p(2m+1)` holds.
- **Scope gap.** The node asserted the rank model for every infinite minimal subshift. 2.1 needs `R` simple for
  injectivity. A minimal `Z^d`-subshift need not be free: a minimal infinite `Z`-subshift, extended constantly in the
  `e_2` direction, is minimal and not effective, and its crossed product is not simple. **Repair:** freeness was
  added to the statement. For a minimal action of the abelian `Z^d`, topologically free equals free, because each
  `Fix(g)` is closed and invariant.
- In the free case the conclusion already follows from `free-minimal-crossed-products-are-simple-with-rank-models`,
  with no complexity hypothesis. `distinct_from` added. Labbé's shift is free, so the downstream use survives.

**Model tests for §2.** `L_k(1,2)` is simple and not directly finite, so it has no rank model and, by 2.1, is not
amenable, consistent with its exponential growth. The Pestov ring passes 2.3.

## 3. Labbé complexity (un-labbe-ring, ebac0fa361)

**Quote check.** S. Labbé, *A self-similar aperiodic set of 19 Wang tiles*, arXiv:1802.03265, read from the PDF
(`lit/labbe-1802.03265.txt`). PDF numbering against the lane's TeX labels:
- Theorem 10 = `thm:exist-homeo`: "ω(S) ⊆ (T \ M) ∪ ((T \ M) ⊙i M) which is recognizable in the Wang shift ΩS and
  surjective up to a shift, i.e., ω(ΩS)∪σ ei ω(ΩS) = ΩT."
- Propositions 15 and 18 = `prop:wecandesubstituteU/V`: `V` of cardinality 21 with `α`, direction `e_2`; `W` of
  cardinality 19 with `β`, direction `e_1`.
- Lemma 19 = `lem:homeoUtoW`: `γ` is a bijection.
- Lemma 20 = `lem:omega-is-primitive`, proof: "whose 7-th power M 7 is positive. Therefore M is a primitive matrix and
  the morphism is primitive."
- Proposition 21 = `prop:pre-main`: "expansive, recognizable in ΩU and satisfies (12) ΩU = ω(ΩU) ∪ σe1 ω(ΩU) ∪ σe2
  ω(ΩU) ∪ σe1+e2 ω(ΩU)". Proof: "sends at least one letter to a 2-dimensional word of shape (2, 2)".
- Corollary 22: the shift-closure of `ω(Ω_U)` is `Ω_U`. Lemma 3: `Y = closure ω(X)` iff `L_Y = closure^Fact ω(L_X)`.
- Lemma 23: `L(X_ω) ∩ U^(2,2) = L(Ω_U) ∩ U^(2,2) = S`. The count `|S| = 50` is the lane's count on the TeX source;
  the PDF display was not recounted here.
- Proposition 24: "ΩU is minimal. More precisely, ΩU = Xω where ω = αβγ."
- Lemma 5, proof of (iv)⇒(i), is the cover step, under the hypotheses "expansive and primitive" and
  `L = closure^Fact ω(L)`.

### 3.1 `labbe-substitution-is-primitive-and-recognizable`: PASS (import faithful)

### 3.2 `labbe-wang-shift-has-polynomial-pattern-complexity`: PASS
- **Letter images.** `β(γ(u))` has shape `(1,1)` or `(2,1)`, and `α` of a letter is `(1,1)` or `(1,2)`. Concatenation in
  direction `e_1` needs equal heights, so `shape(ω(u)) ≤ (2,2)`.
- **Iterates.** Letter images in one column share a width, so `shape(ω(x)) ≤ (2w,2h)`. `M^7 > 0` puts every letter in
  `ω^7(a)`, and some letter has image `(2,2)`, so `shape(ω^8(a)) ≥ (2,2)`, then `shape(ω^(8j)(a)) ≥ (2^j,2^j)`.
- **Count.** With `m = 8⌈log_2 n⌉`, every legal `n × n` word is a subword of `ω^m(u)` for a legal `2×2` word `u`. So
  `p(n) ≤ 50·4^(m+1) ≤ 50·4^9·n^16`.
- **Wiring.** The consequence is recorded in Attempts only, with no route; that is correct. The rank model of Labbé's
  ring is independently on main through `free-minimal-crossed-products-are-simple-with-rank-models`. The middle rung
  `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` is already established through the Abels–Prüfer route,
  so neither path is needed for its status.

## 4. Handed over (no verdict here)
- **un-open-1.** `relative-torsion-defect-mf-radical-step`: the printed identities (Lemma l.866 eq. intertwine,
  `c = diag(1,1,1,1+et)`, the `D(1±f_ij)` commutators, `vcv^(-1)`, `vzv^(-1)`, `[y,d]`, `z^m`) are matrix
  computations. In `EL_n(R)/EL_n(R,J)` they hold only modulo `(EL_n(R) ∩ GL_n(R,J))/EL_n(R,J)`. Sent to the owner and
  to un-hh-extension; the owner is repairing, and un-verify holds the formal verdict.
- **un-open-8, for un-verify.** Older nodes to scan for subsumption of Lemma C: `zariski-envelope-compression-rigidity`,
  `locally-residually-finite-targets-kill-compression-defects`, `finitary-linear-extension-kazhdan-defect-kills-kernel`.
  The re-derivation of tex Lemma l.866 (`u_i` blocks `[[s,e],[0,t]]`, `u` matrix, intertwine, `c`, `uc = e_12(e)u`)
  was done here and checks out.

## 5. Ledger
| node | verdict |
|---|---|
| marked-subshift-elementary-group-determines-language | PASS; overlap over F_2 credited |
| continuum-many-simple-kazhdan-lef-groups | PASS; SUBSUMED in substance (Turing-degree node) |
| subshift-elementary-group-word-problem-equals-language | PASS; tt refinement of a reviewed node |
| sturmian-language-is-turing-equivalent-to-angle | PASS; FOLKLORE |
| every-turing-degree-is-a-simple-kazhdan-lef-word-problem | PASS; SUBSUMED in substance |
| continuum-many-infinite-minimal-binary-subshifts | PASS; classical |
| simple-amenable-affine-algebras-have-unital-rank-models | PASS; PRIOR (Arzhantseva–Păunescu Cor 11.15) |
| subexponential-growth-simple-algebras-have-rank-models | PASS |
| zero-entropy-subshift-pestov-ring-has-rank-model-by-growth | PASS |
| subexponential-complexity-zd-subshift-rings-have-rank-models | GAP (scope) repaired; SUBSUMED when free |
| labbe-substitution-is-primitive-and-recognizable | PASS |
| labbe-wang-shift-has-polynomial-pattern-complexity | PASS |
