# One mechanism behind the non-MF paper and the Pestov 9.1 answer — synthesis, part 1

Lane `un-synthesis`, 2026-09-13, refresh 1 (main tip d1ca5488fc). This is the single readable account of the UN
swarm's theory. It proves nothing new: every statement points to its node and carries a status taken from the
verifier artifacts, never upgraded here.

**Status tags.**
- **[REVIEWED PASS · sha]:** an independent verifier re-derived it. The sha is the review landing.
- **[unreviewed]:** established on main by a complete route, not yet re-derived by a verifier.
- **[import]:** a literature theorem quoted verbatim in a `-citation` route.
- **[printed]:** a theorem of `non_mf_groups_exist.tex` (line given).
- **[OPEN]:** an open claim.

Part 2 covers the flagship free-group theorem, the families, traces and corona invariants, the examples table, the
open middle, and a status ledger.

## 0. The thesis in one paragraph

Take a minimal ample groupoid `𝒢` over the Cantor set, its Steinberg algebra `R = A_k(𝒢)`, and the elementary
groups `EL_N(R)`. For `N ≥ 3`, `EL_N(R)` modulo its centre is always simple, and it is Kazhdan when `k` is finite and
`R` is finitely generated. What decides how such a Kazhdan group can be approximated by matrices is a Tarski
alternative on `𝒢`: paradox versus invariant measure.
- **Paradox branch:** one-sided compressions in `V(R)` kill every MF quotient from a computable rank on. This is
  the non-MF paper's mechanism.
- **Measure branch, with finite towers:** the ring embeds in matrix ultraproducts and the group is LEF. This is
  the Pestov 9.1 mechanism.

The Cuntz groupoid (`L_k(1,2)`) and a minimal ℤ-subshift (`LC(X,F_q)⋊ℤ`) are the two branches' simplest members.

## 1. The two calibrating results

- **[printed l.918, l.1016]** Suppose `R` is countable and unital, `ts = 1`, and `R(1−st)R = R`. Then for `n ≥ 2`
  every homomorphism from `EL_n(R)` to an MF group is trivial. In particular this holds when `R` is simple and
  not directly finite, e.g. `L_k(1,m)`. **[printed l.1038]** `C*_r(EL_n(R))` is stably finite and not MF.
  **[printed l.1218]** For `R` purely infinite simple, `Rad_MF(GL_n R) = [GL_n R, GL_n R]`, with quotient `K_1(R)`.
- **Pestov 9.1** [REVIEWED PASS twice: `ex-review-groups-2026-09-12-part1.md`, `ex-pestov91-second-review-2026-09-13.md`;
  Lean + Comparator]: for an infinite minimal subshift `X`, `R = LC(X,F_q)⋊ℤ` embeds unitally in `∏_ω M_N(F_q)`
  (return-word towers), and `S = EL_3(R)/Z` is infinite, simple, Kazhdan and LEF.

## 2. The dictionary

- **Steinberg algebras.** `A_k(𝒢)` is the span of indicators `χ_B` of compact open bisections, with `χ_B χ_C = χ_(BC)`.
  It is unital when `𝒢⁽⁰⁾` is compact.
  - `L_k(1,2) = A_k(𝒢_2)` for the Cuntz groupoid `𝒢_2`.
  - `LC(X,k)⋊Γ = A_k(X⋊Γ)` for a transformation groupoid.
  - Steinberg / BCFS [import, `steinberg-algebra-simple-iff-minimal-effective`; REVIEWED PASS · 171f0f7525]: for
    Hausdorff ample `𝒢`, `A_k(𝒢)` is simple ⟺ `𝒢` is minimal and effective.
- **Two monoids.**
  - `S(𝒢)`: the type semigroup (Rainone–Sims), with `θ = [𝒢⁽⁰⁾]`. It does not involve `k`.
  - `V(R)`: finitely generated projectives with the algebraic preorder, with `[1] = [R_R]`.
- **The bridge** [unreviewed; landed independently by un-paradox (`no-invariant-measure-steinberg-elementary-no-mf-quotient`,
  Lemma 2) and un-tarski (artifact §1.1)]: there is an order-preserving monoid map `ι : S(𝒢) → V(A_k(𝒢))`,
  `[U] ↦ [1_U R]`, for every field `k`. Consequence: paradox is a property of `𝒢`, and its ring-level shadow holds
  over every field simultaneously.
- **Does `ι` reflect paradox?** [OPEN, `type-semigroup-reflects-paradox-of-steinberg-algebra`] A yes would make stable
  finiteness of `A_k(𝒢)` field-independent. That contains Kaplansky's stable finiteness conjecture for this class,
  so it is at least Kaplansky-hard (§7).

## 3. Uniform simplicity

**Theorem S4** [REVIEWED PASS · 171f0f7525; un-simplicity 6c58d38ebb; `steinberg-elementary-groups-are-simple-mod-centre`].
Let `k` be a field and `𝒢` a Hausdorff ample groupoid with compact **infinite** unit space, minimal and effective.
Put `R = A_k(𝒢)` and `n ≥ 3`.
- Every normal subgroup of `EL_n(R)` is central or everything, and `Z(EL_n R) ⊆ k^× I_n`.
- `EL_n(R)/Z` is an infinite simple group.
- If `k` is finite and `R` is finitely generated as a ring, `EL_n(R)/Z` is finitely generated and Kazhdan (EJZ).

**The proof, in three pieces** (all REVIEWED PASS · 171f0f7525):
- **S1:** `A_k(𝒢)` has *local annihilation* when `𝒢⁽⁰⁾` is infinite (`steinberg-algebras-have-local-annihilation`).
  The displayed condition is the Lean predicate `LocalAnnihilation` verbatim.
- **S2:** the centre is `k·1` (`minimal-effective-steinberg-algebras-have-scalar-centre`; credit Clark–Edie-Michell
  1403.4684 and Steinberg 1408.6014 Prop 3.7).
- **S3:** a simple ring with local annihilation has `EL_n/Z` simple for `n ≥ 3`. This is the Lean theorem
  `GroupApproximation.Pestov91.isSimpleGroup_elementaryGroup_quotient_center`, written by the Pestov 9.1
  formalization swarm, with exactly the hypotheses `3 ≤ card ι`, `IsSimpleRing R`, `LocalAnnihilation R`.

**Reading.**
- Both calibrating groups are instances of S4.
- Simplicity is uniform across the dichotomy, so it does not separate the two sides. What separates them lives in
  `S(𝒢)`.
- **Model tests** (from the review):
  - a field fails local annihilation;
  - `LC(X,k)` for Cantor `X` has local annihilation but is not simple, so its `EL_n` has congruence normal subgroups.

## 4. The ring-level Tarski theorem

**Theorem T** [REVIEWED PASS · 638d4941b5; un-middle 4db95cef51; `simple-ring-stably-finite-iff-unit-not-paradoxical`].
For a countable simple unital ring `R`, the following are equivalent:
- `R` is stably finite;
- `[R]` is not paradoxical in `V(R)`, i.e. `(n+1)[R] ≰ n[R]` for all `n`;
- `V(R)` has a state normalized at `[R]`.

It rests on the Kwaśniewski–Meyer–Prasad Tarski theorem for preordered monoids [import, REVIEWED PASS verbatim ·
638d4941b5, `kmp-tarski-theorem-preordered-monoids`, arXiv:2502.17190v3 Cor 2.16].

**The paradoxical level.** `p(R)` is the least `n` with `M_n(R)` not directly finite, and `p(R) = ∞` iff `R` is
stably finite.

**Caution** [un-tarski artifact §3.0]: a state on `V(R)` is strictly weaker than a Sylvester matrix rank function.
The two agree on von Neumann regular rings, but Steinberg algebras are not regular. So Theorem T is one step below
the measure-side chain of §6.

## 5. The paradox branch: exact rank thresholds

**Theorem P** [unreviewed]. Let `R` be countable and unital. If `2n[1] ≤ n[1]` in `V(R)` for some `n ≥ 1`, every
homomorphism from `EL_N(R)` to an MF group is trivial for every `N ≥ 2n`.
- **Three independent landings of the same theorem** (canonical node pending un-architect): un-paradox
  `stably-infinite-ring-elementary-groups-have-no-mf-quotient` (895c311052), un-middle
  `paradoxical-ring-el-n-full-mf-radical-from-twice-level` (4db95cef51), un-converse
  `full-defect-in-m-by-m-kills-mf-quotients-of-el-2m` (417904a22b).
- **Why the hypotheses agree.** un-middle assumes `(n+1)[1] ≤ n[1]`, which gives `2n[1] ≤ n[1]` (add `[1]` and
  induct). un-converse assumes `ts = 1` with full defect in `M_n(R)`, which is `2[1] ≤ [1]` in `V(M_n R) = V(R)`
  scaled by `n`, i.e. `2n[1] ≤ n[1]` (`full-idempotent-ring-has-properly-infinite-unit`). All three give the same
  threshold.
- **Proof in one line.** The printed l.918 for `M_n(R)` at rank 2, the block identity `EL_2(M_n R) = EL_(2n)(R)`,
  and conjugacy of root subgroups inside `EL_N`.

**Corollary P1** (simple rings) [unreviewed; un-paradox, un-converse Cor B].
- If `R` is simple and not stably finite, `EL_N(R)` has no nontrivial MF quotient for `N ≥ 2p(R)`.
- Contrapositive: if `EL_N(R)` has a nontrivial MF quotient, then `M_m(R)` is directly finite for every `m ≤ N/2`.
- If `EL_N(R)` has an MF quotient for infinitely many `N`, then `R` is stably finite.

**Theorem 5, non-IBN refinement** [unreviewed; un-middle 486d277d93, `non-ibn-ring-el-n-full-mf-radical-above-module-rank`].
If `R^m ≅ R^(m+d)`, every homomorphism from `EL_N(R)` to an MF group is trivial for `N ≥ max(m+1, 3)`. Example:
`EL_N(L_k(2,3))`, `N ≥ 3`, over a ring that is directly finite if Cohn's fir theorem applies (recalled, not
load-bearing).

**Theorem G, groupoid form** [unreviewed; un-paradox 4253950d2e `no-invariant-measure-steinberg-elementary-no-mf-quotient`;
same statement un-middle `measure-free-ample-groupoid-el-n-full-mf-radical`, canonical pending].
Let `𝒢` be ample Hausdorff with compact unit space.
- If `𝒢⁽⁰⁾` carries no invariant probability measure, some `n` has `2n[1] ≤ n[1]` in `V(A_k 𝒢)`, so there is no MF
  quotient from rank `2n`.
- If `2θ ≤ θ` in `S(𝒢)`, then `N ≥ 2`.
- The chain behind it: Tarski for `S(𝒢)` (Rainone–Sims Thm 6.2 [import]), ABBL Lemma 2.3 [import], and the
  bridge `ι`.

**Theorem 6.4, sharp threshold under almost unperforation** [unreviewed; un-tarski 991380d00d,
`unperforated-paradox-makes-steinberg-purely-infinite`]. Let `𝒢` be minimal, effective, Hausdorff, ample, second
countable, with compact unit space and `S(𝒢)` almost unperforated. Then exactly one of:
- `𝒢⁽⁰⁾` carries an invariant probability measure;
- `A_k(𝒢)` is properly purely infinite and simple (Larki Thm 3.4 [import]), and `EL_n(A_k 𝒢)` has no nontrivial MF
  quotient for **every** `n ≥ 2` (printed l.1016).

## 6. The measure branch: what a measure gives, and what it does not

**Corollary 2.5, the measure-side chain** [unreviewed; un-tarski 991380d00d, `algebraic-tarski-for-steinberg-algebras`].
For minimal `𝒢` with compact unit space and any countable field:

  `A_k(𝒢)` has a nonzero Sylvester matrix rank function ⟹ stably finite ⟹ `θ` completely non-paradoxical
  ⟺ `𝒢⁽⁰⁾` carries an invariant probability measure.

**Proposition B, matricial models force a measure** [unreviewed; un-measure 3f486a4805,
`matricial-steinberg-algebras-have-invariant-measures`]. A unital homomorphism `A_k(𝒢) → ∏_ω M_N(k)` gives the rank
function `rk = lim_ω rank/N` and the invariant measure `μ(U) = rk(1_U)`. The Cuntz groupoid fails, since `μ = 2μ`.

**Theorem C, exact matricial ⇒ LEF over arbitrary fields** [unreviewed; un-converse 417904a22b,
`exactly-matricial-rings-have-lef-general-linear-groups`]. If `R` embeds unitally in `∏_ω M_(d_k)(F_k)` with arbitrary
fields `F_k`, then `GL_N(R)` is LEF for every `N`. So every `EL_N(R)` is LEF, hence sofic, hyperlinear and MF. The
proof uses windows plus Malcev's theorem.

**Theorem A, residually finite actions give matricial rings** [unreviewed; un-measure 3f486a4805,
`residually-finite-actions-give-matricial-crossed-products`]. For a minimal, topologically free, residually finite
action `Γ ↷ X` on the Cantor set, `LC(X,k)⋊Γ` embeds unitally in `∏_ω M_N(k)`, with genuine finite `Γ`-sets as
models. The Pestov ring is the case `Γ = ℤ`.

## 7. Characteristic: where the Kazhdan groups live

- **Characteristic 0 is exact** [unreviewed].
  - un-paradox Theorem D0 (f00b23bede, `char-zero-steinberg-stably-finite-iff-invariant-measure`, via Rainone–Sims
    Thm 6.5 and Sims Cor 3.3.4 [imports]): for minimal Hausdorff `𝒢` and char `k = 0`, stably finite ⟺ invariant
    measure.
  - un-tarski Theorem 3.1 (`invariant-measure-gives-rank-function-in-char-zero`): an invariant measure gives a faithful
    Sylvester matrix rank function, via the finite von Neumann algebra of `τ(f) = ∫ f|_X dμ`.
  - So all four conditions of §6 are equivalent. The two landings overlap; canonical pending.
- **Property (T) forces characteristic p** [un-tarski artifact §4.2]. EJZ needs `R` finitely generated as a ring. A
  field finitely generated as a ring is finite (Artin–Tate), so the Kazhdan branch exists only over finite fields.
- **Characteristic p is where the arrow is open** [unreviewed firewall, un-paradox
  `measure-side-stable-finiteness-contains-char-p-kaplansky`]. "Invariant measure ⇒ stably finite" for free minimal
  Cantor actions over `k` would prove Kaplansky's stable finiteness conjecture over `k`. The open claim
  `invariant-measure-gives-rank-function-any-field` [OPEN] records the arrow.
- **Consequence.** The Kazhdan simple groups of this program live exactly where "measure ⇒ matricial" is not a
  theorem, so the measure branch must be witnessed by hand. That is what Pestov's return-word towers do, and what
  Theorem A does for residually finite actions. Ara–Claramunt [import,
  `cantor-z-crossed-product-embeds-in-continuous-factor`] give the rank-function form for every Cantor ℤ-system over
  every field.
