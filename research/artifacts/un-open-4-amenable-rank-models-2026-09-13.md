# Algebraic amenability gives unital rank models, in every characteristic

Lane `un-open-4`, 2026-09-13. Status: **established, unreviewed**, except the literature imports, which are
quoted verbatim from the arXiv TeX sources.

## 0. Why this route exists

The UN root `kazhdan-elementary-approximation-type-mirrors-ring-type` needs, on its measure side, a **unital
rank model**: a unital embedding of the coefficient ring into a rank-metric ultraproduct of matrix algebras.
`un-tarski` produced one from an invariant measure **only in characteristic zero**
(`invariant-measure-gives-rank-function-in-char-zero`), leaving
`invariant-measure-gives-rank-function-any-field` open and noting it contains Kaplansky's stable finiteness
conjecture in characteristic `p`.

That is exactly the wrong half to be missing, because the Kazhdan groups live **only** in characteristic `p`:
`EL_N(R)` is Kazhdan by EJZ only when `R` is finitely generated *as a ring*, and a field finitely generated as
a ring is finite (Artin–Tate). So every Kazhdan example sits over a finite field, where the measure route is
blocked.

This note supplies a rank model by a different mechanism — **Elek's algebraic amenability** — which never
mentions a measure, a groupoid or a type semigroup, and works over an arbitrary field.

## 1. Imported definitions and results (Elek), quoted verbatim

From **G. Elek, "The amenability of affine algebras", arXiv:math/0203261** (TeX source, MSI):

> **Definition.** The affine algebra `R` is (left) amenable if there exists a sequence of finite dimensional
> linear subspaces `W_1 ⊆ W_2 ⊆ …, ∪_{n=1}^∞ W_n = R`, such that for any `r ∈ R`
> `lim_{n→∞} dim_K(W_n r + W_n)/dim_K(W_n) = 1`.

> **Proposition 4.1.** Any affine algebra of subexponential growth is amenable.

> **Theorem 2.** The following conditions are equivalent for affine algebras `R` **without zero-divisors**.
> (1) `R` is amenable. (2) `R` is not paradoxical. (3) There exists a finitely additive invariant
> dimension-measure on `R` with respect to some basis.

From **G. Elek, "On algebras that almost have finite dimensional representations", arXiv:math/0311376**:

> **Definition.** The `k`-algebra `A` is amenable if for any finite dimensional linear subspace `1 ∈ B ⊂ A`
> and `ε > 0` there exists a non-trivial finite dimensional linear subspace `Q ⊂ A` such that
> `(dim_k BQ − dim_k Q)/dim_k Q < ε`.

> **Proposition.** If `A` is amenable, then it almost has finite dimensional representations.

> **Theorem 2.** If `A` is a simple algebra almost having finite dimensional representations then it is
> stably finite.

> **Proposition 4.1.** `RR(A)` is an ideal.

Elek's proof of "amenable ⇒ almost-fd" is the compression `ψ_n(a)v = P_n(av)` on a nearly invariant
subspace `Q_n`. **Everything in §2 below is that construction.** What is added here is only the packaging
along a *single* sequence, which turns Elek's local `ε`-almost representations (whose lower rank bound
`C_L` depends on the subspace `L`) into one Sylvester rank function and one embedding.

**Convention.** Two sides appear in Elek's two papers. Below, "amenable" means the left version of
math/0311376: for every finite-dimensional `1 ∈ B ⊆ R` and `ε > 0` there is a nonzero finite-dimensional
`Q ⊆ R` with `dim(BQ) ≤ (1+ε) dim Q`. Nothing here needs the two versions to agree.

## 2. Theorem 1

**Theorem 1.** Let `k` be any field and `R` a **simple** unital affine `k`-algebra that is amenable. Then
`R` has a unital rank model over `k`: there are integers `d_n` and a unital injective `k`-algebra
homomorphism `Φ : R → ∏_ω M_{d_n}(k)` into the rank-metric ultraproduct. Consequently `R` carries a faithful
Sylvester matrix rank function and is stably finite.

*Proof.*

**(a) One sequence for all of `R`.** `R` is affine, hence of countable `k`-dimension. Fix an exhaustion by
finite-dimensional subspaces `1 ∈ B_1 ⊆ B_2 ⊆ …` with `∪ B_n = R`. Apply amenability to `(B_n, 1/n)` to get
nonzero finite-dimensional `Q_n ⊆ R` with `dim(B_n Q_n) ≤ (1 + 1/n) dim Q_n`. Put `d_n = dim Q_n`. For every
fixed `r ∈ R` we have `r ∈ B_m` for some `m`, so for `n ≥ m`

  `dim(r Q_n + Q_n) ≤ dim(B_n Q_n) ≤ (1 + 1/n) d_n`.   (★)

**(b) The compressions.** Choose a complement `R = Q_n ⊕ T_n` and let `P_n : R → Q_n` be the projection.
Define `φ_n : R → End_k(Q_n) ≅ M_{d_n}(k)` by `φ_n(r)v = P_n(rv)`. Each `φ_n` is `k`-linear and
`φ_n(1) = id`.

**(c) Asymptotic multiplicativity in normalized rank.** For `r, s ∈ R` and `v ∈ Q_n`,
`φ_n(rs)v − φ_n(r)φ_n(s)v = P_n( r (1 − P_n)(sv) )`, so
`φ_n(rs) − φ_n(r)φ_n(s) = P_n ∘ λ(r) ∘ (1 − P_n) ∘ λ(s)|_{Q_n}`, whose rank is at most
`dim (1 − P_n)(s Q_n) ≤ dim(s Q_n + Q_n) − dim Q_n ≤ d_n/n` by (★), once `n` is large enough that `s ∈ B_n`.
Hence `rk(φ_n(rs) − φ_n(r)φ_n(s))/d_n → 0`.

So `Φ(r) = [(φ_n(r))_n]` is a unital `k`-algebra homomorphism `R → ∏_ω M_{d_n}(k)`, the quotient of
`∏_n M_{d_n}(k)` by the ideal of sequences of normalized rank tending to `0` along `ω`.

**(d) The rank function.** Put `rk(r) = lim_ω dim(r Q_n)/d_n ∈ [0,1]`. Then `rk(Φ(r)) = rk(r)`: indeed
`rank φ_n(r) = dim P_n(r Q_n) ≥ dim(r Q_n) − d_n/n` and `≤ dim(r Q_n)`, by (★).

**(e) `N = {r : rk(r) = 0}` is a two-sided ideal.**
- *Subadditive:* `dim((r+s)Q_n) ≤ dim(rQ_n) + dim(sQ_n)`, so `rk(r+s) ≤ rk(r) + rk(s)`.
- *Left:* `s(rQ_n)` is a linear image of `rQ_n`, so `dim(s r Q_n) ≤ dim(r Q_n)` and `rk(sr) ≤ rk(r)`.
- *Right:* for `n` large, `s Q_n ⊆ Q_n + U_n` with `dim U_n ≤ d_n/n` by (★); applying `r`,
  `dim(r s Q_n) ≤ dim(r Q_n) + d_n/n`, so `rk(rs) ≤ rk(r)`.

**(f) Faithfulness.** `rk(1) = 1`, so `1 ∉ N` and `N ≠ R`. `R` is simple, so `N = 0`: `rk(r) > 0` for every
`r ≠ 0`, i.e. `Φ` is injective. A faithful `rk` with `rk(1) = 1` is a faithful Sylvester matrix rank
function pulled back from the ultraproduct, and a ring with one is stably finite. ∎

**Relation to Elek.** Steps (b), (c) are Elek's proof of "amenable ⇒ almost-fd" verbatim. Step (e) is the
single-sequence form of his Proposition 4.1 ("`RR(A)` is an ideal"), and (f) is his Theorem 2 route. The
only genuinely added content is that fixing one Følner sequence makes `rk` a *single* rank function on all
of `R`, so that simplicity yields an **embedding**, not merely stable finiteness. Elek's own lower bound
`dim Ran ψ_{L,ε}(p) ≥ C_L dim V` has `C_L` depending on `L`, which does not by itself produce one
ultraproduct embedding.

## 3. Theorem 2 and the calibrations

**Theorem 2.** Every **simple** unital affine `k`-algebra of subexponential growth has a unital rank model
over `k`, in every characteristic.

*Proof.* Elek Proposition 4.1 gives amenability; apply Theorem 1. ∎

**Calibration A (the Pestov ring, growth only).** Let `X ⊆ A^Z` be an infinite minimal subshift of
**zero topological entropy** (equivalently, subexponential word complexity `p(n)`), for instance any
Sturmian subshift such as the Fibonacci one, which has `p(n) = n+1`. Put `R = LC(X, F_q) ⋊_T Z`. Generators
`{χ_{[a]} : a ∈ A} ∪ {u, u^{-1}}` give `dim R_m ≤ (2m+1)·p(2m+1)`, since any word in the generators
normalizes to `f·u^j` with `|j| ≤ m` and `f` locally constant on the window `[−m, m]`. For Sturmian `X` this
is `O(m^2)`, so `R` has GK dimension `2`, the minimum possible for an infinite-dimensional affine simple
algebra. By Theorem 2, `R` has a unital rank model over `F_q` — **with no return-word towers, no
Kakutani–Rokhlin partitions and no invariant measure**.

This is strictly weaker than what the Pestov 9.1 construction proves (exact matricial models, hence LEF,
hence sofic). Its interest is that it is a one-line growth argument and that it applies verbatim to
coefficient rings with no tower structure at all.

**Calibration B (the paradoxical end fails, as it must).** `L_{F_q}(1,2)` is simple and satisfies
`R ≅ R^2`, so it is not directly finite, hence not stably finite. By Theorem 1 it is therefore **not**
amenable. So the two calibrating rings of the UN program sit on opposite sides of amenability, as required.

## 4. Where this genuinely breaks (the honest boundary)

**Amenability is sufficient, not necessary, and it is not the measure side.**

1. **Exponential growth does not imply non-amenability.** Elek notes that `k[Γ]` is amenable for every
   finitely generated amenable `Γ`, including those of exponential growth. So growth is a sufficient
   criterion only.
2. **The naive "locally finite by amenable group" theorem is false as stated.** One might hope that
   `A ⋊ Γ` is amenable whenever `A` is locally finite and `Γ` is amenable, which would give rank models for
   the whole `Z^d` family regardless of entropy. The product Følner attempt with
   `Q = A_m ⊗ span{u^j : |j| ≤ n}` gives
   `dim(BQ)/dim(Q) ≤ [dim A_{m+J}/dim A_m] · [(2n+2J+1)/(2n+1)]`.
   The second factor tends to `1`, but the first is `p(2m+2J+1)/p(2m+1)`, which tends to `e^{2hJ} > 1` when
   the subshift has positive entropy `h`. So the attempt dies exactly at positive entropy, and the claim is
   recorded as open, not proved: see `positive-entropy-subshift-crossed-product-is-amenable`.
3. **Consequently amenability does not cover the whole measure side.** Every infinite minimal `Z`-subshift,
   positive entropy included, has exact matricial models by return-word towers, hence a rank model; but only
   the zero-entropy ones are known to be amenable. So *matricial ⇏ amenable* as far as this note goes, and
   the amenable class is not a reformulation of the measure side. Whether the inclusion is strict is
   precisely item 2.

## 5. Consequences for the UN root

Let `k` be finite and `R` a simple unital affine `k`-algebra that is amenable (for example, of subexponential
growth). Then for `N ≥ 3`:
- `EL_N(R)` is finitely generated and Kazhdan (`elementary-groups-over-fg-rings-have-property-t`);
- `EL_N(R)/Z` is infinite and simple when `R` is a Steinberg algebra of a minimal effective ample groupoid
  (`steinberg-elementary-groups-are-simple-mod-centre`, reviewed PASS), and in general whenever that node's
  ring hypotheses hold;
- `R` has a unital rank model by Theorem 1, so by
  `rank-modelled-simple-rings-give-linear-sofic-projective-el` the projective elementary groups are
  `k`-linear sofic, hence **weakly sofic**, since `GL_d(k)` is finite and normalized rank is a bi-invariant
  length function on it.

This is rung (Σ⇐) of the root, reached from an algebra-theoretic hypothesis rather than from dynamics.
