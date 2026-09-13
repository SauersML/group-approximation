# The algebraic Tarski dichotomy for Steinberg algebras

Lane `un-tarski`, 2026-09-13. Unreviewed. This is the **measure side** of the UN dichotomy. The
paradox side is lane `un-paradox` (`no-invariant-measure-steinberg-elementary-no-mf-quotient`,
`stably-infinite-ring-elementary-groups-have-no-mf-quotient`, artifact
`un-paradox-groupoid-tarski-2026-09-13-part2.md`); this artifact does not repeat it. Together the two
give one theorem with two exclusive branches.

## 0. Standing hypotheses and notation

`k` is a countable field, `𝒢` a Hausdorff ample second countable groupoid with **compact** unit space
`X = 𝒢^(0)`, and `R = A_k(𝒢)` the Steinberg algebra, unital with `1 = 1_X`. `K(X)` is the set of
compact open subsets of `X`. `S(𝒢)` is the type semigroup (Rainone–Sims), `θ = [X] ∈ S(𝒢)`, and
`V(R)` is the monoid of finitely generated projective right `R`-modules with the algebraic preorder,
`[1] = [R_R]`.

`θ` is **completely non-paradoxical** if `(n+1)θ ≰ nθ` for every `n ∈ ℕ`; otherwise `𝒢` is
**paradoxical at θ**.

A **Sylvester matrix rank function** on `R` is `rk : ⋃_n M_n(R) → [0,∞)` with `rk(0)=0`, `rk(1)=1`,
`rk(AB) ≤ min(rk A, rk B)`, `rk(A ⊕ B) = rk A + rk B`, and `rk([A C; 0 B]) ≥ rk A + rk B`. It is
**faithful** if `rk(A) = 0` only for `A = 0`.

Throughout, `𝒢` **minimal** means `X` has no proper nonempty closed invariant subset, and
**effective** means the interior of the isotropy is `X`. By BCFS/Steinberg (on main,
`steinberg-algebra-simple-iff-minimal-effective`), `R` is simple iff `𝒢` is minimal and effective.

## 1. The bridge, and why the dichotomy is field-independent

**Lemma 1.1 (already on main, `no-invariant-measure-steinberg-elementary-no-mf-quotient`).** There is
an order-preserving monoid homomorphism `ι : S(𝒢) → V(R)`, `[U] ↦ [1_U R]`, for every field `k`.

Sketch, for completeness: a compact open bisection `B` gives `1_B · 1_{B^{-1}} = 1_{r(B)}` and
`1_{B^{-1}} · 1_B = 1_{s(B)}`, so `[1_{s(B)}] = [1_{r(B)}]` in `V(R)`; disjoint unions go to
orthogonal direct sums; levels of `X × ℕ` go to matrix sizes. Lane `un-paradox` derived the same map
independently.

`S(𝒢)` does not mention `k`. Everything below that is phrased through `ι` is therefore a
**field-independent** statement about `𝒢` with a field-dependent shadow in `R`. That is the structural
reason why the non-MF paper (over `F_2`) and the Pestov 9.1 answer (over `F_q`) are two branches of
one groupoid statement rather than two unrelated computations.

## 2. The measure side: rank ⟹ stably finite ⟹ non-paradoxical ⟺ invariant measure

**Lemma 2.1.** If `R` is simple and unital and `rk` is a nonzero Sylvester matrix rank function on
`R`, then `rk` is faithful.

*Proof.* `I = {a ∈ R : rk(a) = 0}` is a two-sided ideal: `rk(ab) ≤ rk(a)` and `rk(ba) ≤ rk(a)` give
closure under multiplication, and `rk(a+b) ≤ rk(a) + rk(b)` (subadditivity, which follows from the
axioms) gives closure under addition. `1 ∉ I` since `rk(1) = 1`. By simplicity `I = 0`. The same
argument in `M_n(R)`, simple whenever `R` is, gives faithfulness at every matrix size. ∎

**Lemma 2.2.** A faithful Sylvester matrix rank function on `R` forces `R` stably finite.

*Proof.* Let `AB = I_n` in `M_n(R)`. Then `n = rk(I_n) ≤ min(rk A, rk B) ≤ n`, so `rk B = n`. The
element `e = BA` is idempotent and `B(AB) = B` gives `rk(B) ≤ rk(BA)`, so `rk(e) = n`. Under the
Malcolmson/Schofield correspondence a Sylvester matrix rank function is the matrix form of a Sylvester
module rank function `dim`, and for an idempotent `e ∈ M_n(R)`, `R^n = eR^n ⊕ (1-e)R^n` gives
`rk(e) + rk(I_n - e) = n`. Hence `rk(I_n - e) = 0`, so `I_n = e = BA` by faithfulness. ∎

**Theorem 2.3 (stably finite ⟹ completely non-paradoxical).** If `R` is stably finite then `θ` is
completely non-paradoxical.

*Proof.* Contrapositive. Suppose `(n+1)θ ≤ nθ`. Applying `ι` of Lemma 1.1, `(n+1)[1] ≤ n[1]` in
`V(R)`, so there is an idempotent `p ∈ M_n(R)` with `p ~ I_{n+1}`: there are `x ∈ M_{n+1,n}(R)` and
`y ∈ M_{n,n+1}(R)` with `xy = I_{n+1}` and `yx = p ≤ I_n`. Pad `x` and `y` by a zero column and row to
`x̃, ỹ ∈ M_{n+1}(R)`. Then `x̃ỹ = I_{n+1}` while `ỹx̃ = diag(p, 0) ≠ I_{n+1}` (its last diagonal entry
is `0 ≠ 1`). So `M_{n+1}(R)` is not directly finite and `R` is not stably finite. ∎

**Theorem 2.4 (completely non-paradoxical ⟺ invariant measure, `𝒢` minimal).** Suppose `𝒢` is
minimal. Then `θ` is completely non-paradoxical iff `X` carries a `𝒢`-invariant Borel probability
measure.

*Proof.* (⟸) An invariant probability measure restricts to a state `ν` on `S(𝒢)` with `ν(θ) = 1`; by
Rainone–Sims Thm `Tarski` (on main, `rainone-sims-tarski-alternative-for-monoids`) a nontrivial state
with `ν(θ) = 1` forces complete non-paradoxicality.

(⟹) Tarski gives a nontrivial state `ν : S(𝒢) → [0,∞]` with `ν(θ) = 1`. Minimality makes `ν` finite
and faithful on nonempty compact opens: for `∅ ≠ U ∈ K(X)` the sets `r(B)` over compact open
bisections `B` with `s(B) ⊆ U` cover the compact `X`, so `θ ≤ m[U]` for some `m`, whence
`1 = ν(θ) ≤ m·ν(U)` and `0 < 1/m ≤ ν(U) ≤ ν(θ) = 1 < ∞`. So `ν|_{K(X)}` is a finitely additive
invariant probability measure on the clopen algebra of the compact totally disconnected space `X`;
since a clopen set admits no infinite disjoint clopen cover (compactness), finite additivity is
countable additivity, and `ν` extends to an invariant Borel probability measure. The extension step is
on main as `abbl-type-semigroup-states-extend-to-invariant-measures`. ∎

**Remark 2.3a (the ring-level equivalence is un-middle's).** Lane `un-middle` landed
`simple-ring-stably-finite-iff-unit-not-paradoxical`: for a countable simple unital `R`, `R` is stably
finite iff `[R]` is not paradoxical in `V(R)` iff `V(R)` has a state normalized at `[R]` (via the KMP
Tarski theorem for preordered monoids, `kmp-tarski-theorem-preordered-monoids`). Theorem 2.3 is not
that statement and does not reprove it: it is the **transfer from the groupoid to the ring**, from
paradox of `θ` in `S(𝒢)` to failure of stable finiteness of `A_k(𝒢)`. The two compose as

  `θ` paradoxical in `S(𝒢)` ⟹ `[1]` paradoxical in `V(R)` ⟺ `R` not stably finite,

the first implication being `ι` and the equivalence being un-middle's.

**Open 2.3b (does `ι` reflect paradox?).** The converse transfer is open: if `[1]` is paradoxical in
`V(A_k(𝒢))`, is `θ` paradoxical in `S(𝒢)`? Equivalently, does `ι` reflect the paradox relation at
`θ`? It would follow from `ι : S(𝒢) → V(A_k(𝒢))` being an order-isomorphism, which holds in both
calibrating cases (`V(L_K(E)) ≅ M_E ≅ S(𝒢_E)` by Ara–Moreno–Pardo, and for Cantor `ℤ`-systems), but
which this lane did not find stated for general ample Hausdorff `𝒢`. The obstruction is that `V(R)` is
computed from arbitrary idempotents in `M_n(R)`, and nothing here diagonalizes them onto compact open
subsets of `X × ℕ`.

**Why 2.3b is worth settling.** `S(𝒢)` does not mention `k`. So a positive answer would make stable
finiteness of `A_k(𝒢)` **independent of the field**: a single dynamical property of `𝒢` would decide
it simultaneously in characteristic 0 and characteristic `p`. By §4.1 that would carry Kaplansky
stable finiteness in characteristic `p` for this class of algebras, so 2.3b is itself at least
Kaplansky-hard and should not be expected cheaply. It is recorded as the open claim
`type-semigroup-reflects-paradox-of-steinberg-algebra`.

**Corollary 2.5 (the chain).** For minimal `𝒢` with compact unit space and any countable field `k`:

  `R` has a nonzero Sylvester matrix rank function
   ⟹ `R` is stably finite
   ⟹ `θ` completely non-paradoxical
   ⟺ `X` carries a `𝒢`-invariant probability measure.

If `𝒢` is also effective, `R` is simple and "nonzero" may be dropped from the first line by Lemma 2.1.

This is exactly complementary to `un-paradox`: contrapositively, no invariant measure forces `𝒢`
paradoxical at `θ`, which forces `2n[1] ≤ n[1]`, which kills every MF quotient of `EL_N(R)` for
`N ≥ 2n`.

## 3. Closing the loop in characteristic zero

The missing arrow is *invariant measure ⟹ rank function*. Over a field embeddable in `ℂ` it is free.

**3.0 A state on `V(R)` is strictly weaker than a Sylvester matrix rank function.** This is the reason
§3 is not a corollary of un-middle's equivalence. A state on `V(R)` is a dimension function on
**finitely generated projective modules** only. A Sylvester matrix rank function assigns a value to
**every** matrix over `R`, singular ones included, compatibly with products and diagonal sums; it
restricts to a state on `V(R)` by `[e] ↦ rk(e)`, but there is no converse in general — recovering a
rank on all matrices amounts to measuring images of arbitrary (non-split) maps, which the monoid
`V(R)` cannot see. Over a von Neumann regular ring the two agree, because every matrix has an
idempotent image; Steinberg algebras of the groupoids here are not regular. So Corollary 2.5 begins
one strict step above un-middle's criterion, and Theorem 3.1 supplies that step in characteristic 0.

**Theorem 3.1.** Let `𝒢` be minimal, effective, Hausdorff, ample, second countable with compact unit
space, and let `μ` be a `𝒢`-invariant Borel probability measure on `X`. Let `k ⊆ ℂ` be a countable
subfield. Then `A_k(𝒢)` carries a faithful Sylvester matrix rank function `rk` with `rk(1_U) = μ(U)`
for every `U ∈ K(X)`. Consequently `A_k(𝒢)` is stably finite, and all four conditions of
Corollary 2.5 are equivalent.

*Proof.* Define `τ : A_ℂ(𝒢) → ℂ` by `τ(f) = ∫_X f|_X dμ`.

*`τ` is a trace.* It suffices to check it on compact open bisections `B, C`. Now
`BC ∩ X = {bc : b ∈ B, c ∈ C, bc ∈ X}`, which is carried bijectively by `r` onto `r(B ∩ C^{-1})`, and
symmetrically `CB ∩ X` is carried onto `r(C ∩ B^{-1}) = s(B ∩ C^{-1})`. So
`τ(1_B 1_C) = μ(r(B ∩ C^{-1}))` and `τ(1_C 1_B) = μ(s(B ∩ C^{-1}))`, equal because `μ` is invariant
and `B ∩ C^{-1}` is a compact open bisection.

*`τ` is faithful and positive.* Write `f = Σ_i c_i 1_{B_i}` with the `B_i` pairwise disjoint compact
open bisections. Then `f^*f = Σ_{i,j} c̄_i c_j 1_{B_i^{-1}B_j}`, and `B_i^{-1}B_j ∩ X ≠ ∅` forces
`B_i ∩ B_j ≠ ∅`, hence `i = j`. So `τ(f^*f) = Σ_i |c_i|² μ(s(B_i))`. Minimality makes `μ` of full
support (finitely many translates of any nonempty compact open cover `X`), so `τ(f^*f) > 0` for
`f ≠ 0`.

*The von Neumann algebra.* Each `1_B` acts boundedly on the GNS space `L²(A_ℂ(𝒢), τ)`, since
`τ((1_B x)^*(1_B x)) = τ(x^* 1_{s(B)} x) ≤ τ(x^*x)`; a general element is a finite sum, hence bounded.
Let `M` be the von Neumann algebra generated by the left action. `τ` extends to a faithful normal
tracial state on `M`, so `M` is finite.

*The rank function.* For `A ∈ M_n(A_ℂ(𝒢)) ⊆ M_n(M)` put `rk(A) = (τ ⊗ Tr_n)(LP(A))`, `LP` the left
support projection. This is the classical dimension function of a finite von Neumann algebra and
satisfies the Sylvester axioms, with `rk(1) = τ(1) = μ(X) = 1`; faithfulness of `τ` on `M` gives
`rk(A) = 0 ⟹ A = 0`. Restrict along `A_k(𝒢) ⊆ A_ℂ(𝒢)`: the axioms and faithfulness are inherited.
Finally `rk(1_U) = τ(1_U) = μ(U)`. Stable finiteness is Lemma 2.2. ∎

*Flagged:* that the Murray–von Neumann dimension of a finite von Neumann algebra satisfies the
Sylvester matrix rank axioms is classical and is used here without re-derivation from a source.

**Every countable field of characteristic 0 embeds in `ℂ`** (transcendence degree at most `ℵ_0` over
`ℚ`), so Theorem 3.1 covers characteristic 0 entirely.

## 4. Why the loop does not close in characteristic p, and why that is where the objects are

**4.1 The obstruction is Kaplansky-hard.** Lane `un-paradox` landed
`measure-side-stable-finiteness-contains-char-p-kaplansky`: proving *invariant measure ⟹ stably
finite* for all free minimal Cantor actions over a field `k` proves Kaplansky's stable finiteness
conjecture over `k`. So the arrow missing from Corollary 2.5 in characteristic `p` is not a gap in
bookkeeping; it contains an open conjecture.

**4.2 Property (T) forces characteristic p.** Ershov–Jaikin-Zapirain gives (T) for `EL_n(R)`, `n ≥ 3`,
when `R` is **finitely generated as a ring**. A field that is finitely generated as a ring is finite
(Artin–Tate / general Nullstellensatz). So `A_k(𝒢)` is finitely generated as a ring only if `k` is
finite, and the EJZ route to Kazhdan elementary groups is available **only in positive
characteristic**.

**4.3 The consequence.** Characteristic 0 has the exact dichotomy but produces no Kazhdan groups;
characteristic `p` produces the Kazhdan groups but has an open arrow. The Kazhdan simple groups of
this program therefore live exactly where the equivalence is not known, and the measure branch has to
be witnessed *by hand* in each case. That is precisely what the Pestov 9.1 answer does: its
return-word tower embedding `LC(X,F_q) ⋊ ℤ ↪ ∏_ω M_N(F_q)` is a construction of the missing arrow for
one groupoid, not an instance of a general theorem. Ara–Claramunt (on main,
`cantor-z-crossed-product-embeds-in-continuous-factor`) give the rank-function form of the same arrow
for every Cantor `ℤ`-system and every field, which is the largest class where the arrow is known.

## 5. Model tests

| `𝒢` | `S(𝒢)` at `θ` | branch | `R = A_k(𝒢)` | `EL_n(R)` |
|---|---|---|---|---|
| Cuntz groupoid `𝒢_2` | `2θ = θ` | paradox | `L_k(1,2)`, purely infinite, not directly finite | no nontrivial MF quotient (non-MF paper Cor l.1016) |
| minimal subshift `X ⋊ ℤ` | invariant measure | measure | `LC(X,F_q)⋊ℤ`, stably finite (towers) | LEF, sofic (Pestov 9.1) |
| boundary action `∂F_d ⋊ F_d` | no invariant measure | paradox | purely infinite | no nontrivial MF quotient (`boundary-action-elementary-simple-kazhdan-not-mf`) |
| Boldrini–Prasad minimal `F_∞` actions | `S(𝒢)` **not** almost unperforated | neither branch is forced | unknown | unknown (lane `un-middle`) |

The first two rows are the two calibrating cases the UN program must reproduce, and they land in
opposite branches, as required. The fourth row is why §6 assumes almost unperforation.

## 6. Sharpening the paradox branch under almost unperforation

`un-paradox` gets the rank threshold `N ≥ 2n` from `2n[1] ≤ n[1]`. Almost unperforation of `S(𝒢)`
pushes the paradox down to the unit itself and gives the best possible threshold.

Recall `S` is **almost unperforated** if `(m+1)x ≤ my` for some `m ≥ 1` implies `x ≤ y`.

**Lemma 6.1.** If `(n+1)θ ≤ nθ` then `Nθ ≤ nθ` for every `N ≥ n`.

*Proof.* Adding `θ` to `(n+1)θ ≤ nθ` gives `(n+2)θ ≤ (n+1)θ ≤ nθ`, and induction gives
`(n+m)θ ≤ nθ`. ∎

**Lemma 6.2.** If `S(𝒢)` is almost unperforated and `θ` is not completely non-paradoxical, then
`2θ ≤ θ`.

*Proof.* Fix `n` with `(n+1)θ ≤ nθ`. By Lemma 6.1, `(2n+2)θ ≤ nθ`, that is `(n+1)(2θ) ≤ n·θ`. Almost
unperforation with `x = 2θ`, `y = θ`, `m = n` gives `2θ ≤ θ`. ∎

**Lemma 6.3.** In addition let `𝒢` be minimal. Then `2[V] ≤ [V]` for every nonempty `V ∈ K(X)`.

*Proof.* Lemma 6.2 gives `2θ ≤ θ`, hence `jθ ≤ θ` for all `j ≥ 1` by induction. Minimality gives
`θ ≤ m[V]` for some `m`, and `[V] ≤ θ`. Then
`(m+1)(2[V]) = (2m+2)[V] ≤ (2m+2)θ ≤ θ ≤ m[V]`, so almost unperforation with `x = 2[V]`, `y = [V]`
gives `2[V] ≤ [V]`. ∎

**Theorem 6.4.** Let `𝒢` be minimal, effective, Hausdorff, ample, second countable with compact unit
space, `S(𝒢)` almost unperforated, `k` a countable field, `R = A_k(𝒢)`. Then exactly one of:

1. `X` carries a `𝒢`-invariant probability measure; or
2. `R` is **properly purely infinite** and simple; `R` is not directly finite; and for every `n ≥ 2`
   every homomorphism from `EL_n(R)` to an MF group is trivial.

*Proof.* The two cases are exclusive and exhaustive by Theorem 2.4. In case 2, `θ` is paradoxical, so
Lemma 6.3 gives `2[V] ≤ [V]` for every nonempty compact open `V`; applying `ι` (Lemma 1.1), every
`1_V` is a properly infinite idempotent of `R`. Minimality makes `𝒢` strongly effective (the only
closed invariant subsets of `X` are `∅` and `X`, and `𝒢` is effective), so Larki Thm 3.4
(on main, `purely-infinite-steinberg-algebras-characterized`), implication (2) ⟹ (1), gives `R`
properly purely infinite. Simplicity is BCFS/Steinberg. Taking `V = X`, `2[1] ≤ [1]` gives `s, t ∈ R`
with `ts = 1 ≠ st`, so `R` is not directly finite, and the non-MF paper's Cor `cor:simple-infinite-ring`
(tex l.1016: "If `R` is a countable simple unital ring that is not directly finite, then every
homomorphism from `EL_n(R)` to an MF group is trivial for every `n ≥ 2`") applies. ∎

Theorem 6.4 improves `un-paradox`'s threshold from `N ≥ 2n` to `N ≥ 2`, at the cost of almost
unperforation, and adds pure infiniteness of `R`. Both calibrating groupoids have almost unperforated
type semigroups; the Boldrini–Prasad examples do not, which is exactly the hypothesis that fails in
row 4 of §5.

## 7. What is unreviewed, and what is open

- **Unreviewed:** Lemmas 2.1, 2.2, Theorems 2.3, 2.4, 3.1 and 6.1–6.4 are this lane's own proofs.
- **Standard and not re-derived:** the Malcolmson/Schofield matrix–module rank correspondence, and the
  Sylvester axioms for the Murray–von Neumann dimension of a finite von Neumann algebra.
- **Cited from main:** Rainone–Sims Thm `Tarski`, the ABBL extension of states to invariant measures,
  Larki Thm 3.4, BCFS/Steinberg simplicity, the non-MF Cor l.1016, and `un-paradox`'s bridge.
- **Open:** `invariant-measure-gives-rank-function-any-field`. Known for `k ⊆ ℂ` (§3), for Cantor
  `ℤ`-systems over any field (Ara–Claramunt), and for the Pestov groupoid by explicit towers. Contains
  Kaplansky stable finiteness over `k` in general (§4.1).
