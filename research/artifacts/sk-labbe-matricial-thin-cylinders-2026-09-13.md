# Thin cylinders carry no quantum tilings of free Z^2 SFTs

Lane `sk-labbe-matricial`, 2026-09-13.
- Status: the Theorem and Corollaries 1–4 are ESTABLISHED but unreviewed; review is queued with sk-verify-5.
- Row 7, whether `LC(Ω_U, F_q) ⋊ Z^2` is exactly matricial, stays UNDECIDED.

## 0. Result

**Setting.**
- `Ω ⊆ A^(Z^2)` is an SFT with forbidden patterns in `B_r` (sup norm), and `D >= r`.
- `k` is any field and `W` any `k`-vector space. No dimension bound is assumed.
- A *scale-`D` family* on `W` consists of idempotents `E_a(z) ∈ End_k(W)` (`a ∈ A`, `z ∈ Z^2`) satisfying (Q1)–(Q3) of `sft-crossed-product-fp-iff-quantum-rigid`:
  - (Q1) partitions of unity at each site;
  - (Q2) commutation within sup-distance `2D`;
  - (Q3) `prod_(h ∈ B_D) E_(π(h))(z+h) = 0` for `π ∉ L_(B_D)(Ω)`.
- The family is *`(0,L)`-periodic* if `E_a(z + (0,L)) = E_a(z)` for all `a, z`.

**Theorem.** Let `1 <= L <= 4D+1`. A nonzero `(0,L)`-periodic scale-`D` family exists iff `Ω` has a point with period `(0,L)`. The same holds for `(L,0)`.

**Corollary 1 (free SFTs).** Suppose `Z^2` acts freely on `Ω`.
- No nonzero scale-`D` family is `(0,L)`- or `(L,0)`-periodic with `L <= 4D+1`.
- So `𝒯_(D,Λ)(Ω,k) = 0` whenever `Λ` contains `(0,L)` or `(L,0)` with `1 <= L <= 4D+1`.
- *Proof.* For a module `V`, put `E_a(z) := e_a(z mod Λ)`. Relations (T1)–(T3) give (Q1)–(Q3), and the family is `Λ`-periodic. So `V = 0`, and a nonzero algebra has a nonzero module (itself).

**Corollary 2 (witness tori).** In `torus-quantum-tilings-decide-matriciality-of-sft-rings` (free `Ω`):
- A lattice `Λ` carrying a nonzero module contains no axis vector of length `<= 4D+1`. So a rectangular witness torus has both sides `>= 4D+2`. Theorem 2(a) of that criterion gives only `max >= 4D+2`.
- In a covariant family with translations `U_1, U_2`, no power `U_i^ℓ` with `1 <= ℓ <= 4D+1` centralizes all `E_a(z)`, because centralizing is exactly periodicity along the axis.

**Corollary 3 (effective dimension).** A covariant scale-`D` family of a free `Ω` on `W = F_q^d` has `q^(d^2) > 4D+2`.
- *Proof.* The image of `U_2` in `PGL_d(F_q)` has order `> 4D+1` by Corollary 2, and `|PGL_d(F_q)| < q^(d^2)`.
- This is weak, but effective; Theorem 2(b) of the criterion is not.

**Corollary 4 (Labbé).** `Ω_U` is a free nearest-neighbour SFT (`r = 1`, `minimal-aperiodic-wang-shift-exists`). Every exact-matricial witness at scale `D` lives on a torus whose two axis periods are both `>= 4D+2`, e.g. at least `14 × 14` at `D = 3`, in both directions.

## 1. Proof of the Theorem

**(⇐)** Let `x ∈ Ω` have period `(0,L)`, and on `W = k` put `E_a(z) = [x(z) = a]`.
- (Q1) and (Q2) are clear.
- The product in (Q3) is `1` iff `x|_(z+B_D) = π`, which is impossible for `π ∉ L_(B_D)(Ω)`.
- The family is nonzero and `(0,L)`-periodic.

**(⇒)** Let the family be nonzero and `(0,L)`-periodic, with `L <= 4D+1`.

*Step 1: columns.* For `c ∈ Z` and `β ∈ B := A^(Z/L)` put `E_β(c) = prod_(j ∈ Z/L) E_(β(j))(c,j)`.
- Take two sites `(c,j)`, `(c',j')` with `|c - c'| <= 2D`. By periodicity their operators equal those of representatives whose vertical difference is at most `⌊L/2⌋ <= 2D` in absolute value. So by (Q2) they commute.
- Hence each `E_β(c)` is an idempotent, the `E_β(c)` (`β ∈ B`) are orthogonal with sum `1` by (Q1), and `E_β(c)` and `E_(β')(c')` commute when `|c - c'| <= 2D`.

*Step 2: illegal windows vanish.* Call `β_0 ⋯ β_(2D) ∈ B^(2D+1)` *legal* if for every `j ∈ Z/L` the pattern `h ↦ β_(D+h_1)(j + h_2 mod L)` on `B_D` lies in `L_(B_D)(Ω)`.
- If `β_i ⋯ β_(i+2D)` is illegal, then `prod_(s=0)^(2D) E_(β_(i+s))(c+s) = 0`.
- Reason: all factors commute (Step 1). After regrouping, the product contains the (Q3) product at `z = (c+D, j)` for an illegal ball, and that product is `0`.

*Step 3: no long legal words.* Call a word *legal* if all its windows of length `2D+1` are legal.
- Suppose legal words of every length exist. `B` is finite, so König's lemma gives a bi-infinite word with all windows legal.
- Put `x(c,j) = β_c(j mod L)`. It has period `(0,L)`, and every `B_D`-pattern of `x` lies in `L_(B_D)(Ω)`. Since `D >= r`, `x ∈ Ω`.
- So if `Ω` has no point of period `(0,L)`, there is `W_0` with no legal word of length `W_0`.

*Step 4: ordered product.* Take the product in increasing order of `c`:
`1 = prod_(c=0)^(W_0-1) ( sum_(β ∈ B) E_β(c) ) = sum_((β_0, …, β_(W_0-1))) E_(β_0)(0) E_(β_1)(1) ⋯ E_(β_(W_0-1))(W_0-1)`.
- Every term contains an illegal window.
- The consecutive factors of that window multiply to `0` by Step 2.
- So `1 = 0` on `W`, and `W = 0`. ∎

## 2. Calibration

- **Periodic tile set** `Ω = {a^(Z^2)}`: it has points of every period, so (⇐) gives one-dimensional families on every thin torus. That is correct, since this `Ω` is not free.
- **SFTs with vertically periodic points but no doubly periodic point:** the Theorem supplies a classical nonzero `(0,L)`-periodic family. This is consistent with Theorem 2(a) of the criterion, which needs both periods small.
- **Wall certificates** (`W = k^2`, two configurations agreeing on a wide wall): these give contextual families, but they are not `(0,L)`-periodic for small `L` unless both configurations are. Consistent.
- **One dimension:** Steps 2–4 alone are the algebraic reason a one-dimensional local tiling algebra with no long legal word is zero, even though sites farther apart than `2D` need not commute.

## 3. What this does not reach

- **Fat tori** (both axis periods `>= 4D+2`). Columns no longer commute internally. No linear order of commuting blocks puts every `D`-ball inside a consecutive window. The ordered-product mechanism is one-dimensional, so row 7 needs a genuinely two-dimensional obstruction or a contextual construction on fat tori.
- **Diagonal short vectors of `Λ`.** Slices along a diagonal meet a `D`-ball in `4D+1` slices, and cross distances exceed `2D`. The argument does not apply as stated.
- **Growth.** Corollary 3 gives only `d > (log_q(4D+2))^(1/2)`.

## 4. Credit and bounds

- The argument is my own. The expansion is the noncommutative distributive law, and the periodic-point step is König's lemma.
- Definitions come from `sft-crossed-product-fp-iff-quantum-rigid` and `torus-quantum-tilings-decide-matriciality-of-sft-rings`.
- Novelty check (bounded): grep of main for thin tori or cylinders, column patterns and ordered products in the SFT context found no prior statement. No literature search.
