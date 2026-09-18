# Houghton groups with five rays: a one-auxiliary-ray splitting lemma, and a polynomial Dehn function for H_5

Lane swarm-0917-w8-w8-z-break, 2026-09-18. Zaremsky Problem 1.24. Status: complete
proof, unreviewed. The derivation of Lemma A was also run literally by a script
(see §4).

All notation, the presentation `P`, and the section numbers `§1–§6` refer to
`research/artifacts/zp-houghton-pours-2026-09-17.md` (the "six-ray note"). There,
`n >= 6` enters only through Lemma 1.2 (two auxiliary rays `e,f`). Its Remark 6.2
says: "Every other step chooses at most four distinct rays at a time." Below,
Lemma 1.2 is replaced by Lemma A, which needs one auxiliary ray. The rest of the
six-ray note then runs for `n = 5` with a worse exponent.

## 1. The obstruction in the six-ray proof, and how to avoid it

In Lemma 1.2 the correction pour `X = E_(d,c)(m_1)` (supported on rays `c,d`) must
pass the middle pour `Y = E_(a,b)(m_2)` (supported on rays `a,b`). As permutations
they commute. To commute them *letterwise*, the six-ray note routes `X` via `e` and
`Y` via `f`. With five rays `a,b,c,d,e`, any route of `X` lies in `{a,b,e}` and any
route of `Y` lies in `{c,d,e}`. So no two pour words for `X` and `Y` have disjoint
letters.

The fix: do not commute `X` past `Y` as a whole. Route `Y` via `e`, so
`Y = λ_ae^(m_2) λ_eb^(m_2)`, and commute `X` past the two halves separately:

- `λ_ae^(m_2)` has letters in `{a,e}`. Route `X` via `b`: `X_b = λ_db^(m_1) λ_bc^(m_1)`
  has letters in `{b,c,d}`.
- `λ_eb^(m_2)` has letters in `{b,e}`. Route `X` via `a`: `X_a = λ_da^(m_1) λ_ac^(m_1)`
  has letters in `{a,c,d}`.

The halves of `Y` are not supported on `{a,b}` as permutations. But each half
commutes with `X` as a permutation, since `X` is supported on `{c,d}` and the halves
on `{a,e}` and `{b,e}`. So each letterwise commutation is legitimate. Between the
two halves, `X` changes route from `b` to `a`, at cost `W(m_1)`.

## 2. Lemma A (five-ray splitting)

Let `n >= 5` and let `W(m)` be as in §1 of the six-ray note:

```text
W(m) = max { Area( E^c_(a,b)(m) · E^d_(a,b)(m)^(-1) ) : a,b,c,d distinct rays }.
```

**Lemma A.** For `m_1, m_2 >= 1`,
`W(m_1 + m_2) <= 3W(m_1) + 2W(m_2) + 4m_1m_2 + 4m_1`.

*Proof.* Fix distinct `a,b,c,d` and choose `e` with `a,b,c,d,e` distinct, using
`n >= 5`. Put `m = m_1 + m_2`. Start from `E^c_(a,b)(m) = λ_ac^m λ_cb^m`. Each step
names the relators it uses. "Route change `(x,y; r -> r')` of size `k`" means
replacing `E^r_(x,y)(k)` by `E^(r')_(x,y)(k)` with `x,y,r,r'` distinct. It costs
`<= W(k)`, since `Area(u v^(-1))` bounds the replacement of `u` by `v`.

- **A (insert).** Insert `λ_ad λ_da` in nested fashion `m_1` times at the front,
  and `λ_bd λ_db` `m_1` times at the end. This uses `2m_1` relators `λ_xy λ_yx`
  and gives

  ```text
  λ_ad^(m_1) · X_a · Y_c · Z_b · λ_db^(m_1),
  X_a = λ_da^(m_1) λ_ac^(m_1) = E^a_(d,c)(m_1),   Y_c = E^c_(a,b)(m_2),
  Z_b = λ_cb^(m_1) λ_bd^(m_1) = E^b_(c,d)(m_1).
  ```

- **B.** Route change `(a,b; c -> e)` of size `m_2` turns `Y_c` into
  `Y_e = λ_ae^(m_2) λ_eb^(m_2)`. This costs `W(m_2)`.
- **C.** Route change `(d,c; a -> b)` of size `m_1` turns `X_a` into
  `X_b = λ_db^(m_1) λ_bc^(m_1)`. This costs `W(m_1)`.
- **D.** Move `X_b` right past `λ_ae^(m_2)`. The ray supports `{d,b}`, `{b,c}` and
  `{a,e}` are disjoint, so this takes `2m_1m_2` commutator relators.
- **E.** Route change `(d,c; b -> a)` of size `m_1` turns `X_b` back into `X_a`.
  This costs `W(m_1)`.
- **F.** Move `X_a` right past `λ_eb^(m_2)`. The ray supports `{d,a}`, `{a,c}` and
  `{e,b}` are disjoint, so this takes `2m_1m_2` commutator relators. The word is now
  `λ_ad^(m_1) · λ_ae^(m_2) λ_eb^(m_2) · X_a · Z_b · λ_db^(m_1)`.
- **G.** Route change `(c,d; b -> a)` of size `m_1` turns `Z_b` into
  `Z_a = λ_ca^(m_1) λ_ad^(m_1)`. This costs `W(m_1)`.
- **H.** `X_a Z_a = λ_da^(m_1) λ_ac^(m_1) λ_ca^(m_1) λ_ad^(m_1)` cancels from the
  middle out, using `2m_1` relators `λ_xy λ_yx`.
- **I.** Route change `(a,b; e -> d)` of size `m_2` turns `Y_e` into
  `E^d_(a,b)(m_2) = λ_ad^(m_2) λ_db^(m_2)`. This costs `W(m_2)`.

The word is now literally `λ_ad^(m_1) λ_ad^(m_2) λ_db^(m_2) λ_db^(m_1) = E^d_(a,b)(m)`.
In every route change the four rays are distinct, as the step names show.

The total is `3W(m_1) + 2W(m_2)` plus `2m_1 + 4m_1m_2 + 2m_1` elementary relators. ∎

*Accounting remark on the six-ray note.* Lemma 1.2 there writes
`λ_ac^(m_1) ≡ λ_ad^(m_1) E^a_(d,c)(m_1)` "freely". That identity inserts
`λ_ad^(m_1) λ_da^(m_1)`, which costs `m_1` relators `λ_xy λ_yx`, because `λ_da` is
not the formal inverse of `λ_ad` in `P`. The same holds on the right. So its bound
should read `... + 4m_1m_2 + 4m_1`. This does not affect Proposition 1.3 there: the
last condition becomes `K >= 2 + 4/m`, which `K >= 3` still gives for `m >= 5`.

## 3. Consequences for n = 5

**Proposition B.** Let `n >= 5` and `β = log_2 5 < 2.33`. Then `W(m) <= 45 m^β` for
all `m >= 1`.

*Proof.* `W(1) = 1`: the length-4 relator `λ_ac λ_cb λ_bd λ_da` lies in `Q`. Let
`W̄(m) = max_(j <= m) W(j)`. For `2 <= m' <= 2^j`, apply Lemma A with
`m_1 = ⌊m'/2⌋` and `m_2 = ⌈m'/2⌉`. Both are `<= 2^(j-1)`. Also `4m_1m_2 <= m'^2` and
`4m_1 <= 2m'`. So

```text
W̄(2^j) <= 5 W̄(2^(j-1)) + 4^j + 2^(j+1) <= 5 W̄(2^(j-1)) + 2·4^j      (j >= 1).
```

Iterating,
`W̄(2^j) <= 5^j (W(1) + 2 Σ_(i>=1) (4/5)^i) = 9·5^j`. For `2^(j-1) < m <= 2^j`,
`W(m) <= 9·5^j = 9 (2^j)^β < 9 (2m)^β = 45 m^β`. ∎

(Splitting unevenly, with `m_1 ≈ 0.4m`, lowers the exponent to about `2.27`. This is
not needed.)

**Theorem C.** For `n = 5` (indeed for every `n >= 5`),
`δ_(H_n)(x) ≼ x^(6+β)`, with `6 + β = 6 + log_2 5 < 8.33`. In particular the Dehn
function of `H_5` is polynomially bounded.

*Proof.* Run §§2–6 of the six-ray note with `n = 5`, using Proposition B in place of
Proposition 1.3. Check the rays and the exponents step by step.

- **Rays.** Every step outside Lemma 1.2 needs at most four distinct rays.
  - Lemma 2.1 uses `x,u,u',e` with `rays(X) = {x}` for `X = τ_x`. The only
    application is (2.2).
  - Theorem 3.1 uses `a,b,c,d`.
  - Proposition 4.1 uses: in (ii), `x,y,c',d'`, with reroutes through (2.2), each
    using four rays; in (iii), `x,y,z,c'`; in (iv), `x,y,c,d`.
  - Lemma 4.2 uses `x,z,w,c'`.
  - §5 and §6 choose no new rays. Corollary 5.3 uses `q <= n-1`, which is valid for
    every `n`.

  Every use of `W` is a route change of a pour on four distinct rays, and `W` is
  bounded by Proposition B for `n = 5`. Section 0 (the presentation `P`, the
  set `Q`, and the transfer to Lee's presentation) is written for arbitrary
  `n >= 3`. So is the 09-13 input (Lemma 1, Lemma 3 and Step 2 of §5 of
  `zp-houghton-dehn-2026-09-13-part1.md`), which the established claim
  `houghton-dehn-polynomially-equivalent-to-commutation-area` states for every
  `n >= 3`.
- **Exponents.** With `W ≼ m^β` and `β > 2`:
  - `R(k) <= 2W(k) + 6k ≼ k^β`, by (2.2).
  - `F(k) ≼ k^β`, by Theorem 3.1, whose extra terms are `O(k^2)`.
  - `E(R) ≼ R^β`, by Proposition 4.1, whose extra terms are `O(R^2)`.
  - The cost bound of Lemma 4.2 is `≼ R^β`.
  - Lemmas 5.5 and 5.6 cost `Γ(R) = C(R R̄(R) + R^2 Ē(R+2)) ≼ R^(2+β)`.
  - In Theorem 6.1 with `R = O(L)`, `M = O(L^2)` and `ℓ = O(L)`:
    - Sort costs `O(L^2)`.
    - Translate costs `O(L^3)`.
    - Normalize costs `M ℓ Γ(R) ≼ L^(5+β)`.
    - Eliminate takes `nR · M` moves, each costing `C R^3 Ē(R+1) + 4R Ē(R) ≼ R^(3+β)`,
      so `≼ L^(6+β)` in total.

So `Area_P(w) ≼ L^(6+β)` for null-homotopic Lee words of length `L`, and
`Area_Lee <= K Area_P` (§0). ∎

**Corollary D.** For `n = 5`, the far commutation of the six-ray note satisfies
`Area([α, α^(g_1^(-k))]) ≼ k^(log_2 5)`. The commutation area `A` of
`houghton-dehn-polynomially-equivalent-to-commutation-area` satisfies
`A(ℓ) <= δ(2ℓ+2) ≼ ℓ^(6+log_2 5)`.

## 4. Machine check of Lemma A

`experiments/houghton-five-rays-2026-09-17/verify_splitting.py` executes steps A–I
literally on words in the letters `λ_xy` over the rays `{1,...,5}`. It does this for
all 120 labelings `(a,b,c,d,e)` and all `1 <= m_1, m_2 <= 6`, which is 4320
derivations. At each move it checks:

- the move is a legal instance of its relator type: nested insertion or
  cancellation of `λ_xy λ_yx`; a swap of two letters with disjoint ray supports; or
  a route change of a literal pour subword with four distinct rays;
- the intermediate word still represents the starting permutation of `[5] x N`;
- the final word is literally `E^d_(a,b)(m)`.

It also checks that the count is exactly `4m_1m_2 + 4m_1` elementary relators,
plus route changes of sizes `m_1, m_1, m_1, m_2, m_2`. Output:

```text
checked 4320 derivations (120 labelings, 1 <= m1,m2 <= 6)
each: 3 route changes of size m1, 2 of size m2, 4*m1*m2 + 4*m1 elementary relators
```

## 5. What stays open: n = 3 and n = 4

With four rays `a,b,c,d`, `W` is still defined, but no pour route lies outside the
four rays of the pours involved. In the Lemma A pattern, `X = E_(d,c)(m_1)` must
pass a factor of a word for `Y = E_(a,b)(m_2)`, and `Y` is routed via `c` or `d`.
Its letters then include `λ_ac` or `λ_cb` (route `c`), or `λ_ad` or `λ_db`
(route `d`). As a permutation, such a half-pour `λ_ac^(m_2)` does not commute with
`X`, because both move ray `c`. So neither the six-ray nor the five-ray trick gives
a letterwise commutation. A four-ray argument needs a genuinely two-dimensional
filling of the skew square `λ_ac^m λ_cb^m λ_bd^m λ_da^m`, whose translation image is
a non-planar quadrilateral in `Z^3`. For `n = 3` the pour itself needs three rays,
and no route change exists at all.
