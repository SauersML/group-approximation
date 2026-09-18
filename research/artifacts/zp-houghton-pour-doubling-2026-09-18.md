# Doubling three-ray pours along the route ray: polynomial two-ray normal forms, and a polynomial Dehn function for H_4

swarm-0917-w11-w11-z-follow, 2026-09-18.

**Summary.**

- In `H_3`, with rays `a,b,c`, the pour `E^c_(a,b)(m) = λ_ac^m λ_cb^m` can be rewritten
  with polynomial area into an explicit two-ray word `N_m` in the letters `λ_ab, λ_ba,
  τ_a, τ_b`. The word has length `<= m^5` (Proposition 5).
- The tool is the doubling endomorphism `Δ` of
  `research/artifacts/zp-houghton-three-rays-2026-09-18.md` §B, with the **route ray
  `c` as the special ray**. Then `Δ(λ_ac) = λ_ac^2` and `Δ(λ_cb) = λ_cb^2` exactly.
  So the lifted word `Δ̂(E^c_(a,b)(m))` is literally `E^c_(a,b)(2m)`. The odd step
  `m -> 2m+1` costs only linear area, by conjugating with `λ_ca`.
- This is the family `A_3` of Remark 3.1 of
  `research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md`, with a different
  two-ray word in place of the bubble sort. The splitting argument there works for any
  two-ray word representing the pour, so `W_4 ≼ m^β` for some `β` (Theorem 6), and
  **`δ_(H_4)` is polynomially bounded** (Theorem 7).
- `H_4` is closed without any input about the Dehn function of `H_3`. The ray-count
  split of `houghton-groups-have-polynomial-dehn-function` now has the single hole
  `n = 3`.
- The exponent is polynomial but not explicit: it contains `log_2 K`, where `K` is the
  area-transfer constant of `Δ` on Lee's relators.

## 0. Conventions

Everything is as in `research/artifacts/zp-houghton-pours-2026-09-17.md` §0.

- Permutations act on the right. Words are read left to right, and `x^h = h^(-1) x h`.
- `λ_xy` sends `(x,p) -> (x,p-1)` for `p >= 2`, `(x,1) -> (y,1)`, and
  `(y,p) -> (y,p+1)`. `τ_x = ((x,1),(x,2))`.
- `P` is the finite presentation of `H_n` given there: Lee's generators and
  relators, the letters `λ_xy, τ_x` with their defining relations, and the set `Q` of
  all trivial words of length `<= 40` in `λ_xy^(±1), τ_x^(±1)`. Section 0 is written
  for every `n >= 3`. `P_3` denotes this presentation for `n = 3`.
- In this note, "relator" means one application of a relator of `P`, and `Area` means
  `Area_P`.

Relators of `Q` used below:

- `λ_xy λ_yx`;
- `λ_ac λ_cb λ_ba` (this says `λ_ac λ_cb = λ_ab`; check (3) of the script);
- `λ_ac ℓ λ_ca ψ(ℓ)^(-1)` for the four two-ray letters `ℓ`, with `ψ(ℓ)` from the table
  in §2. Each has length `<= 6`.

The two-ray letters are `λ_ab, λ_ba, τ_a, τ_b`. A *two-ray word* is a positive word in
them.

## 1. The doubling endomorphism with the route ray special

Define a bijection `β : Y × {0,1} -> Y` by

```text
β(c,p,e) = (c, 2p - 1 + e),        β(x,p,e) = (x, 2p - e)   for x ∈ {a,b},
```

and for `g ∈ H_3` let `Δ(g)` send `β(y,e)` to `β(y·g, e)`. This is the map of
`research/artifacts/zp-houghton-three-rays-2026-09-18.md` §B, with the special ray
called `c` instead of `a`.

**Lemma 1.** `Δ` is an injective homomorphism `H_3 -> H_3`. Exactly as permutations:

```text
Δ(λ_ac) = λ_ac^2,   Δ(λ_ca) = λ_ca^2,   Δ(λ_cb) = λ_cb^2,   Δ(λ_bc) = λ_bc^2,
Δ(λ_ab) = λ_ab^2 τ_b,                   Δ(λ_ba) = λ_ba^2 τ_a,
Δ(τ_a)  = ((a,1),(a,3)) ((a,2),(a,4)),  Δ(τ_b)  = ((b,1),(b,3)) ((b,2),(b,4)).
```

*Proof.* The first sentence and the first four identities are Lemma B.1 of the
three-ray note, verbatim up to renaming the rays `(a,b,c) -> (c,a,b)`. Lemma B.1 there
reads: "`Δ` is an injective homomorphism `H_3 -> H_3`, and the translation vector of
`Δ(g)` is twice that of `g`. Moreover, exactly as permutations:
`Δ(λ_ba) = λ_ba^2, Δ(λ_ca) = λ_ca^2, Δ(λ_ab) = λ_ab^2, Δ(λ_ac) = λ_ac^2`". Its proof
is the observation that `g -> g × id` is an injective homomorphism, transported by
`β`, and a direct check at the boundary tokens.

For `λ_ab`, both rays are ordinary, so `β(x,p,e) = (x,2p-e)`.

- Away from depth `<= 2`, `Δ(λ_ab)` shifts ray `a` down by two and ray `b` up by two.
- The boundary tokens are `(a,1) = β(a,1,1)`, which goes to `β(b,1,1) = (b,1)`, and
  `(a,2) = β(a,1,0)`, which goes to `β(b,1,0) = (b,2)`.
- The permutation `λ_ab^2 τ_b` sends `(a,1) -> (b,1) -> (b,2) -> (b,1)` and
  `(a,2) -> (a,1) -> (b,1) -> (b,2)`, with the same shifts elsewhere.

So the two agree. The case `λ_ba` is the inverse: `Δ(λ_ba) = τ_b λ_ba^2`, and
`τ_b λ_ba^2 = λ_ba^2 τ_a` because `λ_ba^2` carries `{(b,1),(b,2)}` onto
`{(a,2),(a,1)}` (this is a relator of `Q` listed in the pours note §0). For `τ_x`
with `x ∈ {a,b}`, the tokens `β(x,1,e), β(x,2,e)` are `(x,2),(x,4)` for `e = 0` and
`(x,1),(x,3)` for `e = 1`. ∎

So `Δ(λ_ab) = E_(a,b)(2)`, the order-preserving move of the top two points of `a`
onto the top of `b`. That is what makes the doubling below consistent.

**Word lift.** Fix, for each generator `s` of `P_3`, a word `Δ̂(s)` representing
`Δ(s)`, as follows. Extend `Δ̂` letterwise, and send formal inverses to inverse words.

- For the four letters `λ_xy` with `c ∈ {x,y}`: `Δ̂(λ_xy) = λ_xy λ_xy`.
- For the two-ray letters, use the column `Δ̂` of the table in §2. Each entry is a
  two-ray word.
- For the remaining generators of `P_3`, namely `τ_c` and Lee's `g_1, g_2, α`, use any
  fixed words representing their `Δ`-images.

**Lemma 2 (area transfer; Lemma B.2 of the three-ray note).** There is a constant
`K >= 1` with `Area(Δ̂(w)) <= K · Area(w)` for every null-homotopic word `w` of `P_3`.

*Proof* (verbatim from the three-ray note, which proves it for every choice of lifts):
"`Δ̂` sends free reductions to free reductions. It sends each relator `r` of `P` to a
word `Δ̂(r)`, which is trivial in `H_3` because `Δ` is a homomorphism. Put
`K = max_r Area(Δ̂(r))`. This is finite because `P` has finitely many relators. A van
Kampen derivation of `w` with `N` relator applications lifts to a derivation of
`Δ̂(w)` with `<= K N` of them." ∎

`K` depends on the lifts of Lee's generators and on Lee's relators. It is not
computed here, and it is the only inexplicit constant below.

## 2. The two-ray words N_m

Put `ψ(g) = λ_ac g λ_ca = g^(λ_ca)`. If `g` fixes ray `c` pointwise, then `ψ(g)` fixes
ray `c` and the point `(a,1)`, and acts on the rest as `g` transported along the shift
`(a,p) -> (a,p+1)`. This is the hidden-top shift `φ` of the three-ray note, with `a`
as its special ray. In particular `ψ` maps the two-ray subgroup into itself.

The table gives the lifts. Each entry is a shortest two-ray word representing the
element in its column header. The words were found by breadth-first search and are
checked by the script (§6, check (2)).

| `ℓ` | `Δ̂(ℓ)` (represents `Δ(ℓ)`) | `ψ(ℓ)` (represents `λ_ac ℓ λ_ca`) |
|---|---|---|
| `λ_ab` | `λ_ab λ_ab τ_b` | `τ_a λ_ab` |
| `λ_ba` | `λ_ba λ_ba τ_a` | `λ_ba τ_a` |
| `τ_a` | `λ_ab τ_a λ_ab τ_a τ_b λ_ba τ_a λ_ba` | `λ_ab τ_a λ_ba` |
| `τ_b` | `λ_ba τ_b λ_ba τ_a τ_b λ_ab τ_b λ_ab` | `τ_b` |

Two entries by hand:

- `ψ(τ_a) = τ_a^(λ_ba)` swaps `(a,1)·λ_ba = (a,2)` and `(a,2)·λ_ba = (a,3)`. That is
  `φ(τ_a)`.
- `ψ(λ_ab) = τ_a λ_ab`, which fixes `(a,1)` and sends `(a,2) -> (a,1) -> (b,1)`. That
  is `φ(λ_ab)`.

So `|Δ̂(ℓ)| <= 8` and `|ψ(ℓ)| <= 3` for every two-ray letter `ℓ`. Each word
`λ_ac ℓ λ_ca ψ(ℓ)^(-1)` is trivial of length `<= 6`, so it lies in `Q`.

**Definition.** Define two-ray words by

```text
N_1 = λ_ab,        N_(2m) = Δ̂(N_m),        N_(2m+1) = ψ(N_(2m)) · λ_ab,
```

where `ψ` is applied letterwise via the table.

**Lemma 3.** For every `m >= 1`:

- `N_m` is a two-ray word representing `E_(a,b)(m)`, that is, the element of
  `E^c_(a,b)(m) = λ_ac^m λ_cb^m`;
- `|N_m| <= 32^(⌊log_2 m⌋) <= m^5`.

*Proof.* Induction on `m`. The case `m = 1` is `λ_ac λ_cb = λ_ab`.

- *Even step.* `N_(2m) = Δ̂(N_m)` represents
  `Δ(E^c(m)) = Δ(λ_ac)^m Δ(λ_cb)^m = λ_ac^(2m) λ_cb^(2m)`, by Lemma 1.
- *Odd step.* `N_(2m+1)` represents `λ_ac E^c(2m) λ_ca · λ_ab`. Since
  `λ_ca λ_ab = λ_cb`, this is `λ_ac · λ_ac^(2m) λ_cb^(2m) · λ_cb = E^c(2m+1)`.

The table entries are two-ray words, so each `N_m` is one. For lengths:
`|N_(2m)| <= 8|N_m|`, and `|N_(2m+1)| <= 3|N_(2m)| + 1 <= 4|N_(2m)|`. So each binary
digit after the leading one multiplies the length by at most `32`. ∎

The script builds `N_m` for `m <= 40` and checks it against `λ_ac^m λ_cb^m` on every
point of depth `<= |N_m| + 3`. It also computes `|N_m|` exactly up to `m = 4096`.

- `|N_(2^j)|` grows by a factor of about `5.24` per doubling: `|N_1024| = 7 745 024`.
- The worst case for `2^11 <= m <= 2^12` is about `2.1 · 10^11`, so the true exponent
  is about `3.1`, well below the bound `5`.

Shorter words are not needed here.

## 3. Polynomial area in H_3

Let `A(m) = Area_(P_3)( E^c_(a,b)(m) · N_m^(-1) )`, where `E^c_(a,b)(m)` is the
literal word `λ_ac^m λ_cb^m`.

**Proposition 5.** `A(1) <= 1`, and for all `m >= 1`:

```text
A(2m)   <= K · A(m),
A(2m+1) <= A(2m) + 2|N_(2m)| + 1.
```

Hence `A(m) <= 4 (1 + log_2 m) · m^(5 + log_2 K)` for all `m >= 1`.

*Proof.* `E^c(1) N_1^(-1) = λ_ac λ_cb λ_ab^(-1)` is a relator of `Q`.

*Even step.* `Δ̂(λ_ac) = λ_ac λ_ac` and `Δ̂(λ_cb) = λ_cb λ_cb`, and `Δ̂` sends formal
inverses to inverse words. So, **letter for letter**,

```text
Δ̂( λ_ac^m λ_cb^m · N_m^(-1) ) = λ_ac^(2m) λ_cb^(2m) · Δ̂(N_m)^(-1) = E^c(2m) · N_(2m)^(-1).
```

Lemma 2 gives `A(2m) <= K A(m)`.

*Odd step.* Put `N = N_(2m) = ℓ_1 ⋯ ℓ_r`. The word
`E^c(2m+1) N_(2m+1)^(-1) = λ_ac · λ_ac^(2m) λ_cb^(2m) · λ_cb · λ_ab^(-1) ψ(N)^(-1)` is
freely equal to

```text
λ_ac ( E^c(2m) N^(-1) ) λ_ac^(-1)  ·  v,        v = λ_ac N λ_cb λ_ab^(-1) ψ(N)^(-1).
```

The first factor is a conjugate of a word of area `A(2m)`. For `v`:

1. After each `ℓ_i`, insert `λ_ca λ_ac`. That is `r` applications of the relator
   `λ_ca λ_ac`. The result is
   `(λ_ac ℓ_1 λ_ca)(λ_ac ℓ_2 λ_ca) ⋯ (λ_ac ℓ_r λ_ca) · λ_ac λ_cb λ_ab^(-1) ψ(N)^(-1)`.
2. Replace each `λ_ac ℓ_i λ_ca` by `ψ(ℓ_i)`. That is `r` relators of `Q`.
3. Delete `λ_ac λ_cb λ_ab^(-1)`, one relator. Then `ψ(N) ψ(N)^(-1)` cancels freely.

So `A(2m+1) <= A(2m) + 2r + 1`.

*Solving the recursion.* For `m = 2m' + 1 >= 3`, Lemma 3 gives
`2|N_(2m')| + 1 <= 2(2m')^5 + 1 <= 3m^5`. So for every `m >= 2`,
`A(m) <= K·A(⌊m/2⌋) + 3m^5`. Let `j = ⌊log_2 m⌋` and unroll `j` times, using `K >= 1`:

```text
A(m) <= K^j A(1) + 3 Σ_(i<j) K^i (m / 2^i)^5 <= K^j (1 + 3 j m^5).
```

Since `K^j <= m^(log_2 K)`, the bound follows. ∎

**Corollary.** The family `A_3` of Remark 3.1 of the four-ray note, taken with the
two-ray word `N_m` in place of the bubble sort `λ_ab^m ρ_b(m)`, is polynomial. The
original `A_3`, with the bubble sort, differs from `A(m)` by at most the area of the
two-ray relation `N_m · (λ_ab^m ρ_b(m))^(-1)`. That area is not bounded here, and it
is not needed: §4 uses `N_m` itself.

## 4. Four rays

Now `n = 4`, with the presentation `P` of `H_4`. As in the claim
`houghton-four-ray-pour-route-change-bounded-by-h3-dehn`,

```text
W_4(m) = max { Area_P( E^c_(a,b)(m) · E^d_(a,b)(m)^(-1) ) : {a,b,c,d} = {1,2,3,4} }.
```

For a ray `x`, let `S_x` be the pointwise stabilizer of ray `x`. Relabeling the other
three rays gives `S_x ≅ H_3`, and this sends `λ_yz ↦ λ_yz` and `τ_y ↦ τ_y` for
`y,z ≠ x`.

**Theorem 6.** There are constants `C_4` and `β` with `W_4(m) <= C_4 m^β` for all
`m >= 1`. One can take any `β > 5 + log_2 K_max`, where `K_max` is the largest of the
constants `K` of Lemma 2 over the 24 ordered choices of `(a,b,c)` in `{1,2,3,4}`.

*Proof.* Fix distinct `a,b,c,d`. Build `N_m` from the rays `(a,b,c)` as in §2. The
words `Δ̂(ℓ)` and `ψ(ℓ)` of the table involve only `a` and `b`. Their correctness does
not depend on which third ray is special:

- `Δ` restricted to the two-ray subgroup only involves the ordinary rays `a,b`;
- `λ_ac ℓ λ_ca` and `λ_ad ℓ λ_da` are both `φ(ℓ)`, by §2.

So the same recursion with `d` in place of `c` produces **literally the same word**
`N_m`. (Formally: the automorphism of `H_4` that swaps rays `c` and `d` fixes every
two-ray letter and carries the `c`-construction to the `d`-construction.) Check (6) of
the script confirms this in `H_4`: the same table words work with `d` special, and
`N_m = λ_ac^m λ_cb^m = λ_ad^m λ_db^m` for `m <= 40`.

The word `E^c(m) E^d(m)^(-1)` is freely equal to

```text
( E^c_(a,b)(m) · N_m^(-1) ) · ( E^d_(a,b)(m) · N_m^(-1) )^(-1).
```

The first factor has all its letters in `S_d`, and the second all its letters in
`S_c`. Apply Lemma 2 of the four-ray note to each factor, with one change: step 1
uses the diagram of Proposition 5 in the copy of `P_3` on the three rays involved,
instead of `δ_(H_3)`.

- Take `θ(ℓ) = ℓ` and `ι(ℓ) = ℓ` on the letters `λ_yz, τ_y`, so step 3 of that
  lemma is free.
- Step 2 multiplies by `K_1 = max_r Area_P(ι(r))` over the relators `r` of `P_3`.

This gives `W_4(m) <= 2 K_1 · max A(m)`, where the max is over the 24 labelings.
Proposition 5 bounds each `A(m)` by `4(1 + log_2 m) m^(5 + log_2 K)`. ∎

The four-ray note's Remark 3.1 makes the same point: "The proof of Theorem 3 uses
`δ_(H_3)` only on one explicit family ... `W_4(m) <= 2K(2m^3 + A_3(m))` with the
same argument, where Lemma 2 is applied to one fixed word instead of via `δ_(H_3)`."
Its argument uses only three things about `N`:

- `N` is a word in letters whose ray support avoids `c` and `d`;
- it represents the pour;
- it is the same word on both sides.

All three hold for `N_m`.

**Theorem 7.** `δ_(H_4)(x) ≼ x^(6+β)` with `β` as in Theorem 6. In particular the
Dehn function of `H_4` is polynomially bounded.

*Proof.* This is Theorem 4 of the four-ray note, with Theorem 6 in place of its
Theorem 3. Its proof, verbatim: "Run Theorem C of
`research/artifacts/zp-houghton-five-rays-2026-09-17.md` with `n = 4` and `β = 3d`,
using Theorem 3 in place of Proposition B. Theorem C uses `n >= 5` only through `W`:
its ray check shows that every step other than the bound on `W` needs at most four
distinct rays." It then re-checks each ray choice of the six-ray note for `n = 4` and
concludes: "The exponent bookkeeping of Theorem C assumes only `W ≼ m^β` with
`β >= 2` (all extra terms are `O(R^2)`) ... It gives `Area ≼ L^(6+β)`."

Here `W = W_4 ≼ m^β` with `β > 5 >= 2` by Theorem 6. Theorem C's other input, the
09-13 reduction `houghton-dehn-polynomially-equivalent-to-commutation-area`, holds for
every `n >= 3`. So `Area_P(w) ≼ L^(6+β)` for null-homotopic words of length `L`. The
transfer `Area_Lee <= K Area_P` of the pours note §0 finishes. ∎

## 5. Remarks

**Why the route ray must be the special ray.** The doubling with special ray `s`
satisfies `Δ(λ_xy) = λ_xy^2` exactly when exactly one of `x,y` is `s`. If `x` and `y`
are both ordinary, `Δ(λ_xy)` is `λ_xy^2` corrected by a transposition. A pour
`λ_ac^m λ_cb^m` uses the edges `ac` and `cb`, which share `c`. So `s = c` makes both
of them "bipartite". The three-ray note used `s = a` for its families `F_3` and `R_3`,
and there the pour's edge `cb` is not doubled exactly (its §B remark
`Δ(λ_bc) = λ_ba^2 λ_ac^2`).

In `H_4` with types `{a,b}` and `{c,d}` (a doubling with two special rays, defined the
same way), every letter of the skew square `λ_ac^m λ_cb^m λ_bd^m λ_da^m` joins opposite
types. So at `m = 2^j` that square is literally `Δ̂^j` of the length-4 relator, and
its area is `<= K^j`. The odd step is where the two-ray words are needed. This gives
an independent check of the mechanism at powers of two. It is not used above.

**What this does not give for H_3.** `H_3` has no route changes. The hole
`houghton-group-h3-has-polynomial-dehn-function` is the five families of
`houghton-h3-five-three-ray-families-have-polynomial-area`. Proposition 5 does reduce
the reroute family `R_3` to a two-ray commutation, as follows.

- Write `λ_ac^k = E^c(k) λ_bc^k` (free, with letter conversions `λ_cb λ_bc`), and
  commute `τ_a` past `λ_bc^k` (`2k` relators).
- Then `D^c_a(k) = λ_ac^k τ_a λ_ca^k` becomes `N_k τ_a N_k^(-1)` at cost
  `<= 2A(k) + O(k)`.
- `N_k` represents `λ_ab^k r_k`, where `r_k` reverses `(b,1..k)`. So
  `R_3(k) = Area(D^c_a(k) D^b_a(k)^(-1))` is at most `2A(k) + O(k)` plus the area of
  `[τ_a, u_k]`, where `u_k = λ_ba^k N_k` is a two-ray word of length `<= k^5 + k`
  representing `r_k`, a finitary permutation of ray `b` alone.

That last commutation is a far commutation: `τ_a` and `r_k` have disjoint supports,
but `u_k` passes through ray `a`. `R_3` is *not* among the families that Lemma C.1 of
the three-ray note excludes (C.1 lists `B_3, C_3, D_3, F_3`). Indeed `r_k` has a word
avoiding ray `a`, and Proposition 5 turns the rewrite into a single relation:

- Let `M_k` be the word of §2 built with the roles `(a,b,c)` replaced by `(c,b,a)`.
  It is a word in `λ_cb, λ_bc, τ_c, τ_b` representing `λ_ca^k λ_ab^k`, and
  `Area(λ_ca^k λ_ab^k M_k^(-1)) = A'(k)` is bounded by Proposition 5 for that labeling.
- Put `v_k = λ_bc^k M_k`. It represents `r_k`, and its ray support is `{b,c}`. So
  `[τ_a, v_k]` has area `<= |v_k| <= k^5 + k`, by letterwise commutation.
- Put `X_k = λ_ba^k λ_ac^k λ_cb^k`. Check (7) of the script confirms that `X_k`
  represents `r_k`, for `k < 25`. The general case holds because each of the three
  pours reverses the order of the `k` moved points.
- Up to `A(k)` and `O(k)` conversions, `u_k` equals `X_k`. Up to `A'(k)` and `O(k)`
  conversions, `v_k^(-1)` equals `(λ_bc^k λ_ca^k λ_ab^k)^(-1) = λ_ba^k λ_ac^k λ_cb^k = X_k`.
  So `Area(u_k v_k^(-1)) <= A(k) + A'(k) + O(k) + Area(X_k^2)`.

Altogether:

```text
R_3(k) <= poly(k) + 2 · Area( X_k^2 ),     X_k = λ_ba^k λ_ac^k λ_cb^k.
```

So the reroute family reduces to one "triangle rotation squared" relation of length
`6k`. It is left open here, for the following reason.

Doubling with `c` special sends `X_k` to `(λ_ba^2 τ_a)^k λ_ac^(2k) λ_cb^(2k)`. That
differs from `X_(2k)` by `k` conjugates of `τ_a` (pair swaps on ray `a`) that must be
collected. Moving them costs `R_3`-type relations at the same scale. The recursion
therefore does not contract, and no choice of special ray avoids this, since the
triangle `ba, ac, cb` uses all three edges. A polynomial bound on `Area(X_k^2)`
would give `R_3 ≼ poly`.

**Exponent.** Theorem 7 gives `δ_(H_4) ≼ x^(6+β)` with any
`β > 5 + log_2 K_max`. Making `K` explicit would need the `Δ̂`-images of Lee's relators
to be filled explicitly. The factor `m^5` can be lowered to about `m^3.2` by the true
growth of `|N_m|`, and possibly to `m` by better two-ray words. The quadratic question
for `H_4` is untouched.

## 6. Machine check

`experiments/houghton-three-ray-pours-2026-09-17/verify_pour_doubling.py` (runs in
about 10-15 minutes, exit code 0; the output of one run is saved as
`verify_pour_doubling.out` in the same directory) checks:

1. `Δ(λ) = λ^2` for `λ ∈ {λ_ac, λ_cb, λ_ca, λ_bc}`, computed from the formula for `β`;
2. the table of §2, found by breadth-first search over two-ray words and rechecked at
   larger depth;
3. `λ_ac λ_cb = λ_ab`;
4. `N_m = E^c_(a,b)(m)` as elements, and `N_m` two-ray, for `1 <= m <= 40`, plus exact
   lengths `|N_m|` up to `m = 4096`;
5. `Δ(uv) = Δ(u)Δ(v)` on 200 random pairs of words;
6. in `H_4`, that the same table works with `d` special, and that
   `N_m = λ_ac^m λ_cb^m = λ_ad^m λ_db^m` for `m <= 40`;
7. `λ_ba^k λ_ac^k λ_cb^k = r_k` (the reversal of `(b,1..k)`) for `1 <= k < 25`.

All comparisons are made on every point of depth `<= R` of every ray, with `R` at least
the length of the longer word plus 3. That is enough to decide equality in `H_n`. The
area recursion of Proposition 5 is not machine-checked; its steps are the explicit
rewrites listed in its proof.
