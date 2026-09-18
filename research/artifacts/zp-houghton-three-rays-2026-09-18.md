# Houghton H_3: the Dehn function reduces to five explicit three-ray relation families, and a doubling endomorphism halves two of them at even scales

Lane swarm-0917-w10-w10-z-follow, 2026-09-18. Zaremsky Problem 1.24, the one remaining
hole `houghton-group-h3-has-polynomial-dehn-function`. Status: Theorem A is a complete
proof (it reruns §§4–6 of the six-ray note with black boxes). The rest is §B (the
doubling mechanism, with complete proofs of Lemmas B.1–B.4) and §C (where the doubling
recursion stops). Unreviewed.

Conventions are those of `research/artifacts/zp-houghton-pours-2026-09-17.md` (the
*six-ray note*), §0, with `n = 3`:

- permutations act on the right, and `x^h = h^(-1) x h`;
- `λ_xy` pulls ray `x` in and pushes ray `y` out;
- `τ_x = ((x,1),(x,2))`, and `D^u_x(k) = λ_xu^k τ_x λ_ux^k` represents
  `((x,k+1),(x,k+2))`;
- `P` is the finite presentation of §0, and `Area = Area_P`.

The three rays are `{1,2,3}`. A route function `c` is fixed, for example
`c(1) = 2`, `c(2) = 3`, `c(3) = 1`, and `Ed(e)` is the edge word of §4 of the six-ray
note for this `c`.

## A. The reduction for three rays

### A.1 The five families

For `k, i, j >= 0` define the following null-homotopic words and their areas. Each is
maximised over all labelings of the rays with the stated distinctness.

| family | word | length |
|---|---|---|
| `F_3(k)` | `[τ_x, D^(c(x))_x(k)]` | `4k + 4` |
| `R_3(k)` | `D^u_x(k) · D^v_x(k)^(-1)`, with `{x,u,v} = {1,2,3}` | `4k + 2` |
| `B_3(i,j)` | `[Ed(t_x(i)), Ed(t_y(j))]`, with `x != y` | `4(i+j) - 4` |
| `C_3(j)` | `[Ed(σ_{x,y}), Ed(t_z(j))]`, with `σ_{x,y}` and `t_z(j)` vertex-disjoint | `4j + 4` |
| `D_3(j)` | `λ_wz · Ed(t_x(j)) · λ_zw · Ed(t_x(j))^(-1)`, with `{x,z,w} = {1,2,3}` | `4j` |

Put

```text
Φ(k) = max over i, j <= k of { F_3(i), R_3(i), B_3(i,j), C_3(j), D_3(j) }.
```

`C_3` covers cases (iii) and (iv) of Proposition 4.1: `z ∉ {x,y}`, or `z = x` with
`j >= 2`. In `D_3` the ray `x` is the one not moved by `λ_zw`, so `c(x) ∈ {z,w}`, and
the letter `λ_zw` and the word `Ed(t_x(j))` share a ray.

**Theorem A.** There is a constant `C` such that for all `L >= 1`

```text
Φ(L) <= δ_(H_3)(C L)        and        δ_(H_3)(L) <= C L^6 ( Φ(L + C) + L ).
```

In particular `δ_(H_3)` is polynomially bounded if and only if `Φ` is. If
`Φ(k) ≼ k^d` with `d >= 1`, then `δ_(H_3)(x) ≼ x^(6+d)`.

The first inequality holds because every word in the table is null-homotopic and has
length `<= C k`. The second is proved in A.2–A.4.

### A.2 Edge relations with three rays

Let `E(R)` be the largest area of the edge relations (E1)–(E4) of §4 of the six-ray
note, over edges of depth `<= R`. Its proof of Proposition 4.1 splits these relations
into cases. For `n = 3` the cases give the following.

- (E1) and (E4). These cost `<= 2R + 1` and `O(1)` respectively. The proof does not
  use a spare ray.
- (E3). This costs `O(R)`. The proof conjugates by `λ_(x c(x))^(j-1)` and does letter
  conversions, and again uses no spare ray.
- (E2)(i), two ray edges on the same ray. Conjugating by `λ_(x c)^(i-1)` sends the
  relation freely to `w_(j-i)` for the pair `(x, c(x))`, so it costs `<= F_3(j-i) + O(R)`.
- (E2)(ii), two ray edges on different rays. This is `B_3(i,j)` by definition. The
  six-ray proof rerouted here to two distinct fresh rays `c', d'`, which needs `n >= 4`;
  that step is dropped.
- (E2)(iii) and (iv), a top edge and a ray edge. These are `C_3(j)` by definition.
- (E2)(v). This costs `O(1)`.

So `E(R) <= Φ(R) + C R`.

### A.3 Letters on edges with three rays

Let `Λ(R)` be the largest area of `s^(-1) Ed(e) s · Ed(e')^(-1)` over letters
`s = λ_zw`, edges `e` of depth `<= R` and `e' = e^s`, in the first alternative of
Lemma 4.2 of the six-ray note. (The second alternative costs `<= 2` for every `n`.) The
case analysis of Lemma 4.2 gives, with `{x,z,w} = {1,2,3}`:

- `e = t_x(j)`. Then `e' = e`, and after one letter conversion the relation is the word
  of `D_3(j)`. The six-ray proof rerouted to a fourth ray `c' ∉ {x,z,w}`; that step is
  dropped.
- `e = t_z(j)`, `j >= 2`. Then `e' = t_z(j-1)`. If `c(z) = w`, the relation is free
  after `O(1)` letter conversions, because
  `λ_wz λ_zw^(j-1) τ_z λ_wz^(j-1) λ_zw ≡ D^w_z(j-2)`. If `c(z) = x`, reroute to route
  `w` (cost `R_3(j-1)`), use the free identity, and reroute back (cost `R_3(j-2)`).
- `e = t_w(j)`. Then `e' = t_w(j+1)`, and the same argument with route `z` costs
  `<= R_3(j-1) + R_3(j)`.
- `e = t_z(1)` or `e` a top edge. The relation has length `<= 40`, so it costs `O(1)`.

So `Λ(R) <= 2Φ(R+1) + 4R + 4`.

### A.4 Path words and the Dehn function

Let `Ē(R) = max_(R' <= R) E(R')` and `Λ̄` likewise. By A.2 and A.3,
`Ē(R) <= Φ(R) + CR` and `Λ̄(R) <= 2Φ(R+1) + 4R + 4`, because `Φ` is monotone.

**§5 of the six-ray note for `n = 3`.** The proofs of Lemmas 5.1, 5.2, 5.4 and 5.5
and of Corollary 5.3 use only three things: the edge relations (E1)–(E4) at cost
`Ē`, the structure of `Γ` ((S1), (S2)), and the order on `Y`. None of them picks a
ray. Corollary 5.3 applies Lemma 5.2 `q - 1` times, where `q <= n - 1 = 2`. So for
`n = 3` they hold as stated, with `Ē` the three-ray hull above. Lemma 5.5 costs
`<= C R^2 Ē(R+1)`.

Lemma 5.6 goes through the same way. In the case `s = τ_z` it uses Lemma 5.5. In the
case `s = λ_zw` it applies Lemma 4.2 at each of the `2r - 1` edge positions. The
first alternative costs `<= Λ̄(R)`, and the second costs `<= 2`. It then uses
Lemma 5.4 and Corollary 5.3. The one choice there is `m = (w,1)`, with `z ∉ {w,y}`,
and for `n = 3` it is forced: `y` is the third ray. So Lemma 5.6 costs

```text
Γ(R) := C ( R Λ̄(R) + R^2 Ē(R+2) ) <= C' R^2 ( Φ(R+2) + R ).
```

**Proof of the second inequality of Theorem A.** Rerun the proof of Theorem 6.1 of
the six-ray note, with `R = L + C_1 + 2`.

- Steps 1 and 2 (sort, translate) use Lemma 3 and Lemma 1 of the 09-13 note and the
  defining relations of `P`. All of these are valid for every `n >= 3`. They cost
  `O(L^3)`.
- Step 3 (normalize) costs `<= M ℓ Γ(R) <= C L^3 · R^2 (Φ(R+2) + R)`. This is
  `≼ L^5 Φ(L + C) + L^6`.
- Step 4 (eliminate) runs Step 2 of §5 of the 09-13 note. That step is valid for
  every `n`: it is the symmetric-group word problem on `B`, with `|B| = 3R`. Each move
  costs `<= C R^3 Ē(R+1) + 4R Ē(R)`, and there are `<= 3R · M` moves. The total is
  `≼ L^6 (Φ(L + C) + L)`.

Adding up, `Area_P(w) <= C L^6 ( Φ(L+C) + L )`, and `Area_Lee <= K Area_P`. ∎

**Remark A.5.** For `n >= 6` the six-ray note bounds all five families by
`≼ k^2 log k`. That uses pours through two free auxiliary rays (Lemma 1.2), and this
is the only use of `n >= 6`. For `n = 3` no family has a known polynomial bound.
Together, the two inequalities say that `Φ` and `δ_(H_3)` are polynomially
equivalent. So the five families are the whole obstruction: a proof for `H_3` must
bound each of them, and bounding all five suffices.

## B. A doubling endomorphism and lamp halving

In this section the rays are labeled `a, b, c`. By symmetry of the families, it is
enough to treat `F_3` with `x = a` and `c(a) = b`, and `R_3` with `x = a`. Every
construction below depends on the choice of the special ray `a`.

### The doubling endomorphism

Define a bijection `β : Y × {0,1} -> Y` by

```text
β(a,p,e) = (a, 2p - 1 + e),        β(x,p,e) = (x, 2p - e)   for x ∈ {b,c}.
```

For `g ∈ H_3`, put `Δ(g) = β^(-1) (g × id) β`. In words, `Δ(g)` sends `β(y,e)` to
`β(y·g, e)`.

**Lemma B.1.** `Δ` is an injective homomorphism `H_3 -> H_3`, and the translation
vector of `Δ(g)` is twice that of `g`. Moreover, exactly as permutations:

```text
Δ(λ_ba) = λ_ba^2,   Δ(λ_ca) = λ_ca^2,   Δ(λ_ab) = λ_ab^2,   Δ(λ_ac) = λ_ac^2,
Δ(τ_a) = ((a,1),(a,3)) ((a,2),(a,4)).
```

*Proof.* `g -> g × id` is an injective homomorphism into the permutations of
`Y × {0,1}`, and conjugation by `β` transports it. Suppose `g` agrees with the
translation `(x,p) -> (x,p+t_x)` outside a finite set. Since `β` maps `(x,p,e)` to
depth `2p - 1` or `2p`, `Δ(g)` agrees with `(x,q) -> (x,q+2t_x)` outside a finite
set. So `Δ(g) ∈ H_3`.

For `λ_ba`, depths on ray `b` go down by one and depths on ray `a` go up by one.
Under `β` these become shifts by two. The tokens at the boundary are
`β(b,1,1) = (b,1)` and `β(b,1,0) = (b,2)`. They go to `β(a,1,1) = (a,2)` and
`β(a,1,0) = (a,1)` respectively. The permutation `λ_ba^2` sends
`(b,1) -> (a,1) -> (a,2)` and `(b,2) -> (b,1) -> (a,1)`. Both permutations shift
the rest of ray `b` down by two and ray `a` up by two, and fix ray `c`, so they agree.

The case `λ_ca` is the same with `c` in place of `b`, and the other two are the
inverses. For `τ_a`, the pair `(a,1,e), (a,2,e)` is `(a,1), (a,3)` for `e = 0` and
`(a,2), (a,4)` for `e = 1`. ∎

Rays `b` and `c` are oriented the same way, so `Δ(λ_bc) = λ_ba^2 λ_ac^2`, which
is not `λ_bc^2`. This is not needed below.

**Word lift.** For each generator `s` of `P`, fix a word `Δ̂(s)` representing
`Δ(s)`. When `a ∈ {x,y}`, take `Δ̂(λ_xy) = λ_xy λ_xy`. Extend `Δ̂` letterwise to
words, and send each formal inverse to the inverse word.

**Lemma B.2 (area transfer).** There is a constant `K` such that
`Area(Δ̂(w)) <= K · Area(w)` for every null-homotopic word `w` in the generators
of `P`.

*Proof.* `Δ̂` sends free reductions to free reductions. It sends each relator `r` of
`P` to a word `Δ̂(r)`, which is trivial in `H_3` because `Δ` is a homomorphism. Put
`K = max_r Area(Δ̂(r))`. This is finite because `P` has finitely many relators. A van
Kampen derivation of `w` with `N` relator applications lifts to a derivation of
`Δ̂(w)` with `<= K N` of them. ∎

In particular, if the words `u, v` are equal in `H_3`, then replacing `Δ̂(u)` by
`Δ̂(v)` costs `<= K · Area(u v^(-1))`.

**The flip.** Put `f = τ_a = ((a,1),(a,2))`, the swap of `β(a,1,0)` and `β(a,1,1)`. Suppose `g`
fixes `(a,1)`. Then `Δ(g)` fixes `(a,1)` and `(a,2)`, so `Δ(g)` commutes with `f`.
By Lemma B.1 and the choice `Δ̂(λ_ba) = λ_ba λ_ba`, the word `D^b_a(2k)` is literally

```text
D^b_a(2k) = λ_ab^(2k) τ_a λ_ba^(2k) = Δ̂(λ_ab^k) · f · Δ̂(λ_ba^k),
```

and likewise `D^c_a(2k) = Δ̂(λ_ac^k) f Δ̂(λ_ca^k)`.

### The hidden-top shift

Let `ι : Y -> Y ∖ {(a,1)}` be the bijection `(a,p) -> (a,p+1)` that is the identity
on rays `b, c`. For `g ∈ H_3` let `φ(g)` act as `ι^(-1) g ι` on `Y ∖ {(a,1)}` and fix
`(a,1)`. Then `φ` is an injective endomorphism of `H_3`. It preserves translation
vectors, and `φ(g)` fixes `(a,1)` for every `g`.

**Lemma B.3.** Put

```text
φ̂(λ_ba) = λ_ac λ_ba λ_ca,   φ̂(λ_ab) = λ_ac λ_ab λ_ca,
φ̂(λ_ca) = λ_ab λ_ca λ_ba,   φ̂(λ_ac) = λ_ab λ_ac λ_ba.
```

Then `φ̂(s)` represents `φ(s)` for these four letters. Also `φ(g) = g` for every `g`
that fixes ray `a` pointwise. For each of the four letters `s`, the word
`[τ_a, Δ̂(φ̂(s))]` has length `14`, is trivial, and so lies in `Q`.

*Proof.* Take `s = λ_ba`, with `ψ = λ_ac λ_ba λ_ca`.

- The point `(a,1)` goes `-> (c,1) -> (c,1) -> (a,1)`.
- For `p >= 2`, `(a,p)` goes `-> (a,p-1) -> (a,p) -> (a,p+1)`, which is
  `ι λ_ba ι^(-1)` on `ι(Y) ∩ ray a`.
- The point `(b,1)` goes `-> (b,1) -> (a,1) -> (a,2) = ι(a,1)`.
- For `p >= 2`, `(b,p)` goes to `(b,p-1)`.
- Ray `c` is fixed: `(c,p) -> (c,p+1) -> (c,p+1) -> (c,p)`.

So `ψ = φ(λ_ba)`.

For `λ_ca` the same check applies with `b` and `c` swapped: `(a,1) -> (b,1) -> (b,1) -> (a,1)`,
and `(c,1) -> (c,1) -> (a,1) -> (a,2)`. The other two letters are the inverses.

If `g` fixes ray `a` pointwise, then `ι^(-1) g ι` is `g` on `Y ∖ {(a,1)}`, so
`φ(g) = g`. Finally, `φ(s)` fixes `(a,1)`, so `Δ(φ(s))` commutes with `f`. The word
`Δ̂(φ̂(s))` has length 6. ∎

### Lamp halving

Let `h_k = λ_ba^k`, `h'_k = λ_ba φ̂(λ_ba)^(k-1)`, and
`u_k = h_k h'^(-1)_k = λ_ba^k φ̂(λ_ab)^(k-1) λ_ab`, a word of length `4k - 2`.
Let `s_k = λ_ba^k λ_ac^k`, a word of length `2k`.

**Lemma B.4.**

1. `u_k` represents the `k`-cycle `c_k : (b,j) -> (b,j+1)` for `j < k`,
   `(b,k) -> (b,1)`. It fixes ray `a` pointwise, so `u_k φ̂(u_k)^(-1)` is
   null-homotopic.
2. `s_k` fixes ray `a` pointwise, so `s_k φ̂(s_k)^(-1)` is null-homotopic.
3. There is a constant `C` such that for all `k >= 1`

```text
F_3(2k) <= 4K · Area( u_k φ̂(u_k)^(-1) ) + C k,
R_3(2k) <= 2K · Area( s_k φ̂(s_k)^(-1) ) + C k.
```

The two relators have lengths `16k - 8` and `8k`. They are statements at scale `k`.

*Proof.* (1) Compute `(b,j)·h_k` and `(b,j)·h'_k`.

- `h_k` sends `(b,j)` to `(a, k-j+1)`.
- `h'_k` sends `(b,1)` to `(a,1)`, since `φ(λ_ba)` fixes `(a,1)`.
- For `2 <= j <= k`, `λ_ba` sends `(b,j)` to `(b,j-1)`. Then `j - 2` factors of
  `φ(λ_ba)` bring it to `(b,1)`, one more sends it to `(a,2)`, and the remaining
  `k - j` factors push it to `(a, k-j+2)`.

On the rest of `Y`, `h_k` and `h'_k` agree: both shift ray `a` up by `k` and the
part of ray `b` beyond depth `k` down by `k`, and both fix ray `c`. Hence
`c_k = h_k h'^(-1)_k` sends `(b,j) -> (b,j+1)` for `j < k` and `(b,k) -> (b,1)`, and
fixes everything else. By Lemma B.3, `φ(c_k) = c_k`, and `φ̂(u_k)` represents
`φ(c_k)`.

(2) `λ_ba^k` sends `(a,p)` to `(a,p+k)`, and `λ_ac^k` sends it back, so `s_k` fixes
ray `a` pointwise. Use Lemma B.3.

(3), `F_3`. The word is `[f, D]` with `D = D^b_a(2k) = Δ̂(λ_ab^k) f Δ̂(h_k)`.

1. After `O(k)` inverse-letter conversions, `D ≡ Δ̂(h_k)^(-1) f Δ̂(h_k)`.
   Since `h_k ≡ u_k h'_k` freely, `Δ̂(h_k) ≡ Δ̂(u_k) Δ̂(h'_k)` freely.
2. Replace each of the four occurrences of `Δ̂(u_k)^(±1)` in `[f, D]` by
   `Δ̂(φ̂(u_k))^(±1)`. By Lemma B.2 this costs `<= 4K · Area(u_k φ̂(u_k)^(-1))`.
3. Move `f` (and `f^(-1)`, after one conversion) through `Δ̂(φ̂(u_k))`, block by
   block. That is `4k - 2` relators of Lemma B.3. Then cancel freely. Now
   `D ≡ Δ̂(h'_k)^(-1) f Δ̂(h'_k) = V^(-1) D' V`, where
   `V = Δ̂(φ̂(λ_ba))^(k-1)` and `D' = λ_ab^2 τ_a λ_ba^2`.
4. The word is `f^(-1) V^(-1) D'^(-1) V f V^(-1) D' V`, up to conversions. Move
   `f^(±1)` through `V^(±1)`, which takes `2(k-1)` relators of Lemma B.3. This gives
   `V^(-1) [f, D'] V`.
5. `D'` represents `((a,3),(a,4))`, so `[τ_a, λ_ab^2 τ_a λ_ba^2]` is a trivial word
   of length 12 and lies in `Q`. One relator, then free cancellation.

(3), `R_3`. After `O(k)` conversions and a cyclic permutation, the word
`D^b_a(2k) D^c_a(2k)^(-1)` becomes `f Δ̂(s_k) f^(-1) Δ̂(s_k)^(-1)`.

1. Replace both `Δ̂(s_k)^(±1)` by `Δ̂(φ̂(s_k))^(±1)`. This costs
   `<= 2K · Area(s_k φ̂(s_k)^(-1))`.
2. Move `f` through the `2k` blocks, one relator each, and cancel `f f^(-1)`. ∎

**What Lemma B.4 buys.** A relation at scale `2k` becomes a relation at scale `k`.
It does so exactly, with a multiplicative constant `4K` and a linear error. But the
new relation is not a member of the five families, and its length is not halved
(`16k - 8` against `8k + 4` for `F_3`, and `8k` against `8k + 2` for `R_3`). §C
explains why this does not close the recursion.

## C. Where it stops, and one class of approaches that cannot work

### C.1 The recursion does not close

A polynomial bound by halving needs an inequality of the form
`Φ(2k) <= A · Φ(k + C) + poly(k)` with `A` a constant. Then `Φ(k) ≼ k^(log_2 A)`, up
to the polynomial term. Lemma B.4 gives the first factor `4K`. What is missing is a
bound on `Area(u_k φ̂(u_k)^(-1))` and `Area(s_k φ̂(s_k)^(-1))` by `A' · Φ(k + C)`.
The only available bound is Theorem A applied to a word of length `<= 16k`:

```text
Area(u_k φ̂(u_k)^(-1)) <= δ(16k) <= C (16k)^6 ( Φ(16k + C) + 16k ).
```

This increases the scale from `2k` to `16k`, so the recursion runs the wrong way.
Theorem A loses the scale in two places. First, the sorting step (Lemma 3 of the
09-13 note) creates conjugators whose depth is bounded only by the total length.
Second, the canonical words route every transposition through the top vertices.
Both relators in Lemma B.4 have all their letters at depth `<= k + 1`, but no step of
Theorem A preserves depth.

Two things would be enough. The first is a *depth-local* version of Theorem A: a
null-homotopic word of length `ℓ`, all of whose prefixes have depth `<= R`, has area
`<= poly(ℓ) · (Φ(R + C) + ℓ)`. With it, Lemma B.4 would give
`Φ_(F,R)(2k) <= poly(k) · Φ(k + C)`. That alone yields only `k^(O(log k))`
(quasi-polynomial), because the factor is not constant. It would still improve on
Lee's exponential bound. The second is that the same halving would also have to work
for `B_3`, `C_3`, `D_3`. Neither is proved here.

### C.2 The parity gap

`Δ` sends every finitary permutation to an even one, since `g × id` has two copies of
each cycle of `g`. The image of `Δ` lies in the pair-preserving subgroup: the pairs
are `{(x,2p-1),(x,2p)}` on every ray. The transposition `D^b_a(2k+1)`, which is
`((a,2k+2),(a,2k+3))`, straddles two pairs. So it is not `f` conjugated by any
element of `Δ(H_3)`, and Lemma B.4 cannot reach odd scales. Every family word
contains a `τ` letter, which is odd. So the doubling is only usable through lamps as
in Lemma B.4, never as a pure image `Δ̂(w)`.

The shifted pairing `β'(a,p,e) = (a, 2p + e)`, with `(a,1)` fixed, gives the
endomorphism `g -> φ(Δ(g))`. Its pairs on ray `a` are `{(a,2p),(a,2p+1)}`, so
`D^b_a(2k+1)` is a lamp for it. But `τ_a` is then not a lamp, and
`λ_ab^(2k)` is not literally the lift of `λ_ab^k` (the lift is
`φ̂(λ_ab)^(2k)`). So odd scales need a further conversion at scale `k`. It is not
written out here.

### C.3 Ray supports: the letterwise-disjointness approach dies for three rays

The *ray support* of a word is the union of the ray supports of its letters: `{x,y}`
for `λ_xy`, and `{x}` for `τ_x`. Two words with disjoint ray supports commute
letter by letter, with relators `[s,t] ∈ Q`. Their commutator therefore has area
`<= |w_1| |w_2|`. This is how the six-ray note proves (E2)(ii) and Lemma 4.2 case 1.
It first reroutes both edge words to fresh routes with disjoint ray supports
(Prop 4.1, using rays `c', d'`) and then commutes letterwise.

**Lemma C.1.** Let `w` be a word in the letters `λ_xy^(±1)`, `τ_x^(±1)` of `H_3`.

- If `w` moves a point `(x,p)` with `p >= 3`, then its ray support contains `x` and
  some other ray `u`.
- If `w` moves `(x,1)` to `(y,1)` with `y != x`, then its ray support contains
  `{x,y}`.

Consequently, for every member of `B_3(i,j)` with `i, j >= 2`, of `C_3(j)` with
`j >= 2`, of `D_3(j)` with `j >= 2`, and of `F_3(k)` with `k >= 1`, the two
commuting parts can never be rewritten into words with disjoint ray supports.

*Proof.* A letter whose ray support does not contain `x` fixes ray `x` pointwise, and
`τ_x` fixes every `(x,p)` with `p >= 3`. So if no letter is `λ_xu^(±1)` or
`λ_ux^(±1)`, then `w` fixes `(x,p)` for `p >= 3`. The second claim is similar: some
letter must carry a point of ray `x` off the ray, and some letter must carry a point
onto ray `y`.

Now the consequence for `B_3`, `C_3` and `D_3`. Each commuting part is one of three
things: it represents a transposition moving a point of depth `>= 3` (`t_x(j)` with
`j >= 2`), or it joins two top vertices (`σ_{x,y}`), or it is the letter `λ_zw`. In
every case, every word representing it has ray support of size `>= 2`. Two subsets
of `{1,2,3}` of size `>= 2` always intersect.

For `F_3(k)`, the parts are `τ_x` and `D(k) = ((x,k+1),(x,k+2))`. Every word for
`τ_x` moves `(x,1)` and so involves ray `x`. Every word for `D(k)` moves a point of
depth `>= 3` on ray `x`. So both supports contain `x`. ∎

So every derivation in the class "reroute to disjoint ray supports, then commute
letter by letter" dies at the commute step for `n = 3`, whatever the rerouting. The
invariant is the ray support. With four rays, the disjoint pair `{x,u}, {y,v}` exists,
and this is exactly where §4 of the six-ray note uses a fourth ray. Any proof for
`H_3` must use relators whose two sides share a ray, such as the hidden-top relators
of Lemma B.3 or the lamp relators of Lemma B.4.

### C.4 What is left

`houghton-group-h3-has-polynomial-dehn-function` is equivalent to a polynomial bound
on the five explicit families of A.1 (Theorem A). The doubling endomorphism reduces
the even-scale `F_3` and `R_3` to the two hidden-top relators `u_k φ̂(u_k)^(-1)` and
`s_k φ̂(s_k)^(-1)`, at constant factor (Lemma B.4). The most promising next step is
the depth-local version of Theorem A (C.1). The second target is a halving lemma for
`B_3`, `C_3`, `D_3`. The Lemma B.4 argument does not apply directly, because their
parts are not lamps of a single pairing.

