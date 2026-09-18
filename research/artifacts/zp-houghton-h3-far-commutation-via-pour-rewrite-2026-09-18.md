# H_3: far commutation is bounded by the two-ray rewrite of one pour

Lane swarm-0917-w12-w12-z-break, 2026-09-18. Zaremsky Problem 1.24. Status: complete
proof, unreviewed. The element identities and free-word steps are machine-checked
(`experiments/houghton-h3-2026-09-17/verify_far_commutation_via_pour_rewrite.py`).

Notation as in `research/artifacts/zp-houghton-pours-2026-09-17.md` (the "six-ray
note") §0, with `n = 3`.

- `P` is the finite presentation of `H_3` built by the six-ray note's recipe. The
  recipe uses only Lee's Theorem C and Lemma 3 of
  `research/artifacts/zp-houghton-dehn-2026-09-13-part1.md`, both valid for all
  `n >= 3`.
- `Q ⊂ P` is the set of all trivial words of length `<= 40` in `λ_xy^(±1), τ_x^(±1)`.
- `D^b_a(k) = λ_ab^k τ_a λ_ba^k`, which is the transposition `((a,k+1),(a,k+2))`.
- `E^z_(x,y)(m) = λ_xz^m λ_zy^m`.
- `N_(x,y)(m) = λ_xy^m ρ_y(m)` is the two-ray word of Lemma 1 of
  `research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md`. It has length
  `<= m^3`, uses only the letters `λ_xy, λ_yx, τ_y`, and equals `E^z_(x,y)(m)` as an
  element.

Define

```text
A_3(m) = max over distinct rays x,y,z of H_3 of Area_P( E^z_(x,y)(m) · N_(x,y)(m)^(-1) ),
F_3(k) = max over distinct rays a,b of Area_P( w_k ),   w_k = τ_a D^b_a(k) τ_a^(-1) D^b_a(k)^(-1).
```

For `a = 1, b = 2` the word `w_k` is Lee's `[α, α^(g_1^(-k))]` after `O(k)`
substitutions (six-ray note, Theorem 3.1). `A_3` is the quantity of Remark 3.1 of the
four-ray note, maximized over labelings.

## Theorem

For all `k >= 3`,

```text
F_3(k) <= 4 A_3(k-2) + 2k^3 + 14k.
```

So `A_3(m) ≼ m^D` gives `F_3(k) ≼ k^(max(D,3))`. Combined with Remark 3.1 of the
four-ray note (`W_4(m) <= 2K(2m^3 + A_3(m))`, hence `δ_(H_4) ≼ x^(6+D)`), this means
one polynomial bound on the single explicit family `A_3` gives both a polynomial
Dehn function for `H_4` and polynomial far commutation in `H_3`.

## Proof

Fix distinct rays `a,b,c` of `H_3` and put `j = k-2 >= 1`.

**Step 1 (push the far transposition to the top of ray b).** Put `h = λ_ab^k`. Areas
are invariant under conjugation, so `Area(w_k) = Area(h^(-1) w_k h)`. In
`h^(-1) D^b_a(k) h = λ_ab^(-k) λ_ab^k τ_a λ_ba^k λ_ab^k`, convert `λ_ba^k` to
`λ_ab^(-k)` (`k` relators `λ_xy λ_yx`). The result is freely `τ_a`. Do the same for
`h^(-1) D^b_a(k)^(-1) h` (another `k` relators). The word becomes

```text
T τ_a T^(-1) τ_a^(-1),      T = λ_ab^(-k) τ_a λ_ab^k.
```

Next, replace `τ_a` inside `T` and inside `T^(-1)` by `λ_ab^2 τ_b λ_ba^2`, which
costs one relator of `Q` each (six-ray note §0). Then convert `λ_ba^2` to `λ_ab^(-2)`
and `λ_ab^(-(k-2))` to `λ_ba^(k-2)`, `k` relators for each of `T` and `T^(-1)`. So
`T` becomes, freely, `λ_ba^j τ_b λ_ab^j = D^a_b(j)`. Hence

```text
Area(w_k) <= Area([D^a_b(j), τ_a]) + 4k + 2.
```

As elements, `T` is `((b,k-1),(b,k))`, which equals `D^a_b(k-2)`. This is check (2)
of the script.

**Step 2 (reroute through the third ray).** `D^a_b(j)` and `D^c_b(j) = λ_bc^j τ_b λ_cb^j`
are the same element `((b,j+1),(b,j+2))`. Put
`R(j) = Area(D^a_b(j) D^c_b(j)^(-1))`. Replacing both occurrences costs `2R(j)`.
Every letter of `D^c_b(j)^(±1)` has ray support in `{b,c}`, disjoint from `{a}`. So
`τ_a` passes `D^c_b(j)` with `2j+1` commutation relators of `Q`, and the rest cancels
freely. Hence

```text
Area(w_k) <= 2R(j) + 6k.
```

**Step 3 (a reroute is a commutation with a pour).** Converting the `2j+1` letters of
the formal inverse `D^c_b(j)^(-1)` gives `λ_bc^j τ_b λ_cb^j`. So the word
`D^a_b(j) D^c_b(j)^(-1)` becomes

```text
λ_ba^j τ_b λ_ab^j λ_bc^j τ_b λ_cb^j,
```

whose cyclic conjugate is `τ_b V τ_b V'`, where

- `V = λ_ab^j λ_bc^j = E^b_(a,c)(j)`,
- `V' = λ_cb^j λ_ba^j`, which becomes the formal inverse `V^(-1)` after `2j`
  conversions.

This is Lemma 2.1 of the six-ray note with `x = b`, `u = a`, `u' = c`, `X = τ_b`. The
six-ray note needs an auxiliary ray `e` at this point. We do not.

**Step 4 (replace the pour by its two-ray word).** Replace `V` by `N = N_(a,c)(j)` and
`V^(-1)` by `N^(-1)`, at cost `<= 2A_3(j)`. Convert the second `τ_b` to `τ_b^(-1)`
(one relator). Every letter of `N` is `λ_ac`, `λ_ca` or `τ_c`, with ray support in
`{a,c}`, disjoint from `{b}`. So `τ_b^(-1)` passes `N` with `|N| <= j^3` commutation
relators, and `τ_b N τ_b^(-1) N^(-1)` becomes freely trivial. Hence

```text
R(j) <= 2A_3(j) + j^3 + 4j + 2.
```

**Total.**

```text
Area(w_k) <= 4A_3(j) + 2j^3 + 8j + 4 + 6k <= 4A_3(k-2) + 2k^3 + 14k.
```

Maximizing over `(a,b)` proves the theorem. ∎

Reading the steps backwards, the only non-linear input is the rewrite `V -> N`. That
rewrite takes a three-ray word (`V` touches ray `b`) to a two-ray word that avoids
ray `b`. It is exactly the step that the six-ray note performs with an auxiliary ray,
and the only step whose cost is not polynomial by construction.

## Consequences

1. **The Hanoi recursion is not intrinsic.** The recorded `H_3` attempts (six-ray note
   Remark 3.2) bound the reroute `R` recursively, with `R(k) <= 2R(k-1) + O(k)`. Step 3–4
   bound it non-recursively, `R(j) <= 2A_3(j) + O(j^3)`, by one explicit
   pour-to-two-ray rewrite. The exponential factor, if there is one, lives in `A_3`.
2. **Lower bounds.** If `w_k` has superpolynomial area in `H_3`, as
   `houghton-far-transposition-commutation-is-superpolynomial` asserts for some `n`,
   then `A_3` is superpolynomial. So the rewrite `λ_ac^m λ_cb^m -> λ_ab^m ρ_b(m)` is
   the concrete object any lower-bound argument has to beat.
3. **One family controls both open cases.** `A_3 ≼ m^D` gives `δ_(H_4) ≼ x^(6+D)`
   (four-ray note, Remark 3.1) and `F_3 ≼ k^(max(D,3))` (this note).

## What is not proved (the converse)

The four-ray note's §5 sketches `A_3` via far commutations and reroutes in `H_3`. It
telescopes `E` into `u_j = λ_ac^j λ_ab λ_ca^j` and rewrites each `u_j` by
conjugating with `λ_ac`. If that sketch became a proof with polynomially many
relations of type `F_3` and Coxeter moves, then `A_3 ≍ F_3` up to polynomials.
Where it dies, as recorded here:

- Conjugating a two-ray word by `λ_ca` sends `λ_ab` to `λ_ab s_0`, with
  `s_0 = ((a,1),(b,1))`. It sends each `s_i` to a word that has to be commuted past
  `λ_ac`. That commutation is `[λ_ac, D^a_b(i-1)]`, a relation between elements with
  disjoint supports but with overlapping ray supports.
- The induction `u_j = λ_ac u_(j-1) λ_ca` therefore multiplies the word length unless
  the word is renormalized after every step. Renormalizing needs a polynomial bound
  on the number of `S_∞` Coxeter moves between two words of length `O(j^3)`.
- Each move costs `O(depth) + F_3(distance)`. The move count is not bounded here.

If the converse holds, it would make polynomial far commutation in `H_3` imply a
polynomial Dehn function for `H_4`.
