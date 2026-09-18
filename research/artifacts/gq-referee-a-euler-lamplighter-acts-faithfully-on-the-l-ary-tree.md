# Referee report (gq-referee-a, proof-gap lens): the Euler lamplighter acts faithfully on the l-ary tree

**Reviewed:**
- `euler-lamplighter-acts-faithfully-on-the-l-ary-tree` and its route `-proof` (lane gq-k2-q, c49d99f83), read on
  origin/main;
- on request, the heuristics of the OPEN companion `euler-lamplighter-has-a-faithful-finite-state-action`.

**Verdict: PASS.** Items 1–4 hold as stated, and I found no gap. Nits N1–N4 are one-line additions. Nit N3 is needed
for the phrase "residual `l`-finiteness", because the tree action alone gives only residual finiteness when `l` is
odd. The companion's heuristics are mostly fair, and three points are listed at the end.

## Checks, by item

**Item 1: the model.**
- *`ι` is injective and has dense image.* If `p(1+T) = 0`, then `q = y^N p` is a polynomial with `q(1+T) = 0` in
  `Z_l[T] ⊂ Λ`, so `q = 0`. The image is dense because `ι(Z[y]) = Z[T]` surjects onto every `Λ/(l,T)^n`. ✓
- *`F_n` is a coefficient condition.* `F_n = (l,T)^n` is the set of `Σ c_b T^b` with `v_l(c_b) ≥ n − b`. This set
  contains the generators `l^a T^(n−a)` and is an ideal. ✓
- *`lD` preserves `F_n`.* The `T^(b−1)`-coefficient of `lD g` is `l b c_b + l(b−1) c_(b−1)`. It has valuation
  `≥ n − (b−1)`, so `lD(F_n) ⊆ F_n`. ✓
- *The Neumann series converges.* `(lD)^k Λ ⊆ l^k Λ ⊆ F_k`, so `Σ (−lD)^k` converges (l,T)-adically and inverts
  `β̂`.
- *The relations and the action.*
  - The composite of `x̂^(±1)` and `β̂^(±1)` along any word trivial in `H` is continuous and is the identity on the
    dense `ι(M)`. Here `β̂^(−1) ι = ι β^(−1)` because `β̂ ι β^(−1) = ι`. So it is the identity on `Λ`.
  - `ĥ τ_(ι(m)) ĥ^(−1) = τ_(ι(hm))`, so `(m, h) ↦ [g ↦ ĥg + ι(m)]` is an action of `M ⋊ H`.
- *Faithfulness.* If `(m, h)` acts trivially, evaluating at `g = 0` gives `ι(m) = 0`, so `m = 0`. Then `ĥ = 1`
  restricts to `h = 1` on `M`, and `H ≤ Aut(M)`. ✓

**Item 2: the measure picture, checked as asked.**
- Under the Iwasawa identification `Z_l[[Z_l]] ≅ Z_l[[T]]`, `δ_1 ↦ 1+T`, which is classical, so `(1+T)^j = δ_j`
  and `Dδ_j = jδ_j`.
- Two operators are both continuous:
  - `D`, which maps `F_n` into `F_(n−1)`;
  - multiplication of measures by the continuous function `x ↦ x`.
- They agree on `Z_l[T] = span{δ_j : j ≥ 0}`, which is dense. So they are equal, and `β̂` is multiplication by
  `1 + lx`, a function with values in `1 + lZ_l ⊂ Z_l^×`.
- Its inverse is multiplication by `(1+lx)^(−1)`, in agreement with the Neumann series. ✓

**Item 3: the flag.**
- *The graded action.* `lD(l^a T^(n−a)) = (n−a) l^(a+1) T^(n−a−1) + (n−a) l^(a+1) T^(n−a)`, and the second term
  lies in `F_(n+2)`.
  - So `β̂ e_a ≡ e_a + (n−a) e_(a+1)` on `gr_n`. At `a = n` the coefficient is 0, so no `e_(n+1)` is needed.
  - `(1+T)^(±1) ≡ 1` on `gr_n`, since `T F_n ⊆ F_(n+1)`.
  - Hence `lD`, `β̂` and `(1+T)^(±1)` preserve every `E_(n,j)`.
- *The endpoints of the flag.* `E_(n,0) = F_n` and `E_(n,n+1) = F_(n+1) = E_(n+1,0)`. Each step
  `E_(n,j)/E_(n,j+1)` is `F_l e_j`, since `l e_j ∈ F_(n+1)`. ✓
- *Inverses.* `β̂^(−1)` preserves `E_(n,j)`: `E_(n,j) ⊇ F_(n+1)` is open, hence closed, and each `(lD)^k` preserves
  it. Alternatively, `β̂` induces a surjection of the finite set `Λ/E`, hence a bijection.

**Item 4: the tree.**
- *Cosets.* Affine maps whose linear part is bijective and preserves each `E` permute the cosets compatibly with
  inclusion.
- *`l`-regularity.* Each coset of `E_(n,j)` splits into `l` cosets of `E_(n,j+1)`. ✓
- *Faithfulness on the tree.* An element fixing every vertex maps `g` into `∩_k (g + E_k) = {g}`. So it is trivial on
  `Λ`, hence trivial. ✓
- *Ends.* The ends are `lim Λ/E_k`. The `E`-topology equals the (l,T)-adic topology, and `Λ` is compact, so the ends
  are `Λ`. ✓
- *The coordinates.* Membership in `E_(n,j+1)` is a set of conditions `c_b ≡ 0 (mod l^(k_b))` on separate
  coefficients. For `g − g'` each condition says that the first `k_b` digits of `c_b(g)` and `c_b(g')` agree. So
  carries never cross between coefficients or break the digit description.
  - The step `E_(n,j) → E_(n,j+1)` reads the digit `d_(j, n−j)`. This is the order `a + b` ascending, then `a`
    ascending, as stated. ✓

## Nits
- **N1 (Part 1).** "`D^k` lowers `T`-degree by at most `k`" plays no role. The reason is `(lD)^k Λ ⊆ l^k Λ`.
- **N2 (Part 2).** Add the density-and-continuity sentence above. The proof now says only "continuous extension".
- **N3 (the last line, "residual `l`-finiteness").** For odd `l`, the level quotients of `Aut(T_l)` are not
  `l`-groups, so the tree action alone gives residual finiteness only. The `l`-version needs one more line, and it
  holds:
  - by item 3 every linear part acts trivially on each step quotient `F_l e_j`. For `β̂`,
    `e_j + (n−j)e_(j+1) ≡ e_j (mod E_(n,j+1))`.
  - So the image of `G_l` on `Λ/E_k` consists of translations and elements of the stability group of a series of a
    finite `l`-group. That stability group is an `l`-group.

  Either add this, or say "residual finiteness".
- **N4 (Part 1, faithfulness).** Spell out the evaluation at `0`, as above.

## The companion OPEN node's heuristics (not reviewed as a proof)
- **H1, overstated.** "A faithful finite-state action is the same as an embedding of `G_l` in a finitely generated
  self-similar group" is not right in one direction: the elements of a finitely generated self-similar group need not
  be finite-state.
  - The correct class is *automaton groups*: groups generated by a finite set closed under taking sections.
  - The group generated by the states of `f_0, x, β` is such a group. Every element of an automaton group is
    finite-state, so the equivalence holds with that class.
- **H2, the hypothesis is too weak.** "`q`-th roots of `f_0` for `q > d` are unique in `Aut(T_d)`" needs `q` to have
  no prime factor `≤ d`. That makes `g ↦ g^q` bijective on every level quotient, since their orders have only prime
  factors `≤ d`. It also needs `l ∤ q`, so that `f_0/q ∈ M`. For example, `d = 3`, `q = 4` fails.
- **H3, not misleading as hedged, but the mechanism is misplaced.**
  - The algebra `1 + lx = (1+la)(1 + l^(m+1)x'/(1+la))` on `a + l^m Z_l` is right. But a cylinder of `Z_l` is not a
    vertex of the tree of `Λ`. Cylinders index a direct-sum decomposition of `Λ`, that is, coordinates. Sections live
    at vertices, which are cosets of `E_k`, finite data of the measure.
  - The honest form: in cylinder-value coordinates, the digit stream of the coordinate `(a, m)` is multiplied by the
    integer `1 + la`. Infinitely many such streams are interleaved, and the pending carries are unbounded.
  - In monomial digits the graded action `e_a ↦ e_a + (n−a) e_(a+1)` is periodic mod `l` in `(n, a)`. So any
    obstruction there sits in the carries of the integer factors `b` in `D(l^a T^b)`, not in the graded part. That is
    where a proof, or a finite-state recoding, would have to act.
- The arXiv:2405.16678 statement belongs to the citation lens.
