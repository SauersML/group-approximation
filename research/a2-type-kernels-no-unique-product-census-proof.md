---
rg: 2
id: a2-type-kernels-no-unique-product-census-proof
kind: route
title: Normalize the supports, compute exact Cayley balls of the triangle-presentation groups by confluent rewriting, and exhaust the no-unique-product condition by SAT
target: a2-type-kernels-have-no-small-non-up-pairs
requires: []
artifacts:
  - experiments/a2-non-up-2026-09-17/up_a2.py
  - experiments/a2-non-up-2026-09-17/a2group.py
  - experiments/a2-non-up-2026-09-17/summarize.py
  - experiments/a2-non-up-2026-09-17/presentations_q2_all.json
  - experiments/a2-non-up-2026-09-17/presentations_q3.json
---

Notation as in `a2-type-kernels-have-no-small-non-up-pairs`. `|g|` is word length in
`{a_x^{±1}}`, `B(r)` the ball in `Γ_T`, and `H ∈ {Γ_0, Γ_T}` the host.

## Step 1. Unique products and normalization

**Unique-product lemma (every field).** Let `α, β ∈ k[H]` be nonzero with supports `A, B`.
If some `g ∈ AB` has exactly one expression `g = ab` with `a ∈ A`, `b ∈ B`, then the
coefficient of `g` in `αβ` is `α_a β_b ≠ 0`. So `αβ = 0` forces `(A, B)` to have no uniquely
represented product.

**Normalization.** Let `(A, B)` in `H` have no uniquely represented product, with
`rad_L(A) ≤ ra` attained at `a_0` and `rad_R(B) ≤ rb` attained at `b_0`. Put
`A' = a_0^{-1} A` and `B' = B b_0^{-1}`.
- `ab ↦ a_0^{-1} ab b_0^{-1}` is a bijection on expressions, so `(A', B')` still has no
  uniquely represented product.
- `A', B' ⊆ H`, since `H` is a subgroup.
- `1 ∈ A' ⊆ B(ra) ∩ H` and `1 ∈ B' ⊆ B(rb) ∩ H`.

So it suffices to exclude pairs with `1 ∈ A ⊆ B(ra) ∩ H` and `1 ∈ B ⊆ B(rb) ∩ H`.

**Inversion symmetry.** If `(A, B)` has no uniquely represented product, neither has
`(B^{-1}, A^{-1})`, because `(ab)^{-1} = b^{-1} a^{-1}`. Word length is inversion-invariant,
`H` is closed under inversion, and `1` stays in both sets. So the instance `(ra, rb)` is
UNSAT iff `(rb, ra)` is, for the same `T`.

## Step 2. Exact multiplication

`a2group.py` was copied unchanged from `experiments/a2-left-orderability-2026-09-17/`
(lane sw-108). For a triangle presentation `T` it builds the length-2 rewriting system:

| Rule | Rewrite | Condition |
|---|---|---|
| R0 | `a_x a_x^{-1} → 1`, `a_x^{-1} a_x → 1` | none |
| R1 | `a_x a_y → a_z^{-1}` | `(x,y,z) ∈ T` |
| R2 | `a_y^{-1} a_x^{-1} → a_z` | `(x,y,z) ∈ T` |
| R3 | `a_y^{-1} a_z → a_{z'} a_{y'}^{-1}` | `y ≠ z`, `p` the unique point with `y, z ∈ λ(p)`, `(z',p,y) ∈ T`, `(p,z,y') ∈ T` |

**Validity.**
- R0 holds in any group. R1 and R2 are rotated relators.
- R3 follows from `a_{z'} a_p a_y = 1` and `a_p a_z a_{y'} = 1`, which give
  `a_{z'} = (a_p a_y)^{-1}` and `a_{y'}^{-1} = a_p a_z`. Hence
  `a_y^{-1} a_z = (a_p a_y)^{-1} (a_p a_z) = a_{z'} a_{y'}^{-1}`.
- Conversely R0 and R1 contain the group relators. So the monoid presented by the rules
  on the letters `a_x^{±1}` is `Γ_T`.

**Termination and uniqueness.** Every rule either shortens the word or keeps its length and
lowers the number of pairs (negative letter before positive letter). So rewriting
terminates. `check_confluence()` resolves every overlap of two rules on a word of length 3.
By Newman's lemma the irreducible words are unique normal forms.

**Balls.** `A2Group.ball(r)` is breadth-first search in the Cayley graph. Layer `r+1`
consists of the normal forms `reduce(w s)`, for `w` in layer `r` and `s` a letter, that were
not seen before. Normal forms are unique, so the layers are exactly the spheres of `Γ_T`, and
their union is `B(r)`. (No rule lengthens a word, so the normal form is also a geodesic.)

**Checks repeated before every run** (`up_a2.py`, asserts):
- confluence of all critical pairs;
- every relator reduces to the empty word (`check_relators()`);
- the sphere sizes of `B(max(ra, rb))` equal the vertex counts of spheres in a thick Ã2
  building of order `q`. By Cartwright–Mantero–Steger–Zappa I (Geom. Dedicata 47 (1993)), the
  1-skeleton of the building is the Cayley graph of `Γ_T` for `{a_x^{±1}}`, and there are
  `N(m,0) = N(0,m) = (q^2+q+1) q^{2(m-1)}` and
  `N(m,n) = (q^2+q+1) q^{2(m-1)} (q^2+q) q^{2(n-1)}` vertices of shape `(m,n)` at
  graph distance `m+n`. For `q = 3` the spheres are `1, 26, 390, 4914`. For `q = 2` they
  are `1, 14, 98, 560`.

**The type kernel.** Relators have exponent sum 3, so `τ(w) = (exponent sum of w) mod 3` is
well defined on `Γ_T`, and `Γ_0 = ker τ`. `host_ball` keeps the normal forms of type 0.
For `q = 3`: `|B(2) ∩ Γ_0| = 157` and `|B(3) ∩ Γ_0| = 2263`. For `q = 2`:
`|B(3) ∩ Γ_0| = 267`, `|B(4) ∩ Γ_0| = 939`, and `|B(3)| = 673`.

## Step 3. SAT encoding

`up_a2.py`, function `build`:
- Unknowns are `x_a` (`a ∈ B(ra) ∩ H`) and `y_b` (`b ∈ B(rb) ∩ H`), with unit clauses for
  the identity in both.
- Products `ab` are grouped into cells by normal form. For a cell `P_g`:
  - if `|P_g| = 1`, the clause `¬x_a ∨ ¬y_b`;
  - otherwise `z_p ↔ x_a ∧ y_b` and "the number of true `z_p` is 0 or at least 2". Cells
    with at most 10 pairs use `z_k → ∨_{l≠k} z_l`. Larger cells use an exact sequential
    counter: `s_k` means at least one of `z_1..z_k`, `d_k` means at least two, both are
    bounded above and below, and the final clause is `s_m → d_m`.
- A model is exactly a pair `(A, B)` with `1 ∈ A`, `1 ∈ B` and no uniquely represented
  product. Here `A = {a : x_a}` and `B = {b : y_b}`, and a pair `p = (a,b)` is used iff
  `a ∈ A` and `b ∈ B`.
- The solver is CaDiCaL 1.5.3 through python-sat 1.9.dev15, single-threaded.
- Every SAT model is recomputed exactly (`verify()`) by multiplying all selected pairs in
  normal form.

UNSAT therefore excludes, for that `T`, host and radii, every normalized pair and hence, by
Step 1, every pair without a uniquely represented product with `rad_L(A) ≤ ra` and
`rad_R(B) ≤ rb`.

## Step 4. Controls

When `T` contains a triple `(x,x,x)`, `a_x^3 = 1` in `Γ_T`. Then `A = B = {1, a_x, a_x^{-1}}`
is a pair without unique products at radius 1. Running the full group at `(1,1)` must answer
SAT, and it does, with verified models:
- `q = 3`, orbit 0 (`runs/control-q3-full-r11.jsonl`): `A = {1, a_11, a_11^{-1}}`;
- `q = 2`, orbit 2 (`runs/control-q2-full-r11.jsonl`).

This tests the ball enumeration, the product table, the counter and the model extraction
end to end.

## Step 5. The presentation lists

`presentations_q2_all.json` (11 entries) and `presentations_q3.json` (133 entries) were
copied unchanged from lane sw-108.
- Lane sw-108 produced them by SAT enumeration and certified them complete: every triangle
  presentation over the standard `PG(2,q)` is `PGL(3,q)`-equivalent to one entry. The
  certificate is `complete_pg2.py`, which blocks all listed orbits and proves every cube
  UNSAT; its output is in that lane's `complete_q3.out`.
- Merging orbits under reversal `T ↦ {(z,y,x)}` gives 8 and 89 classes, the counts of
  Cartwright–Mantero–Steger–Zappa II.
- Relabeling points by `PGL(3,q)` and reversal (`a_x ↦ a_x^{-1}` composed with a plane
  isomorphism) induce group isomorphisms preserving `|·|` and `τ` up to sign. So the census
  covers every vertex-regular Ã2 lattice of order 2 or 3, and each group is run at least once
  up to isomorphism.

The claim is stated for the listed presentations. The completeness import affects only its
reading as "every such group".

## Step 6. Running and checking

```text
cd experiments/a2-non-up-2026-09-17
nice -n 10 timeout 1200 python3 up_a2.py --file presentations_q3.json --index $(seq 0 132) \
    --host gamma0 --ra 2 --rb 2 --out runs/q3-gamma0-r22.jsonl
nice -n 10 timeout 1200 python3 up_a2.py --file presentations_q2_all.json --index $(seq 0 10) \
    --host gamma0 --ra 3 --rb 3 --out runs/q2-gamma0-r33.jsonl
for i in $(seq 0 132); do     # one presentation per process, each under the 1200 s cap
  nice -n 10 timeout 1200 python3 up_a2.py --file presentations_q3.json --index $i \
      --host gamma0 --ra 2 --rb 3 --out runs/q3-gamma0-r23.jsonl
done
python3 summarize.py    # tables; nonzero exit if a SAT model fails verification
```

`runs/q3-gamma0-r23.jsonl` has one UNSAT record for each index `0..132`. The `(3,2)` case of
the claim is the `(2,3)` instance transported by the inversion symmetry of Step 1.
