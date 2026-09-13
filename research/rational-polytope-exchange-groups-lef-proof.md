---
rg: 2
id: rational-polytope-exchange-groups-lef-proof
kind: route
title: Proof that finitely generated groups of rational polytope exchanges are LEF, by rational specialisation
target: rational-polytope-exchange-groups-are-lef
requires: []
---

Notation is as in `rational-polytope-exchange-groups-are-lef`. Let
`G = <g_1, ..., g_m>` be a group of rational polytope exchanges of `T^k`, with the
generating set closed under inverses.
- The inverse of a rational polytope exchange is one: its pieces are the images
  `g(P_j)`, which are rational polyhedral by the computation in step 1 with one letter.
- Give each generator, inverses included, its own data.
- Complements of basic sets are finite unions of basic sets with the same normals up to
  sign, since `not (⟨a, x⟩ < b)` is `⟨-a, x⟩ <= -b`. So every piece is a finite disjoint
  union of basic sets, and we take those basic sets as the pieces.
- Replacing `t_j` by `t_j - ⌊t_j⌋` does not change `g`, so assume `t_j ∈ [0, 1)^k`.
- List all offsets and translation coordinates of all generators as `P ∈ R^N`. The normals,
  the relation symbols and the frame inequalities `0 <= x_i < 1` are fixed discrete data.

**1. Itineraries, cells and displacements.** Let `w = s_M ⋯ s_1` be a word of length `M`
in the generators, applied right to left.
- An *itinerary* `ι` chooses, for `l = 1, ..., M`, a piece `β_l` of `s_l` with translation
  `t^(l)`, and a vector `ν_l ∈ {0, 1}^k`.
- Put `x_0 = x` and `x_l = x_(l-1) + t^(l) - ν_l`.
- The *cell* `C(w, ι)` is the set of `x ∈ [0, 1)^k` with `x_(l-1) ∈ β_l` and
  `⌊x_(l-1) + t^(l)⌋ = ν_l` for every `l`.
- Each defining condition has the form `⟨a, x⟩ ⋈ c`, with `a ∈ Z^k` a normal of a piece or
  `±e_i`, and `c` an affine form `⟨γ, P⟩ + κ` with `γ ∈ Z^N` and `κ ∈ Z`. For a piece
  condition, `c = b - ⟨a, Σ_(l' < l) (t^(l') - ν_(l'))⟩`. For a floor condition, `c` is
  `ν_(l,i) - t^(l)_i` or `ν_(l,i) + 1 - t^(l)_i`. So `C(w, ι)` is a basic set whose offsets
  are integer affine forms in `P`.
- Since `x_(l-1) ∈ [0, 1)^k` and `t^(l) ∈ [0, 1)^k`, the floors lie in `{0, 1}^k`. So the
  cells of `w` partition `[0, 1)^k`.
- On `C(w, ι)`, `w(x) = x + d(w, ι)` exactly in `R^k`, where `d(w, ι) = Σ_l (t^(l) - ν_l)`.
  Each coordinate of `d` is an integer affine form in `P`.

**2. Fourier–Motzkin.** Fix integer normals `a_1, ..., a_s ∈ Z^k` and relation symbols.
There are finitely many linear forms `μ_1, ..., μ_R` on `R^s` with rational coefficients,
and prescribed signs `ε_j ∈ {<0, <=0, =0}`, such that `{x : ⟨a_i, x⟩ ⋈_i c_i for all i} ≠ ∅`
iff `μ_j(c) ε_j` for all `j`.
- Eliminate `x_1, ..., x_k` one at a time.
- An equality with a nonzero coefficient of the current variable is used to substitute it.
  That keeps rational coefficients, and the right-hand sides are rational linear combinations
  of the `c_i`.
- Otherwise every pair of a lower and an upper bound is combined with positive rational
  multipliers, strict if either bound is strict, and constraints not involving the variable
  are kept.
- Each step preserves solvability. The coefficients depend only on the normals and symbols,
  and the final variable-free system is a list of sign conditions on rational linear forms in
  `c`.

**3. A finite sign vector decides the ball.** Fix `M`.
- For words `u, v` of length at most `M` and itineraries `ι, ι'`, the set
  `C(u, ι) ∩ C(v, ι')` is a basic set with integer normals whose offsets are integer affine
  forms in `P`.
- `u = v` in `G` iff `d(u, ι) = d(v, ι')` whenever that intersection is nonempty.
- By step 2, composed with the integer affine offsets, all these statements are decided by the
  signs at `P` of a finite set `Φ_M` of affine forms on `R^N` with rational coefficients.
  Each coordinate of `d(u, ι) - d(v, ι')` is itself such a form.
- **Bijectivity.** Let `Ψ` consist of the forms deciding, for each generator, that its pieces
  are pairwise disjoint and cover `[0, 1)^k`, and that the sets `{β_j + t_j}` (each a finite
  union of basic sets, with offsets shifted by integer affine forms in `P`) are pairwise
  disjoint and cover `[0, 1)^k`. Any `Q ∈ R^N` with the same signs as `P` on `Ψ` defines
  bijections `g_i^Q`.
- Choose `Φ_M` to contain `Φ_(M')` for `M' <= M`.

**4. Rational specialisation.** Fix `n` and put `Σ = Φ_(3n) ∪ Ψ`.
- Let `L` be the set of `Q ∈ R^N` with `φ(Q) = 0` for every `φ ∈ Σ` vanishing at `P`.
- `L` contains `P` and is cut out by linear equations with rational coefficients. So
  Gaussian elimination over `Q` writes `L = Q_0 + V` with `Q_0 ∈ Q^N` and `V` spanned by
  rational vectors, and `L ∩ Q^N` is dense in `L`.
- Choose `P' ∈ L ∩ Q^N` so close to `P` that every `φ ∈ Σ` with `φ(P) ≠ 0` keeps its sign.
  Then `sign φ(P') = sign φ(P)` for all `φ ∈ Σ`.

**5. The finite model.**
- Let `g_i' = g_i^(P')`, which are bijections by step 3. Put `G' = <g_1', ..., g_m'>`, with
  cells `C'` and displacements `d'` at `P'`.
- **Witness points.** Every nonempty basic set with integer normals and rational offsets
  contains a rational point. Back-substitute through the Fourier–Motzkin tower: at each stage
  the admissible values of the next variable form a nonempty interval with rational endpoints,
  possibly degenerate or unbounded, which contains a rational number, and substituting it keeps
  the data rational.
- For words `u, v` of length at most `n` and itineraries with `C'(u, ι) ∩ C'(v, ι') ≠ ∅`, pick
  one rational point in that set.
- Let `q` be a common denominator of the entries of `P'` and of these finitely many points, and
  put `Ω = ((1/q)Z ∩ [0, 1))^k`, a finite set.
- Each `g_i'` translates by vectors in `(1/q)Z^k` followed by fractional parts, so it maps
  `Ω` into `Ω`. It is injective, hence permutes `Ω`. Let `ρ : G' -> Sym(Ω)` be the action.

**6. The local embedding.** Let `B_n` be the ball of radius `n` in `G`. For `g ∈ B_n` choose a
word `w_g` of length at most `n` representing it, and put `φ(g) = ρ(w_g(g_1', ..., g_m'))`.
- **Well defined.** Words `u, v` of length at most `n` with `u = v` in `G` satisfy the same
  sign conditions in `Φ_n ⊆ Σ`, so `u = v` in `G'`.
- **Multiplicative.** If `g, h, gh ∈ B_n` have words `u, v, w`, then the word `uv` has length
  at most `2n` and equals `w` in `G`. Hence it equals `w` in `G'`, and `φ(g) φ(h) = φ(gh)`.
- **Injective.** If `g ≠ h` in `B_n` with words `u, v`, the sign data at `P'` give itineraries
  with `C'(u, ι) ∩ C'(v, ι') ≠ ∅` and `d'(u, ι) ≠ d'(v, ι')`. At the witness point `x ∈ Ω` of
  that set, `u'(x) = x + d'(u, ι) ≠ x + d'(v, ι') = v'(x)` in `R^k`. So `φ(g) ≠ φ(h)`.

So every ball of `G` embeds partially multiplicatively into a finite symmetric group, and `G`
is LEF. ∎

**Where integrality is used.** Steps 2 and 4 need the normals to be rational, so that
nonemptiness of cells is decided by rational affine forms in the parameters. With a normal
such as `(φ, 1)`, the eliminated forms have coefficients in `Q(φ)`. Then the subspace `L`
need not contain rational points near `P`, and a rational specialisation of the offsets can
create or destroy cells: these are the slivers of `research/artifacts/labbe-lef-2026-09-12.md`,
Remark L4.
