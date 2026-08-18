# The minimal marked orbital graph has a private neighbour at every finite set

Kun--Thom Theorem E Laurent pair, 2026-08-18.  Full proofs for the claims
`minimal-marked-graph-private-neighbour`,
`minimal-marked-graph-nondegenerate`, `private-neighbour-density` and
`vertex-supported-symplectic-completion`.

This artifact answers the sub-question left open in
`research/invariant-graph-crossed-product-ce.md` — *is the minimal member of
the invariant-graph family nondegenerate?* — in the affirmative, and in a
form strictly stronger than nondegeneracy.  It closes the combinatorial half
of that lane.  It says nothing about the analytic half; see
"What is not claimed" at the end.

## 0. Setting and notation

Let `q` be a prime power, `r,d ≥ 3`,

```text
R₊ = F_q[x₁,…,x_d],        R = F_q[x₁^{±1},…,x_d^{±1}],
Γ  = EL_r(R₊),             N = EL_r(R),       G = N ⋊ SL_d(ℤ),
```

the Kun--Thom Theorem E pair of `kun-thom-nonsofic-wreath`, and `X = G/Γ`.
Put

```text
m = x₁x₂⋯x_d,     μ = m^{-1},     h = e₁₂(μ),     D = Γ h Γ.
```

`h` is the marked element of `docs/COMMUTING_WREATH_SOFIC_RADICAL.md`,
Corollary 2, and `{Γ, hΓ}` is the marked edge.  `S_min` is the orbital graph
of `D`: `gΓ ∼ g'Γ` iff `g^{-1}g' ∈ D`.  It is the smallest `G`-invariant
graph on `X` containing the marked edge, so every statement proved here about
`S_min` is a statement about the cheapest member of the family in
`invariant-graph-crossed-product-ce`.

`b = b_{S_min}` is the `F_2`-bilinear alternating adjacency form on
`V = F_2^{(X)}`, `b(δ_x, δ_y) = 1` iff `x ∼ y`.

Two classical inputs are used throughout and nowhere else:

* **Suslin stability.**  `SL_r(R₊) = EL_r(R₊) = Γ` for `r ≥ 3`.  In
  particular a matrix of `N` all of whose entries lie in `R₊` lies in `Γ`,
  and every constant matrix of `SL_r(F_q)` lies in `Γ`.
* **B. H. Neumann's coset-cover theorem** (Publ. Math. Debrecen **3**
  (1954), 227--242): a group is not the union of finitely many cosets of
  subgroups of infinite index.  Section 5 below replaces this by an explicit
  finite-box count, so the qualitative citation is a convenience, not a
  dependency.

## 1. The double coset is symmetric, and every root position is available

**Lemma 1.**  For `r ≥ 3` and every characteristic, `Γ h Γ = Γ h^{-1} Γ`;
and for every `p ≠ q` the element `h_{pq} = e_{pq}(μ)` lies in `D`.

*Proof.*  Let `δ = diag(-1, 1, -1, 1, …, 1) ∈ SL_r(F_q) ⊆ Γ` (this needs
`r ≥ 3`; in characteristic two `δ = I`).  Conjugation by a diagonal matrix
`diag(t₁,…,t_r)` sends `e₁₂(c)` to `e₁₂(t₁t₂^{-1}c)`, so
`δ h δ^{-1} = e₁₂(-μ) = h^{-1}`, whence `ΓhΓ = Γh^{-1}Γ` and `D = D^{-1}`.

For `p ≠ q` pick a monomial matrix `w` with `w e_j = ε_j e_{σ(j)}`,
`σ(1) = p`, `σ(2) = q`, and `ε ∈ {±1}^r` chosen so that
`det w = sgn(σ)∏ε_j = 1`; this is possible because `r ≥ 3` leaves an index
outside `{1,2}` to absorb the sign.  Then `w ∈ SL_r(F_q) ⊆ Γ` and
`w h w^{-1} = e_{pq}(ε₁ε₂^{-1}μ) = h_{pq}^{±1}`, which lies in `D` by the
first paragraph.  ∎

So `S_min` is a graph (not merely a digraph) and the marked neighbours of the
base point may be produced in any root position.

## 2. The denominator ideal, and the polynomiality of `mD`

**Lemma 2 (denominator ideal; restated from
`marked-double-coset-infinite-degree-proof`).**  Let `0 ≠ f ∈ R` and write
`f = x^w P` uniquely with `w ∈ ℤ^d` and `P ∈ R₊` divisible by no variable.
Put `w⁻_j = max(0, -w_j)`.  Then

```text
I_f := { a ∈ R₊ : a f ∈ R₊ } = x^{w⁻} R₊,
```

an ideal of `R₊`; and if `f ∉ R₊` — equivalently `w⁻ ≠ 0` — then the additive
index `[R₊ : I_f]` is infinite.

**Lemma 3.**  `m·M ∈ M_r(R₊)` for every `M ∈ D`.

*Proof.*  Write `M = A h^{ε} B` with `A,B ∈ Γ` and `ε = ±1` (Lemma 1).  Since
`h^{ε} = I + ε μ E₁₂` and `mμ = 1`,

```text
mM = m A B + ε A E₁₂ B,
```

and `A, B` have entries in `R₊`.  ∎

## 3. The exact opposite-root stabilizer, and an explicit neighbour chart

Write `U_{qp} = { e_{qp}(a) : a ∈ R₊ } ⊆ Γ`.

**Theorem 4.**  For every `p ≠ q`,

```text
U_{qp} ∩ Γ ∩ h_{pq} Γ h_{pq}^{-1} = { e_{qp}(a) : a ∈ m² R₊ }.
```

*Proof.*  `e_{qp}(a) ∈ h_{pq}Γh_{pq}^{-1}` iff
`h_{pq}^{-1} e_{qp}(a) h_{pq} ∈ Γ`.  With `h_{pq}^{±1} = I ± μE_{pq}`,
`E_{qp}E_{pq} = E_{qq}`, `E_{pq}E_{pq} = 0` and `E_{pp}E_{pq} = E_{pq}`,

```text
(I - μE_{pq})(I + aE_{qp})(I + μE_{pq})
      = I + aE_{qp} + aμE_{qq} - μaE_{pp} - μ²aE_{pq},
```

i.e. the `{p,q}` block is `[[1-μa, -μ²a],[a, 1+μa]]`, of determinant
`1 - μ²a² + μ²a² = 1`, and the identity elsewhere.  All entries lie in `R₊`
iff `μa ∈ R₊` and `μ²a ∈ R₊`, i.e. iff `m² | a`, i.e. iff `a ∈ m²R₊` (the
second condition implies the first).  For such `a` the matrix lies in
`SL_r(R₊) = Γ` by Suslin.  ∎

**Corollary 5 (neighbour chart).**  Fix `p ≠ q` and put

```text
z_a = e_{qp}(a) h_{pq} Γ        (a ∈ R₊).
```

Every `z_a` is a neighbour of the base point `Γ` in `S_min`, and

```text
z_a = z_b   ⟺   a - b ∈ m²R₊.
```

Hence `a ↦ z_a` is an injection `R₊/m²R₊ ↪ N(Γ)` — an explicit affine
parametrisation of an infinite set of marked neighbours, one for each root
direction.

*Proof.*  `e_{qp}(a) ∈ Γ` and `h_{pq} ∈ D` (Lemma 1), and `D` is
`Γ`-bi-invariant, so `e_{qp}(a)h_{pq} ∈ D` and `z_a ∼ Γ`.  For the second
statement, `z_a = z_b` iff
`h_{pq}^{-1} e_{qp}(b-a) h_{pq} ∈ Γ`, which is Theorem 4.  ∎

This strengthens `marked-double-coset-infinite-degree`, which gives infinitude
of the neighbour set but no coordinates on it.

## 4. Private neighbours

**Lemma 6 (generic row alignment).**  Let `g₁Γ, …, g_sΓ ∈ N/Γ` all differ
from `Γ`.  Then there is a single `v ∈ Γ` such that for every `i` the matrix
`v g_i` has a nonpolynomial entry in row `1`.

*Proof.*  Each `g_i ∈ N ⊆ SL_r(R)` has some entry outside `R₊`: otherwise
`g_i ∈ SL_r(R₊) = Γ` by Suslin, contradicting `g_iΓ ≠ Γ`.  Fix a column `k_i`
containing such an entry.  For `a = (a₂,…,a_r) ∈ R₊^{r-1}` put

```text
v(a) = I + Σ_{j≥2} a_j E_{1j} = ∏_{j≥2} e_{1j}(a_j) ∈ Γ,
```

a product of commuting elementary matrices, so `v(a) ∈ Γ` and `v(a)Γ = Γ`.
Row `1` of `v(a)g_i` is `row₁(g_i) + Σ_{j≥2} a_j row_j(g_i)`, so the entry in
column `k_i` is the affine expression

```text
F_i(a) = (g_i)_{1k_i} + Σ_{j≥2} a_j (g_i)_{j k_i}.
```

If every `(g_i)_{jk_i}` with `j ≥ 2` lies in `R₊`, then `(g_i)_{1k_i} ∉ R₊`
and `F_i(a) ∉ R₊` for every `a`: competitor `i` imposes no condition.
Otherwise fix `j₀ ≥ 2` with `f = (g_i)_{j₀k_i} ∉ R₊`.  The bad set
`B_i = { a : F_i(a) ∈ R₊ }` is empty or a coset of the subgroup

```text
K_i = { b ∈ R₊^{r-1} : Σ_{j≥2} b_j (g_i)_{jk_i} ∈ R₊ },
```

since differences of solutions lie in `K_i` and translation by `K_i`
preserves the condition.  Intersecting `K_i` with the `j₀` axis gives exactly
`I_f`, so

```text
∞ = [R₊ : I_f] = [axis : axis ∩ K_i] ≤ [R₊^{r-1} : K_i],
```

using `[A : A∩K] ≤ [W : K]` for `A ≤ W`.  Thus each `B_i` is a coset of an
infinite-index subgroup, and finitely many such cosets cannot cover
`R₊^{r-1}` (Neumann; or Section 5).  Any `a` outside `⋃B_i` gives the
required `v = v(a)`.  ∎

**Lemma 7 (separation from a common bad row).**  Let
`g₁Γ, …, g_sΓ ≠ Γ` and suppose every `g_i` has a nonpolynomial entry in one
common row `p`.  Fix any `q ≠ p`.  Then there is `a ∈ R₊` such that `z_a`
(Corollary 5, in the direction `(p,q)`) is adjacent to `Γ` and to none of the
`g_iΓ`.

*Proof.*  Adjacency of `z_a` to `Γ` is Corollary 5.  Suppose `z_a ∼ g_iΓ`.
Since `D = D^{-1}`,

```text
M_i = (e_{qp}(a)h_{pq})^{-1} g_i = h_{pq}^{-1} e_{qp}(-a) g_i ∈ D,
```

so `mM_i` is polynomial by Lemma 3.  Now

```text
m h_{pq}^{-1} e_{qp}(-a) = m(I - μE_{pq})(I - aE_{qp})
                          = mI - maE_{qp} - E_{pq} + aE_{pp},
```

whose row `p` is `(m+a)·e_p^T - e_q^T`.  Hence

```text
row_p(mM_i) = (m+a)·row_p(g_i) - row_q(g_i).
```

Choose a column `j_i` with `f_i = (g_i)_{p j_i} ∉ R₊`.  Polynomiality of that
entry forces

```text
a f_i + c_i ∈ R₊,      c_i = m f_i - (g_i)_{q j_i},
```

whose solution set in `a ∈ R₊` is empty or a coset of `I_{f_i}`, of infinite
index by Lemma 2.  So adjacency to competitor `i` confines `a` to one coset
of an infinite-index subgroup of `(R₊,+)`; finitely many such cosets do not
cover `R₊`, and any `a` outside their union works.  ∎

**Theorem 8 (private neighbour).**  For every nonempty finite `F ⊆ X` there
is a vertex `z ∈ X` with `|N(z) ∩ F| = 1`.

*Proof.*  `⟨Γ,h⟩ = N` (`docs/NOTEPAD.md`, `(AB5)`: constant Weyl matrices
move `e₁₂(μ)` to every root position and
`[e_{ij}(μ), e_{jk}(c·∏_{s≠l}x_s)] = e_{ik}(c x_l^{-1})`, so together with
the polynomial roots every Laurent root is reached), and the components of
`S_min` are the fibres of `X = G/Γ ↠ G/N`.  So the component of `Γ` is
`N/Γ`, no edge crosses components, and it suffices to treat `F ⊆ N/Γ`; a
general finite `F` is handled by choosing one component meeting it and
working inside that component, where a private neighbour stays private
because it has no neighbours elsewhere.

`S_min` is left `N`-invariant, so translating by `y^{-1}` for a chosen
`y ∈ F` we may assume `F = {Γ, g₁Γ, …, g_sΓ}` with `g_iΓ ≠ Γ`.  Take `v ∈ Γ`
from Lemma 6 and translate by `v`: the base point is fixed (`vΓ = Γ`) and
every competitor `v g_iΓ` now has a nonpolynomial entry in row `1`.  Lemma 7
with `p = 1` and any `q ≠ 1` supplies `z` adjacent to `Γ` and to no
`v g_iΓ`.  Translating back by `v^{-1}` and then by `y` gives a vertex
adjacent to `y` and to no other member of `F`.  ∎

**Corollary 9 (nondegeneracy).**  `Rad(b_{S_min}) = 0`.

*Proof.*  Let `0 ≠ ξ ∈ V` have (finite, nonempty) support `F`; over `F_2`,
`ξ = Σ_{x∈F} δ_x`.  Take `z` from Theorem 8.  Then
`b(ξ, δ_z) = |N(z) ∩ F| mod 2 = 1`, so `ξ ∉ Rad(b)`.  ∎

**Corollary 10 (no twins).**  Distinct `x, y ∈ X` never have equal
neighbourhoods; equivalently `gΓhΓ ≠ ΓhΓ` for `g ∉ Γ`.  (The case `|F| = 2`
of Corollary 9.)

By `invariant-graph-clifford-phase` item 4, Corollary 9 says exactly that the
minimal lamp algebra `A_{S_min}` is a factor — the hyperfinite `II₁` factor —
and that `⟨z⟩` is the monolith of `W̃_{S_min}`.

## 5. Quantitative form: bad parameters have vanishing density

For `L ≥ 0` let `P_L ⊆ R₊` be the `F_q`-span of the monomials `x^α` with
`0 ≤ α_j ≤ L` for all `j`, so `|P_L| = q^{(L+1)^d}`.  For `f ∉ R₊` write
`I_f = x^u R₊` with `u = w⁻ ≠ 0` (Lemma 2).  Then `I_f ∩ P_L` is the span of
the `x^{u+β}` with `β_j ≤ L - u_j`, so

```text
dim_{F_q}(I_f ∩ P_L) = ∏_j max(L - u_j + 1, 0),
κ_u(L) := (L+1)^d - ∏_j max(L - u_j + 1, 0)  →  ∞   (L → ∞),
```

the growth being `κ_u(L) ~ (Σ_j u_j)(L+1)^{d-1}`.

**Lemma 11.**  For any `c ∈ R`, the set `{ a ∈ P_L : af + c ∈ R₊ }` is empty
or is a coset of `I_f ∩ P_L` inside `P_L`, hence has relative size exactly
`q^{-κ_u(L)}`.

*Proof.*  Two solutions differ by an element of `I_f`, and the difference
lies in the `F_q`-subspace `P_L`; conversely translating a solution by
`I_f ∩ P_L` preserves the condition.  ∎

**Corollary 12 (abundance).**  Fix competitors as in Lemma 7 and draw `a`
uniformly from `P_L`.  The probability that `z_a` is adjacent to some
competitor is at most `Σ_i q^{-κ_{u_i}(L)} → 0`.  Likewise, in Lemma 6, if
each shear parameter is drawn uniformly and independently from `P_L`, then
conditionally on the others the remaining coordinate must avoid at most one
coset of `I_{f_i} ∩ P_L`, so the alignment fails with probability at most
`Σ_i q^{-κ_{u_i}(L)} → 0`.

So the construction is not merely non-constructive parity: high-degree random
shears and random root parameters are private neighbours with probability
tending to one, which is what an ensemble-of-blocks construction would need.

## 6. Finite completions supported on actual vertices

Global nondegeneracy does not make an arbitrary finite window nondegenerate.
The private-neighbour property repairs windows using real vertices, with an
explicit bound.

**Theorem 13.**  Let `F ⊆ X` be finite and `V_F = span_{F_2}{δ_x : x ∈ F}`.
There is a finite `F' ⊇ F` with `b|_{V_{F'}}` nondegenerate and

```text
|F' \ F| = dim Rad(b|_{V_F}) ≤ |F|,     so |F'| ≤ 2|F|.
```

*Proof.*  Let `V = V_{F''}` be the current window with `Rad(V) ≠ 0` and pick
`0 ≠ ξ ∈ Rad(V)`.  Theorem 8 applied to `supp(ξ)` gives a vertex `z` with
`b(δ_z, ξ) = 1`; in particular `δ_z ∉ V`, since `ξ` pairs trivially with all
of `V`.  Put `V' = V + F_2δ_z` and `φ = b(δ_z, ·)|_V`.  For
`x + αδ_z ∈ Rad(V')` and all `v ∈ V`, `b(x,v) + αφ(v) = 0`.  If `α = 1` then
`φ` lies in the image of `V → V^*`, `x ↦ b(x,·)|_V`, whose image is the
annihilator of `Rad(V)` (kernel `Rad(V)`, so the dimensions agree) — but
`φ(ξ) = 1`.  So `α = 0` and

```text
Rad(V') = Rad(V) ∩ ker φ,
```

of dimension exactly `dim Rad(V) - 1`.  Iterate.  ∎

**Corollary 14 (vertex-supported full-matrix exhaustion).**  Enumerate
`X = {x₁, x₂, …}` and set `F_n = ` the completion of `F_{n-1} ∪ {x_n}` given
by Theorem 13.  Then `F₁ ⊆ F₂ ⊆ ⋯`, `⋃F_n = X`, each `b|_{V_{F_n}}` is
nondegenerate — so `|F_n|` is even and the twisted group algebra at the
character `z ↦ -1` is

```text
C*_σ(V_{F_n}) ≅ M_{2^{|F_n|/2}}(ℂ),
```

— and `V_{F_{n+1}} = V_{F_n} ⊕ V_{F_n}^⊥` symplectically, so each inclusion
is a tensor-factor inclusion.  Hence `A_{S_min}` is exhausted by full matrix
Clifford blocks generated by actual vertices; its C*-completion is the
`2^∞`-UHF algebra and its tracial closure the hyperfinite `II₁` factor.

**Corollary 15 (exact finite lamp microstates).**  For every finite lamp
window `F ⊆ X` there are `D ≤ 2^{|F|}` and self-adjoint unitaries
`W_x ∈ M_D(ℂ)`, `x ∈ F`, with

```text
W_x W_y = (-1)^{b(δ_x,δ_y)} W_y W_x        exactly,
tr_D(W) = 0 for every nontrivial Weyl word W in the W_x,
```

matching the canonical twisted-group trace on that window exactly.  (Complete
`F` to `F'` by Theorem 13 and take `D = 2^{|F'|/2} ≤ 2^{|F|}`.)

The abstract hyperfiniteness of `A_S` for nondegenerate `S` was already
recorded in `invariant-graph-clifford-phase`; what is new is that for the
minimal graph nondegeneracy *holds*, and that the exhaustion can be taken
supported on graph vertices with the size bound above.

## 7. Checks

* `g_i ∉ Γ` really forces a Laurent denominator: `g_i ∈ N ⊆ SL_r(R)`, and
  all-polynomial entries would give `g_i ∈ SL_r(R₊) = EL_r(R₊) = Γ`.
* The row shear is in `Γ` and fixes the base coset, so applying Lemma 6 does
  not move the point that is to be kept private.
* The bad sets are genuine cosets of subgroups: both conditions
  (`F_i(a) ∈ R₊` and `a f_i + c_i ∈ R₊`) are affine over the additive group,
  and their homogeneous parts are the subgroups `K_i`, `I_{f_i}`.
* Lemma 3 uses no inverse or determinant: `mM = mAB + εAE₁₂B` term by term.
* The row identity of Lemma 7 was recomputed from
  `h_{pq}^{-1}e_{qp}(-a) = I - aE_{qp} - μE_{pq} + μaE_{pp}` in general
  characteristic; characteristic two is the special case `h = h^{-1}`,
  `δ = I`, and nothing else in the argument sees the characteristic.
* Theorem 13's radical drop is exactly one because `φ` is nonzero *on*
  `Rad(V)`, not merely nonzero.
* A finite-support radical candidate meets only finitely many components; a
  private neighbour inside one of them pairs to `1` globally because no edge
  leaves a component.

## 8. What would falsify this

Three inputs carry the weight: the denominator identity (Lemma 2, already in
`marked-double-coset-infinite-degree-proof`); Suslin stability
`SL_r(R₊) = EL_r(R₊)` for `r ≥ 3`; and the identification of the marked
element and of `⟨Γ,h⟩ = N`.  Everything else is explicit matrix arithmetic
reproduced above.  A cheap independent regression test would be to evaluate
Lemmas 6 and 7 in a truncated Laurent model for small `r, d` and bounded
degree, or to formalise Lemma 2 plus the two affine-coset arguments.

## 9. What is not claimed

Nothing here bears on Connes embeddability.  The minimal graph now satisfies
the *algebraic* conditions demanded by `invariant-graph-crossed-product-ce`
(marked edge present, `b_S` nondegenerate, base a hyperfinite factor), which
removes the existential search over graphs from that lane's combinatorial
half and leaves exactly one target,

```text
A_{S_min} ⋊ G is Connes embeddable,
```

recorded as `minimal-marked-graph-crossed-product-ce`.  The obstruction that
the rest of the corpus isolates — coherent, non-coordinate Clifford/action
microstates — is untouched, and is *not* implied to be surmountable by any
of the finite constructions above: `marked-double-coset-infinite-degree`
still forbids finite degree, the finite-rank invariant-form no-go of
`docs/NOTEPAD.md` still forbids a `G`-invariant finite symplectic quotient
retaining the mark, and the completions of Section 6 are noninvariant by
construction.
