---
rg: 2
id: exact-models-cannot-separate-marked-pair-proof
kind: route
title: The collapse welds the slot sheets into one expander, and deletions cannot cut it
target: exact-models-cannot-separate-marked-pair
requires: [finite-quotient-blindness, kun-thom-nonsofic-wreath, pair-constraint-graph-criterion]
---

# The collapse welds the slot sheets into one expander, and deletions cannot cut it

Throughout, `𝒢` is the pair-constraint graph of
`pair-constraint-graph-criterion` for the window `F₀ = S_Γ ∪ S_Γ^{-1} ∪ {h}`
and the model `(A, φ)`, and "labels" means two-point label data on `S ⊆ A`.
By item 1 of that criterion, labels exist iff `(s,p)` and `(s,q)` lie in
distinct components of `𝒢` restricted to `S × {p,q}` for every `s ∈ S`.
Write `D = A ∖ S`.  Constants: `c₀ = κ²/2` and `K = 1 + 4|S_Γ|/κ²`, with `κ`
the max-convention Kazhdan constant of `(Γ, S_Γ)`.

We work in the subgraph of `𝒢` spanned by the `S_Γ`-edges on the `p`-slot
and the single `h`-edge family below.  Discarding the remaining edges is
legitimate in this direction: a sub-edge-set only refines components, so
connectivity proved in the subgraph holds in `𝒢`.

**(1) The collapse.**  An exact model is a genuine action, i.e. a
homomorphism `φ : G → Sym(A)`; let `π : G → Q := φ(G)` be the induced finite
quotient — stabilizers arbitrary, freeness never used.  `SL_d(ℤ)` acts
transitively on primitive vectors of `ℤ^d` for `d ≥ 2`, and `−(1,…,1)` is
primitive, so there is `A_h ∈ SL_d(ℤ)` with `A_h·e_1 = −(1,…,1)`; with
`u = (1, A_h)` the monomial substitution gives
`u\,e_12(x_1)\,u^{-1} = e_12(x^{A_h e_1}) = h`, and `e_12(x_1) ∈ Γ`.  By
`finite-quotient-blindness`, each compressor image normalizes `π(Γ)` and the
compressors generate `G` (infranormality, Theorem E), so `π(Γ)` is normal in
`π(G)`; hence `π(h) ∈ π(u)\,π(Γ)\,π(u)^{-1} = π(Γ)`.  Write
`Γ̄ = π(Γ) ∋ h̄ = π(h)`.  *Trust note:* the Lean file
`GroupApproximation/Criterion/FiniteQuotientBlindness.lean` formalizes the
per-compressor statements (`compressedImage_eq`,
`compressorImage_normalizes`); the generation-to-normality bridge (the
normalizer is a subgroup containing a generating set) is one line of group
theory and is currently unformalized.

**(2) Orbits.**  Decompose `A` into `Γ̄`-orbits.  Since `h̄ ∈ Γ̄`, both
`φ(h)` and `φ(h)^{-1}` preserve every orbit `O`.  This is the single
load-bearing hypothesis that separates the marked pair from the compressor
pair — see the consistency check at the end.

**(3) The p-sheet is an expander on each orbit.**  The left action of `G` on
`G/Γ` fixes `p = Γ` under every `γ ∈ Γ`, so for each `γ ∈ S_Γ` and every
`s ∈ A` the edge rule (instance `g = γ, x = p`, using `γ^{-1}·p = p`) yields
the edge `(s,p) — (φ(γ)s, p)`.  Restricted to an orbit `O`, these are
exactly the Schreier-graph edges of `(Γ, S_Γ)` acting on `O`.  On a single
orbit the invariant vectors of `ℓ²(O)` are the constants, so `ℓ²(O) ⊖ ℂ1`
has none, and property (T) for `Γ` (`kun-thom-nonsofic-wreath`, Theorem E)
gives, for `W ⊆ O` with `|W| ≤ |O|/2` and `f = 1_W − (|W|/|O|)·1`:
some `γ ∈ S_Γ` has `‖γf − f‖² ≥ κ²‖f‖² ≥ κ²|W|/2`, and
`‖γf − f‖² = |γW Δ W|`, so the generator-labelled crossing pairs number

```text
|∂W| ≥ (κ²/2)|W| = c₀|W|.
```

The constant depends only on `κ` — one constant for all reps without
invariant vectors — so it is uniform over all finite `Γ`-sets and all orbit
sizes.

**(4) The matching.**  The instance `g = h, x = q` of the edge rule — valid
because `h^{-1}·q = h^{-1}hΓ = Γ = p`, pure group theory in every
characteristic — gives for every `s ∈ A` the edge `(s, p) — (φ(h)s, q)`.
Equivalently `(s,q)` is joined to `(φ(h)^{-1}s, p)`.  No `q`-slot edges and
no conjugated generators are needed: all `q`-slot connectivity routes
through the `p`-sheet via this matching, whose endpoints stay in one orbit
by (2).

**(5) Deletion cannot fragment the sheet.**  Fix an orbit `O`, let
`D_O = D ∩ O`, and consider the `p`-sheet induced on `O ∖ D_O`.  (Components
are correctly computed there: the equivariance clause fires only when both
`s` and `φ(g)s` lie in `S`, and deleting a point removes both its slots.)
Each connected component `C` with `|C| ≤ |O|/2` has, by (3), at least
`c₀|C|` sheet edges leaving it inside `O`; none may end at a surviving
vertex outside `C` (that would extend the component), so all end in `D_O`.
Boundary edge sets of distinct components are disjoint, and a deleted vertex
meets at most `2|S_Γ|` sheet edges, so the union of all small components has
size at most `(2|S_Γ|/c₀)|D_O| = (K−1)|D_O|`.  Call `O` *good* when
`|D_O| < |O|/(2K)`.  On a good orbit some component must exceed `|O|/2`
(otherwise `|O| ≤ |D_O| + (K−1)|D_O| < |O|·(K+1)/(2K)`, forcing `2K < K+1`,
impossible for `K > 1`); two components cannot both do so, so there is a
single giant component `P` with `|O ∖ P| ≤ K|D_O|`.

**(6) Failure on good orbits.**  For `s ∈ O` with `s ∈ P` and
`φ(h)^{-1}s ∈ P`, the path

```text
(s,q) — (φ(h)^{-1}s, p) — [p-sheet inside P] — (s,p)
```

lies entirely in `S × {p,q}`, so `(s,p)` and `(s,q)` share a component and
labels fail at `s`.  Since `φ(h)^{-1}` is a bijection of `O`, the failing
`s` number at least `|O| − 2|O ∖ P| ≥ |O| − 2K|D_O|`.  (Singleton orbits
are not an exception: there `P = O = {s}`, `φ(h)^{-1}s = s`, and the path
has length one.)

**(7) Counting.**  Charging bad orbits (`|D_O| ≥ |O|/(2K)`) by
`|O| ≤ 2K|D_O|` and summing over all orbits:

```text
#failing ≥ |A| − 2K|D| − 2K|D| = |A| − 4K|D| ≥ (1 − 4Kε)|A|.
```

Every failing `s` lies in `P ⊆ O ∖ D ⊆ S`, and at a failing `s` the
criterion forces `j_s(p) = j_s(q)`, so admissible label data forbids any
failing `s` at all.  For `ε < ε₀ := 1/(4K)` the count is positive, so no
admissible `S` exists.  (A single failing basepoint already contradicts
admissibility; the density form is recorded because any extension to
approximately multiplicative models will consume it.)  ∎

**Consistency check — the theorem does not prove too much.**  Steps (3)–(4)
would apply verbatim to the compressor pair `(Γ, tΓ)` (since
`t^{-1}·(tΓ) = p` gives the same matching instance), and
`compressor-coset-two-point-exact` exhibits exact models separating that
pair with `S = A`.  No contradiction: step (2) fails there — `t̄ ∉ Γ̄` in
`Q_M`, so `φ(t)` moves each point into a *different* `Γ̄`-orbit and no
p-sheet path returns.  In the explicit labels of that node, `j_s(p) =
s^{-1}Γ̄` and `j_s(q) = s^{-1}t̄Γ̄` are distinct exactly because `t̄ ∉ Γ̄`,
while for `h` both collapse.  `h̄ ∈ Γ̄` does all the work.

**Scope notes.**  Freeness is used nowhere, so this strictly extends the
reach of item 3 of `pair-constraint-graph-criterion` (which assumed free
exact models), and it does not conflict with item 3 of
`congruence-transporter-girth`: passing the girth *test* only rules out
window-length-bounded obstruction words, while the components here are
joined by paths of unbounded length.  The refutation instantiates the
two-point definition at the single window `F₀` and any `ε < ε₀`, which
suffices against the exact subclass at every window `F ⊇ F₀` by restriction;
the definition's full `∀F ∀ε ∃model` statement is *not* refuted — an
`(F,ε)`-multiplicative `φ` breaks step (1), the orbit decomposition of (2)
is then undefined, and nothing forces `φ(h)` near any `φ(γ)`.  Whether (3)
and (4) survive genuine multiplicativity defects is exactly the surviving
question of the lane.
