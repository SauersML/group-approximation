---
rg: 2
id: quantum-rigid-subshifts-are-determined-by-thick-collars
kind: claim
title: In a quantum-rigid subshift, every thick cut has at most one free side, so collars determine interiors; hence rigid subshifts over amenable groups have zero entropy, rigid subshifts over two-ended groups are countable, cap coherence in finite fibres forces the group to be amenable, and rigid Toeplitz shifts carry nested periodic wire nets
distinct_from:
  rigid-subshifts-without-isolated-points-factor-onto-the-ends: that glues across the components of the complement of a ball; this glues across an arbitrary cut, whose two sides may both be infinite and need not be components.
  positive-entropy-sft-crossed-products-are-not-fp: that refutes rigidity of positive-entropy Z^2-SFTs through recurrence of an annulus pattern; this proves zero entropy for every rigid subshift over every amenable group, with no finite type, no recurrence and no measure on the rigid side.
  rigid-subshift-amenability-from-coherent-variation-caps: that reduces (RA) to cap coherence; this shows that in finite fibres over the equicontinuous factor cap coherence forces the group to be amenable, so the finite-fibre case of (RA′) is a non-existence statement.
  time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows: that locates non-exact automorphism groups of Z^d-rows in infinite fibres; this treats finite fibres for an arbitrary acting group and gives the structure a residually finite counterexample would need.
---

**ESTABLISHED** for items 1–6 (lane proof, elementary; bh-ra-proof, 2026-09-19; not reviewed; no
priority claimed). The standard facts marked "recalled" were not re-read. (RA) and (RA′) stay **open**.

## Setting

- `Λ` is finitely generated, with the left-invariant word metric `d(a,b) = |a⁻¹b|`. Then
  `N_w(F) = F·B_w`, and the *collar* of `F` is `∂_w F = F·B_w ∖ F`.
- `X ⊆ A^Λ` is a subshift (finite type not assumed), `D`-quantum rigid over some field, in the sense of
  `fp-v-times-subshift-full-groups-force-quantum-rigidity`. Put `w = 2D`.
- The action is `(g.x)(h) = x(g⁻¹h)`, and `Δ(x,y) = {q : x(q) ≠ y(q)}`.
- `L_F(X)` is the set of patterns on `F` that occur in `X`.

## Theorem

1. **One free side per cut.**
   - Let `Λ = P ⊔ M ⊔ N` with `d(P, N) > 2D`, let `ω ∈ L_M(X)`, and let `y ∈ X` extend `ω`.
   - Then either every extension of `ω` in `X` agrees with `y` on `P`, or every extension agrees with
     `y` on `N`.
2. **Collars determine interiors.** Suppose `X` has no isolated points, and let `F` be finite.
   - Then `x|∂_w F` determines `x|F`.
   - So `|L_F(X)| ≤ |L_(∂_w F)(X)| ≤ |A|^(|∂_w F|)`.
3. **Amenable groups: zero entropy.** If `Λ` is infinite and amenable, every quantum-rigid subshift over `Λ` has
   topological entropy `0`. Isolated points are allowed.
4. **Two-ended groups: countability.** If `Λ` is virtually infinite cyclic, every quantum-rigid subshift
   over `Λ` is countable. So no infinite minimal subshift over `Λ` is quantum rigid.
5. **Finite fibres (the finite-fibre case of (CC′)).** Let `X` be minimal and infinite, and suppose its
   maximal equicontinuous factor `π : X → Z` has finite fibres.
   - (a) `X` carries a `Λ`-invariant Borel probability measure.
   - (b) If `X` satisfies cap coherence (CC) of `rigid-subshift-amenability-from-coherent-variation-caps`,
     then `Λ` is amenable. The same holds if `Λ ↷ X` is merely topologically amenable.
   - (c) Over an amenable `Λ`, (RA) holds at `X` for trivial reasons, and item 3 adds zero entropy.
     Over a non-amenable `Λ`, (CC′) restricted to finite fibres is equivalent to the non-existence
     statement **(RA_fin)**: *no infinite, minimal, quantum-rigid subshift over a non-amenable group is
     finite-to-one over its maximal equicontinuous factor.*
   - Coherence cannot prove (RA_fin), because at any such `X` (CC) is false. Only non-existence can.
6. **Rigid Toeplitz shifts carry nested wire nets.**
   - *Setting.* Let `Λ` be residually finite and `x` a Toeplitz point: every `g` has a normal
     finite-index `Γ` with `x(γg) = x(g)` for all `γ ∈ Γ`. Let `X` be the orbit closure of `x`, and
     suppose `X` is infinite and `D`-rigid.
   - *Notation.* For normal finite-index `Γ`, let `Per_Γ` be the set of those `g`, and
     `H_Γ = Λ ∖ Per_Γ` the *holes*. Both are left `Γ`-invariant. The *level class* is
     `K_Γ = {y ∈ X : y = x on Per_Γ}`, and it contains `Γ.x`.
   - (a) All the variation of the level class, `⋃_(y ∈ K_Γ) Δ(x,y)`, lies in a single `2D`-coarse
     component `C_Γ` of `H_Γ`.
   - (b) `γ C_Γ = C_Γ` for every `γ ∈ Γ`. So `C_Γ` is a coarsely dense, uniformly coarsely connected,
     `Γ`-periodic *wire net*, quasi-isometric to `Λ`.
   - (c) The nets are nested and escape. If `Γ' ≤ Γ`, then `C_(Γ') ⊆ C_Γ`. `C_Γ` misses every ball
     contained in `Per_Γ`, and `⋂_Γ C_Γ = ∅`.

## Proof

1. Suppose `y_1` extends `ω` and differs from `y` on `P`, and `y_2` extends `ω` and differs from `y` on
   `N`. Let `z` be `y_1` on `P`, `ω` on `M`, and `y_2` on `N`.
   - A ball `pB_D` has diameter `≤ 2D < d(P,N)`, so it lies in `P ∪ M` or in `M ∪ N`. There `z` reads
     `y_1` or `y_2`, so every `B_D`-pattern of `z` occurs in `X`.
   - `Δ(y, z)` meets `P` and `N`, and is contained in `P ∪ N`. Its two parts are at distance `> 2D`.
   - Lemma 1′ (the two-piece certificate) of `rigid-subshifts-over-free-factors-are-tight-almost-everywhere`
     then refutes `D`-rigidity.
   - This is the gluing step of `rigid-subshifts-without-isolated-points-factor-onto-the-ends`, stated
     for an arbitrary cut.
2. Take `P = F`, `M = ∂_w F` and `N = Λ ∖ F·B_w`. Then `d(P, N) ≥ w + 1 > 2D`. Apply item 1 to
   `ω = x|M` and `y = x`.
   - In the first case, every extension agrees with `x` on `F`.
   - In the second case, every extension agrees with `x` off the finite set `F`. Two distinct such
     extensions would be a modification with finite support. That is impossible by item 1(c) of
     `rigid-subshift-amenability-from-coherent-variation-caps`, since `X` has no isolated points. So the
     extension is `x` alone.
3. Suppose `h_top(X) > 0`. By the variational principle for amenable groups (recalled), some ergodic
   invariant `μ` has `h_μ > 0`. Let `S = supp μ`, a closed invariant subset.
   - *`S` has no isolated points.* An isolated point `s` of `S` has `μ({s}) > 0`. Invariance gives every
     point of `Λs` the same mass, so `Λs` is finite. By ergodicity `μ` lives on that finite orbit, and
     then `h_μ = 0` (recalled), a contradiction.
   - *`S` is rigid* (`quantum-rigidity-passes-to-subshifts`).
   - *Entropy.* With the action above, the pattern windows `E_n` in the entropy formula are inverses of
     Følner sets. So `|E_n B_w ∖ E_n| = o(|E_n|)`. By item 2, `log|L_(E_n)(S)| ≤ |∂_w E_n| log|A|`, hence
     `h_top(S) = 0 < h_μ ≤ h_top(S)`. This is a contradiction.
4. Let `⟨t⟩ ≤ Λ` be infinite cyclic of finite index, with right coset representatives `c_1, …, c_k`. Put
   `F_r = {t^j c_i : |j| ≤ r}`.
   - For `b ∈ B_w`, write `c_i b = t^(e) c_(i')`. Then `|e| ≤ L` for some `L` that does not depend on
     `r`. So `|∂_w F_r| ≤ 2kL` for all `r`, and the `F_r` exhaust `Λ`.
   - Let `X_perf` be the perfect kernel (Cantor–Bendixson). It is closed and invariant, rigid by
     `quantum-rigidity-passes-to-subshifts`, and has no isolated points.
   - Item 2 gives `|L_(F_r)(X_perf)| ≤ |A|^(2kL)` for every `r`. Distinct points differ on some `F_r`, so
     `X_perf` is finite. A nonempty finite space has isolated points, so `X_perf = ∅`.
   - Then `X` is scattered, hence countable (recalled). An infinite minimal subshift has no isolated
     points, so it cannot be rigid.
5. (a) `Z = K/H` for a compact group `K` into which `Λ` maps densely, and it carries the image `m` of
   Haar measure (recalled).
   - Put `μ = ∫ u(π⁻¹(ζ)) dm(ζ)`, where `u` is the uniform measure on a finite fibre. The fibre map
     `ζ ↦ π⁻¹(ζ)` is upper semicontinuous into the hyperspace, hence Borel, and `u` is Borel on finite
     sets (recalled). So the integral makes sense.
   - `g` maps `π⁻¹(ζ)` bijectively onto `π⁻¹(gζ)`, so `μ` is invariant.

   (b) By item 4 of the caps node, (CC) gives continuous maps `m_R : X → Prob(Λ)` with
   `sup_x ‖g_* m_R(x) − m_R(g.x)‖_1 → 0`. Put `λ_R = ∫ m_R dμ`. By invariance of `μ`,
   `‖g_* λ_R − λ_R‖_1 ≤ sup_x ‖g_* m_R(x) − m_R(g.x)‖_1 → 0`. That is Reiter's condition, so `Λ` is
   amenable.

   (c) Every action of an amenable group is topologically amenable (recalled). The equivalence follows
   from (b).
6. (a) Take `y ∈ K_Γ` with `y ≠ x`.
   - `Δ(x,y) ⊆ H_Γ`, and it is `2D`-coarsely connected (item 1(a) of the caps node). So it lies in one
     component of `H_Γ`.
   - Suppose `y_1, y_2 ∈ K_Γ` vary in different components `C ≠ C'`. Apply item 1 with `P = C`,
     `N = H_Γ ∖ C`, `M = Per_Γ`, `ω = x|Per_Γ` and base point `x`. Distinct `2D`-components are at
     distance `> 2D`, so this contradicts item 1.

   (b) `X` is infinite, so `x` is not `Γ`-periodic. Fix `γ' ∈ Γ` with `γ'.x ≠ x`; then
   `∅ ≠ Δ(x, γ'.x) ⊆ C_Γ`.
   - For `γ ∈ Γ`, both `γ.x` and `γγ'.x` lie in `K_Γ`. So
     `γΔ(x, γ'.x) = Δ(γ.x, γγ'.x) ⊆ Δ(γ.x, x) ∪ Δ(x, γγ'.x) ⊆ C_Γ`.
   - Also `γΔ(x, γ'.x) ⊆ γC_Γ`. Since `γ` permutes the components of the invariant set `H_Γ`,
     `γC_Γ = C_Γ`.
   - `C_Γ` contains an orbit `Γc`. Finite index makes that orbit coarsely dense.
   - `Γ` acts freely and cocompactly on the `2D`-graph of `C_Γ`, which is connected and locally finite.
     Švarc–Milnor (recalled) makes it quasi-isometric to `Γ`, hence to `Λ`.

   (c) `Per_Γ ⊆ Per_(Γ')`, so `H_(Γ') ⊆ H_Γ`. `C_(Γ')` is `2D`-connected and contains
   `Δ(x, γ.x) ⊆ C_Γ` for some `γ ∈ Γ'`. So `C_(Γ') ⊆ C_Γ`. Since `x` is Toeplitz, every `g` eventually
   lies in `Per_Γ`, which gives the last claim. ∎

## Calibration

| Case | Consistent with |
|---|---|
| Ledrappier over `Z^2`: a difference vanishing on an annulus vanishes inside (look at the top row of a finite support); entropy `0` | item 2, item 3 |
| positive-entropy `Z^2`-SFTs (`positive-entropy-sft-crossed-products-are-not-fp`) | item 3 recovers the non-rigidity for all subshifts and all amenable groups |
| step shift `{x ∈ {0,1}^Z nondecreasing}`: rigid, countable (constants plus isolated steps) | item 4 |
| group subshifts over `Z`: rigid iff the lamp group `M ⋊ Z` is fp (`group-subshifts-are-quantum-rigid-iff-the-lamp-group-is-fp`), which in characteristic `p` forces `M` finite (Bieri–Strebel, recalled) | item 4: a countable compact group is finite |
| Cornulier-regime coset shifts over `V`: rigid, Bernoulli, not minimal; every coset `gΔ` meeting `F` leaves through `∂_w F` when `Δ` is generated inside `B_w` | item 2 holds (`L_F` is read on `F·s_0 ⊆ ∂_w F·s_0`); items 3–5 do not apply (`V` is non-amenable, and the shift is not minimal) |
| crossing-wire and hierarchical `Z^2` rows: minimal, rigid, at most `|τ|`-to-one over the odometer (`automorphisms-of-hierarchical-rows-are-virtually-abelian`) | item 5(c): the group is amenable, and entropy is `0`; item 6 predicts that the variation of a level class runs along one `Z^2`-periodic connected seam net (heuristic, not checked) |
| time lifts `G × Z^d` over finite-fibre rows: `G` is finite-by-abelian (`time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows`, item 2) | item 5(c): amenable, so (RA) holds outright |

## What this says about (RA′)

> **Scope (2026-09-19).** (RA) as stated is **refuted** on main by a non-free example with a
> non-amenable point stabilizer (`rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer`; the group
> there is exact). What survives is
> - (RA′): a minimal, topologically free, rigid subshift forces an exact group;
> - (RA_free): a free, minimal, rigid subshift action is amenable.
>
> Read "(RA)" below as one of these, as stated at each use.

Here item 5 concerns the finite-fibre form (RA_fin), which the non-free refutation does not touch: its
example carries no invariant measure. A rigid Toeplitz shift over `G` refutes (RA′) if it is
topologically free, and (RA_free) as well if it is free.

- **Correction to the plan "prove (CC) in finite fibres".** In finite fibres, an invariant measure
  exists. So (CC) there holds only over amenable groups, where (RA) needs no proof. Every rigid row on
  main is of this kind. The finite-fibre case at a non-amenable group is the non-existence statement
  (RA_fin), not a coherence statement.
- **What remains at Osajda's group `G`.** `G` is residually finite. A finite-fibre counterexample over an
  overgroup of `G` is Toeplitz-like: an almost 1-1 or finite-to-one extension of a profinite
  odometer. Item 6 says what it must carry:
  - at every level, a `Γ`-periodic, coarsely connected hole net that holds all the variation of the
    level class;
  - quasi-isometric to the group;
  - nested in `Γ`, and escaping every ball.

  So the door that bh-invent-16 left open for residually finite inputs, the profinite distal layer,
  is a question about nested periodic wire nets in a non-amenable group.
- **Infinite fibres** (a relatively weakly mixing layer, or a non-expansive distal layer) remain as in
  `time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows`. There join-cap coherence (JC′) of `products-of-trees-refute-cap-coherence-join-caps-restore-it` is the target; plain (CC′) is false (cf68fcdd7).

## Lesson for general BH

**Quantum rigidity is boundary determination.**
- Every thick cut has at most one free side. So the pattern on a collar determines everything inside
  it.
- Over amenable groups, that forces zero entropy for every rigid ambient. Over two-ended groups, it
  forces countability.
- For (RA′), it splits the problem by the equicontinuous factor.
  - In finite fibres an invariant measure exists, and amenability of the action would force the group
    to be amenable. So the question there is non-existence, and its residually finite form is about
    nested periodic wire nets.
  - Join-cap coherence (JC′) is the right target only in infinite fibres. Plain (CC′) fails already for
    `∂T_m ⊠ ∂T_n` (cf68fcdd7).

Credit: the variational principle for amenable groups is due to Ornstein–Weiss and Kerr–Li (recalled).
The link between amenable actions with invariant measures and amenable groups is due to
Anantharaman-Delaroche and Renault. Structure of equicontinuous minimal systems is due to Ellis
(recalled). The two-piece certificate, the clustering theorem and the ends gluing are bh-star-b's
(ca15e5298, f676c07d2, 6a95ce886). The fibre bookkeeping over `Z^d` rows is bh-invent-16's (c930a62ab).
The permutational scope correction is bh-ra-counter's (4ed22df890).

## Referee (bh-ref-hl, 2026-09-19): PASS for items 1–6, with two precisions to item 5(c)

This is an internal lane review, line by line. Lemma 1′ and items 1(a), 1(c) and 4 of
`rigid-subshift-amenability-from-coherent-variation-caps` are used as stated. I checked that 1(a) is Lemma 1′ applied to `x, y ∈ X`,
and that 1(c) uses only non-isolatedness.
- **Item 1 (the key step).**
  - A `D`-ball has diameter `≤ 2D < d(P,N)`, so it lies in `P ∪ M` or in `M ∪ N`, where `z` reads `y_1` or `y_2`. So every
    `B_D`-pattern of `z` occurs.
  - `Δ(y,z) ⊆ P ∪ N` meets both sides. Lemma 1′ needs only colourings with occurring `B_D`-patterns, so `z ∉ X` is allowed.
    Correct.
- **Item 2.**
  - `d(F, Λ∖F·B_w) ≥ w+1 > 2D`.
  - In the second case, two distinct extensions would differ only inside `F`. Directly: take `M′ = F·B_R ∖ F` for large `R`. A point
    `y ≠ x` agreeing with `x` on `F·B_R` exists because `x` is not isolated. Then item 1 applies to `x′` (varying on `F`) and `y`
    (varying outside `F·B_R`).
  - Restriction `L_(F∪∂F) → L_(∂F)` is injective, which gives the count. Correct.
- **Item 3.**
  - Windows. With `(g.x)(h) = x(g⁻¹h)`, the join over a left Følner set `F_n` reads `x` on `F_n⁻¹`, which is right Følner. So
    `|E_nB_w ∖ E_n| ≤ Σ_(b∈B_w)|E_nb ∖ E_n| = o(|E_n|)`.
  - An isolated point of `supp μ` has positive mass, so its orbit is finite. Ergodicity then puts `μ` on that orbit, and `h_μ = 0`.
  - Rigidity passes to `S` because an `S`-family is an `X`-family.
  - The variational principle and the ergodic decomposition of entropy for amenable groups are recalled. Correct.
- **Item 4.**
  - `|∂_w F_r| ≤ 2kL` holds because `c_i b = t^e c_(i′)` with `|e| ≤ L`, for finitely many pairs.
  - If there were more than `|A|^(2kL)` points, finitely many pairs of them would be separated on one `F_r`.
  - Then a perfect finite set is empty, and scattered compact metrizable spaces are countable. Correct.
- **Item 5.**
  - (a) Correct: Haar on `K/H`. The fibre map is upper semicontinuous, and on each stratum `{|F| = n}` the uniform measure is
    continuous.
  - (b) Correct: `‖g_*λ_R − λ_R‖ ≤ ∫‖g_*m_R(x) − m_R(gx)‖dμ`, which is Reiter's condition.
  - (c) Two precisions:
    - **P1.** (CC′) quantifies over *topologically free* `X`. As stated, (RA_fin) omits topological freeness. So (RA_fin) ⇒ (CC′) in
      finite fibres, and the converse gives only (RA_fin) for topologically free `X`. The fix is to add "topologically free" to
      (RA_fin), or to state only the implication.
    - **P2.** The commit subject's "finite-fibre case of (RA′) is non-existence" should read "(CC′) / (RA) in finite fibres". (RA′),
      exactness of `Λ`, concerns only non-exact groups. It is implied by (RA_fin) in finite fibres, not equivalent to it. The body's
      item 5(c) and "What this says about (RA′)" are phrased correctly: the cap-coherence route cannot work there.
- **Item 6.**
  - (a) `γ.x ∈ K_Γ` because `Per_Γ` is left `Γ`-invariant. Differences are `2D`-connected, and item 1 applies with
    `M = Per_Γ` across two distinct `2D`-components.
  - (b) `γΔ(x,γ′x) = Δ(γx, γγ′x)`, and `γ` permutes the components, so `γC_Γ = C_Γ`. The action on the `2D`-graph of `C_Γ` is free
    and cocompact, and Švarc–Milnor applies.
  - (c) Nesting uses a `γ ∈ Γ′ ⊆ Γ` with `γ.x ≠ x`. Correct.
- **Credit suggestion.** The amenable variational principle is also due to Stepin–Tagi-Zade and Moulin Ollagnier–Pinchon (recalled).
