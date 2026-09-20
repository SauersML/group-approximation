---
rg: 2
id: tree-grafting-inflations-kill-superlinear-ratio-proof
kind: route
title: Proof that leaf-grafting inflations kill superlinear-ratio coarsening derivatives
target: tree-grafting-inflations-kill-superlinear-ratio-derivatives
requires: [marginal-derivative-amplification-is-sharp-at-log-height]
---

Notation is as in the target. The required claim is used only for the definitions of a
derivative datum, (E′) and thinness, and in the Sharpness remark for "marginal ⇒ thin".
Theorems 1, 2 and 4 and Corollary 3 use nothing else from it.

## Imports from Moore, arXiv:0905.1118v7 (verbatim from the TeX source)

**Partial action (Sec. 3).** "A \emph{partial action} of $G$ on a set $S$ is a partial function
$\cdot: S \times G \to S$ such that: $x \cdot e = x$ for all $x \in S$; $x \cdot g = y$ if and
only if $x = y \cdot g^{-1}$ for all $g \in G$ and $x,y \in S$; $x \cdot (gh) = (x \cdot g) \cdot
h$ for all $g,h\in G$ and all $x \in S$ for which all computations involving $\cdot$ are
defined."

**Weighted Følner sets (Sec. 3).** "$\sum_{\gamma \in \Gamma} \sum_{s \in S} |\mu(s \cdot
\gamma) - \mu (s)| < \varepsilon \sum_{s \in S} \mu(s)$ where we adopt with the conventions that
$\mu (s) = 0$ if $s$ is not in the domain of $\mu$ and $\mu(s \cdot g) = 0$ if $s \cdot g$ is
undefined."

**Trees (Sec. 2).**
- "If $U$ and $V$ are in $\Tcal$, then we will say that $U$ is \emph{dominated by} $V$ if every
  element of $U$ has a extension in $V$."
- "$T/u = \{s : u \tie s \in T\}$."
- "We view a tree diagram as describing a map of sequences defined by $$s_i \tie x \mapsto t_i
  \tie x$$ where $s_i$ and $t_i$ are the $i\Th$ elements of $L$ and $R$ respectively and $x$ is
  any binary sequence."
- The generators, verbatim: "$x_0 = \seq{00} \mapsto \seq{0}, \seq{01} \mapsto \seq{10},
  \seq{1} \mapsto \seq{11}$", and "$x_1 = \seq{0} \mapsto \seq{0}, \seq{100} \mapsto \seq{10},
  \seq{101} \mapsto \seq{110}, \seq{11} \mapsto \seq{111}$". The TeX source sets these as
  `cases` environments.
- The action on trees: "If $T$ is in $\Tcal$ and $f$ is in $F$ with $f$ defined on all of $T$,
  then $T \cdot f$ is the pointwise image of $T$ under $f$. It is easily checked that this results
  in an element of $\Tcal$ and hence this defines a partial right action of $F$ on $\Tcal$."

**Lemma 4.2 (`\label{Folner->trees}`).** "There is a constant $C$ such that if $A \subseteq F$
is a (right) $\varepsilon$-F\o lner set, then there is a weighted $C \varepsilon$-F\o lner set of
trees supported on a subset of $\{R_f : f \in A\}$."

**Interior elements and Definition 5.1.**
- "If $T$ is in $\Tcal$, then the \emph{end points} of $T$ are the maximum and minimum elements
  of $T$. All other elements of $T$ are said to be \emph{interior}."
- "$\partial T$ is the maximum $U \in \Tcal$ (with respect to the order of domination) which is
  dominated by $T$ which satisfies the following \emph{defining conditions}: (1) $U$ contains
  extensions of both $\seq{01}$ and $\seq{10}$; (2) one of the following holds: if $u <_\lex v$
  are interior elements of $U$, then $2 |T/u| \leq |T/v|$; if $u <_\lex v$ are interior
  elements of $U$, then $2 |T/v| \leq |T/u|$; (3) the minimum (respectively the maximum) interior
  element of $U$ terminates with a $\seq{1}$ (respectively with a $\seq{0}$). If no such $U$
  exists, then $\partial T$ is defined to be the trivial tree."

**Lemma `\label{proper_act}`.** "The set $\{T \in \Tcal : \Gamma \textrm{ does not act properly
on }\partial T \}$ is marginal."

## Conventions

- For a finite binary sequence `t` and `f ∈ F` given by a tree diagram `(L, R)`, `t·f` is
  defined iff `t` extends some `s_i ∈ L`, and then `t·f = t_i x` where `t = s_i x`. So `T·f` is
  defined iff every leaf of `T` extends an element of `L`.
- `f` is order-preserving on the leaves: if `u <_lex u'` are leaves of `T` and `T·f` is
  defined, then `u·f <_lex u'·f`. This is because the maps `s_i x ↦ t_i x` preserve `<_lex`
  within each piece, and `L` and `R` are listed in the same order.
- Hence the `i`-th leaf of `T` goes to the `i`-th leaf of `T·f`, and `|T·f| = |T|`.
- Write `bd_γ(μ) = Σ_{s∈S} |μ(s·γ) − μ(s)|`, with Moore's conventions. So `bd = Σ_γ bd_γ`.

## Theorem 1 (Inflation Lemma)

Let `σ : S → S` satisfy `σ(s·γ) = σ(s)·γ` whenever `s·γ` is defined, for `γ ∈ Γ`. In
particular `σ(s)·γ` is then defined. Put `ν = σ_*μ`, `ν(x) = Σ_{σ(s)=x} μ(s)`, and
`P_x = σ^{-1}(x)`. Clearly `ν(S) = μ(S)`.

This differs from Moore's Lemma 3.2 (`\label{Folner_hom_prop}`). That lemma needs `h(s·γ)` and
`h(s)·γ` to be defined together. Here `σ(s)·γ` may be defined while `s·γ` is not, which is
exactly what happens for refinements. The price is the factor 2.

Fix `γ ∈ Γ`.

**Step 1 (points `x` with `x·γ` undefined).** For `s ∈ P_x`, `s·γ` is undefined, since otherwise
`x·γ = σ(s)·γ` would be defined. So the term is
`|0 − ν(x)| = Σ_{s∈P_x} μ(s) = Σ_{s∈P_x} |μ(s·γ) − μ(s)|`, using the convention `μ(s·γ) = 0`.

**Step 2 (points `x` with `x·γ = y` defined).**
- The map `s ↦ s·γ` sends `{s ∈ P_x : s·γ defined}` into `P_y`, since `σ(s·γ) = σ(s)·γ = y`.
- It is injective, because `s·γ = s'·γ` gives `s = (s·γ)·γ^{-1} = s'` by the second axiom of a
  partial action.
- Let `t ∈ P_y` be outside its image. If `t·γ^{-1} = s` were defined, then `s·γ = t` and
  `σ(s)·γ = σ(t) = y = x·γ`, so `σ(s) = x` by the same axiom. That puts `t` in the image, a
  contradiction. So every `t ∈ P_y` outside the image has `t·γ^{-1}` undefined.
- Therefore, with the three sums
  - `Σ_1 = Σ_{s∈P_x, s·γ def} |μ(s·γ) − μ(s)|`,
  - `Σ_2 = Σ_{s∈P_x, s·γ undef} μ(s)`,
  - `Σ_3 = Σ_{t∈P_y, t·γ^{-1} undef} μ(t)`,

  we get `|ν(y) − ν(x)| ≤ Σ_1 + Σ_2 + Σ_3`.

**Step 3 (summing over `x`).**
- The fibres `P_x` are disjoint, so the `Σ_1` and `Σ_2` parts from Steps 1–2 sum to at most
  `Σ_s |μ(s·γ) − μ(s)| = bd_γ(μ)`. The undefined terms are exactly the ones counted with the
  convention `μ(s·γ) = 0`.
- The map `x ↦ x·γ` is injective, so the fibres `P_y` in `Σ_3` are disjoint as `x` varies.
  Hence the `Σ_3` parts sum to at most `Σ_{t : t·γ^{-1} undef} μ(t) ≤ bd_{γ^{-1}}(μ)`.
- So `bd_γ(ν) ≤ bd_γ(μ) + bd_{γ^{-1}}(μ)`. Summing over the symmetric set `Γ` gives
  `bd(ν) ≤ 2·bd(μ)`. ∎

Injectivity of `σ` was never used. The sums are finite, because `μ` is finitely supported and
each point has at most one `γ`-image and one `γ`-preimage.

## Theorem 2 (grafting inflations)

Fix trees `P_{i,n} ∈ 𝒯` for `0 ≤ i < n`. For `T` with leaves `u_0 <_lex … <_lex u_{n−1}`, put
`σ(T) = {u_i w : i < n, w ∈ P_{i,n}}`. This is a complete prefix code, since it replaces the
leaf `u_i` by the tree `P_{i,n}` hung below it.
- `P_{i,n} = {0,1}^{j(n)}` for all `i` gives `σ_j`.
- `P_{k,n} = P`, with `P_{i,n}` trivial for `i ≠ k`, grafts `P` at the `k`-th leaf from the
  left. The choice `k ↦ n − 1 − k` grafts from the right.

**Claim.** If `T·γ` is defined, then `σ(T)·γ` is defined and equals `σ(T·γ)`.

*Proof.*
- Each leaf `u_i w` of `σ(T)` extends `u_i`, and `u_i` extends some domain piece `s` of `γ`.
  So `(u_i w)·γ = (u_i·γ) w` is defined.
- By the Conventions, `T·γ` has `n` leaves and its `i`-th leaf is `u_i·γ`.
- Hence `σ(T)·γ = {(u_i·γ) w : w ∈ P_{i,n}} = σ(T·γ)`. ∎

## Corollary 3

Let `B` be `c`-thin, let `σ` be as in Theorem 2, and let `ν = σ_*μ`.
- By Theorem 1, `ν(B) ≤ c·bd(ν) ≤ 2c·bd(μ)`.
- If `μ` is weighted `ε`-Følner, then `bd(μ) < ε μ(𝒯)`, so `ν(B) ≤ 2cε·μ(𝒯)`.
- Suppose `B ⊇ σ(𝒯)`. Then `μ(𝒯) = ν(σ(𝒯)) ≤ ν(B) ≤ 2c·bd(μ)` for every finitely supported
  `μ ≥ 0`. So no weighted `ε`-Følner set of trees exists with `ε ≤ 1/(2c)`.
- If `F` were amenable, it would have right `ε`-Følner sets for every `ε > 0`. Imported Lemma
  4.2 would then give weighted `Cε`-Følner sets of trees for every `ε`, a contradiction. So `F`
  is non-amenable, and `𝒯` itself is `2c`-thin. ∎

## Theorem 4 (class kill)

**`j(n)` is well defined and nondecreasing.**
- Fix `n`. Since `sup φ(x)/x = ∞`, choose `x_0 ≥ 1` with `φ(x_0) > 16n·x_0`.
- Let `m = 2^{j−3}` be the least power of 2 with `m ≥ x_0`, taking `j ≥ 3`. Then `m < 2x_0`.
- By monotonicity, `φ(m) ≥ φ(x_0) > 16n·x_0 > 8n·m = 2^j·n`. So the set defining `j(n)` is
  non-empty.
- The condition `φ(2^{j−3}) > 2^j·n` only gets harder as `n` grows, so `j(n)` is nondecreasing.

**Size facts for `S = δ^j(T)`, with `|T| = n` and `j = j(n)`.**
- Every leaf of `S` has length `≥ j ≥ 3`, and `|S| = 2^j·n`.
- A node `x` of `S` at depth `d ≤ j` lies strictly above the grafted layer or inside it. In
  either case `x` is a prefix of some `u w` with `u ∈ T`, and `S/x` contains a complete binary
  tree of depth `j − d`. So `|S/x| ≥ 2^{j−d}`.
- In particular, `|S/01| ≥ 2^{j−2}`, `|S/10| ≥ 2^{j−2}`, and `|S/y| ≤ 2^j·n` for every `y`.
- Every leaf of `S` has length `≥ 3`, so it extends one of `00, 01, 1` and one of `0, 100, 101,
  11`, and likewise for the domains of `x0^{-1}`, `x1^{-1}`. So `S·γ` is defined for all
  `γ ∈ Γ`.

**Claim: `S ∉ A`.** Suppose `S ∈ A`, and let `U = ∂S`, dominated by `S`.
- **(E′) forces a shape.** `S·x0` is defined, so by (E′) `U·x0` is defined. Then every leaf of
  `U` extends `00`, `01` or `1`, so `U` splits the root and `0`. Likewise `U·x1` is defined, so
  every leaf of `U` extends `0`, `100`, `101` or `11`, and `U` splits `1` and `10`.
- **The crossing pair is interior.** So `U` has leaves under `00`, `01`, `10` and `11`. The
  minimum leaf of `U` extends `00` and the maximum extends `11`. Hence every leaf of `U` under
  `01` or `10` is interior.
- Let `a_1 <_lex … <_lex a_r` be the leaves of `U` under `01`, and `b_1 <_lex … <_lex b_q` those
  under `10`, with `r, q ≥ 1`. Then `a_r` and `b_1` are consecutive leaves of `U`.
- Since `U` is dominated by `S`, the leaves of `S` below `01` are partitioned by the `a_i`. So
  `Σ_i |S/a_i| = |S/01| ≥ 2^{j−2}`, and similarly `Σ_i |S/b_i| = |S/10| ≥ 2^{j−2}`.

**Increasing case.** Here `|S/v| ≥ φ(|S/u|) ≥ 2|S/u|` for consecutive interior `u <_lex v`.
- Along `a_1, …, a_r` this gives `|S/a_i| ≤ 2^{i−r}|S/a_r|`. Hence
  `|S/01| ≤ |S/a_r|·Σ_{k≥0} 2^{−k} = 2|S/a_r|`, and `|S/a_r| ≥ 2^{j−3}`.
- Then `2^j·n ≥ |S/b_1| ≥ φ(|S/a_r|) ≥ φ(2^{j−3}) > 2^j·n`, a contradiction.

**Decreasing case.** Here `|S/u| ≥ φ(|S/v|) ≥ 2|S/v|` for consecutive interior `u <_lex v`.
- Along `b_1, …, b_q` this gives `|S/b_i| ≤ 2^{1−i}|S/b_1|`. Hence `|S/10| ≤ 2|S/b_1|`, and
  `|S/b_1| ≥ 2^{j−3}`.
- Then `2^j·n ≥ |S/a_r| ≥ φ(|S/b_1|) ≥ φ(2^{j−3}) > 2^j·n`, a contradiction.

So `σ_j(𝒯) ⊆ B`. By Corollary 3, if `B` is `c`-thin then `F` is non-amenable. In that case
`𝒯` is thin, and `H_k` holds with `A = ∅`, so the datum proves nothing new. ∎

Only consecutive pairs were used. Data that impose the ratio condition on all pairs of interior
leaves, as Moore does, belong to the class.

**Moore-type maximal coarsening with `φ`.** Let `∂_φ T` be the maximum `U` dominated by `T`
satisfying Moore's conditions (1)–(3), with (2) replaced by the `φ`-version on consecutive
interior elements, and the trivial tree if no such `U` exists.
- Any such `U` for `S = σ_j(T)` contains extensions of `01` and `10`. So it splits the root, `0`
  and `1`, its minimum leaf lies under `00`, and its maximum leaf lies under `11`.
- So the leaves under `01` and `10` are interior, and the two computations above apply verbatim.
  They used only that these leaves are interior, not that `U` splits `10`.
- Hence no `U` exists, and `∂_φ S` is trivial. Since `S·x0` is defined but the trivial tree
  `{∅}·x0` is not (the empty sequence extends none of `00, 01, 1`), no good set satisfying (E′)
  contains `S`.

## Sharpness at linear `φ`

- For `φ(x) = 2x`, Moore's `∂` with `A = {T : Γ acts properly on ∂T}` lies in the class. It is
  dominated by `T` by Definition 5.1, and (2) with all pairs implies the consecutive form.
- It is a derivative datum by his Lemma 5.5, as recorded in the required claim.
- Its bad set is marginal by the imported lemma `proper_act`, hence thin. The required claim
  records "Every set that is marginal in Moore's sense (Def. 3.3) is `c`-thin for some `c`, by
  his Lemma 3.10."
- So the hypothesis `sup φ(x)/x = ∞` cannot be dropped, unless `F` is non-amenable. For Moore's
  datum `B` is thin, so by Corollary 3, `B ⊉ σ(𝒯)` for every grafting inflation `σ` whenever `F`
  is amenable. The proof shows where the argument breaks: `j(n)` does not exist when
  `φ(x) ≤ 8n·x` for all `x`.

## Computation

`experiments/tree-grafting-inflations-2026-09-17/check_inflation.py`, output in `output.txt`:
- 120 of 120 equivariance instances hold for each of four inflations, on all trees with at most
  6 leaves;
- 300 random measures satisfy `bd(σ_*μ) ≤ 2bd(μ)`, with worst observed ratio 1.61;
- a dynamic program over nodes finds no admissible `U` (splitting the root, `0`, `1` and `10`,
  with the `φ`-chain on interior leaves in either direction) on `δ^{j(n)}T`, for
  `φ = max(2x, x²)` and all `T` with `n ≤ 5` leaves, where `j(n) = 7, 8, 8, 9, 9`.

The theorem does not depend on the computation.
