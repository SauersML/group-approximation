# Locally free groups: first L2-Betti number, cost dichotomy, and the shape of a counterexample

Worker `swarm-0917-w2-fp-pull-2`, September 17, 2026. Goal
`fpbs-fixed-price-universal`, hole `fpbs-fixed-price-non-amenably-generated-from-fg`.

## 0. Summary

A group is *locally free* if every finitely generated subgroup is free. Such a
group is torsion-free. For a countably infinite locally free group `Γ` and a
finite set `F ⊆ Γ`, put

    c_F(Γ) = min { rk L : L ≤ Γ finitely generated, F ⊆ L },     c*(Γ) = sup_F c_F(Γ) ∈ [0, ∞].

For finite `F ⊇ F_0`, where `⟨F_0⟩ ≠ 1`, every such `L` is a nontrivial free
group. A free group of rank `r ≥ 1` has fixed price `r` (Gaboriau 2000). So
`c*` agrees with the `c*` of `research/artifacts/fpbs/docs/fixed-price-countable-passage.md` §4.

**Theorem L.** If `Γ` is countably infinite and locally free, then
`β_1^(2)(Γ) = c*(Γ) − 1`.

**Theorem P.** If `Γ` is countably infinite and locally free, then every free
p.m.p. action `a` of `Γ` satisfies

    C(a) ∈ { c*(Γ), ∞ }     and     PC(a) ≤ c*(Γ).

If some free action has finite cost, then `C(Γ) = c*(Γ)` and every free action
has pseudocost exactly `c*(Γ)`.

**Corollary Q.** For a countably infinite locally free group `Γ`, the following
are equivalent:
- `Γ` has fixed price;
- `Γ` does not have one free action of finite cost and another of infinite cost.

A locally free group without fixed price has shape (B) of Theorem G of the
passage artifact, and never shape (A). This holds unconditionally, without the
hypothesis H. Condition (L) of Theorem E (`c* ≤ C(Γ)`) holds for every locally
free group, by Theorem L and Gaboriau's inequality. For the test group `Γ_mal` (`c* = 2`), every free action has cost
2 or ∞. So `Γ_mal` has fixed price iff condition (U) holds, or else every free
action has infinite cost.

Both theorems are unconditional. Theorem P needs no hypothesis on finitely
generated groups: free groups have fixed price by Gaboriau, and the only
inputs are Theorem L, Gaboriau's inequality and Tucker-Drob's pseudocost
results.

## 1. Imports (verbatim)

**[JZ]** A. Jaikin-Zapirain, *Free groups are L2-subgroup rigid*,
arXiv:2403.09515v2, TeX source `l2subgrouprigid25.tex`, read September 17,
2026.
- Definitions: "A finitely generated subgroup $H$ of a free group $F$ is called
  {\bf compressed} if for any finitely generated subgroup $L$ of $F$ containing
  $H$, $\rk(H)\le \rk(L)$, and it is called {\bf inert} if for any finitely
  generated subgroup $L$ of $F$, $\rk(H\cap L)\le \rk(L)$."
- "We also say that $H$ is {\bf $L^2$-independent} in $F$ if the canonical map
  $$\D(F)\otimes_{\Q[H]}I_{\Q[H]}\to \D(F)\otimes_{\Q[F]}I_{\Q[F]}$$ is
  injective."
- Here $\D(F)$ is given by: "the strong Atiyah conjecture over $\mathbb{Q}$
  (which states that the division closure $\mathcal D(G)$ of $\mathbb{Q}[G]$ in
  $\mathcal U(G)$ is a division ring)". Also: "In this paper we make use of
  Linnell's solution of the Strong Atiyah Conjecture for free groups".
- Cor `inertcompressed`: "Let $F$ be a free group and $H$ a finitely generated
  subgroup. Then the following are equivalent: (1) $H$ is compressed in $F$;
  (2) $H$ is inert in $F$; (3) $H$ is $L^2$-independent in $F$."

**[L]** W. Lück, *L2-invariants from the algebraic point of view*,
arXiv:math/0310489, TeX source `ltwoalg.tex`, read September 17, 2026.
- Definition (Division and rational closure) and: "The ring $\cald(G)$
  appearing in the fundamental square [...] is the rational closure of
  $\bbC G$ in $\calu(G)$."
- Definition (Linnell's class): "Let $\calc$ be the smallest class of groups,
  which contains all free groups and is closed under directed unions and
  extensions with elementary amenable quotients."
- Linnell's Theorem: "Let $G$ be a group in $\calc$. Suppose that there exists
  $d \in \bbZ$, $d \ge 1$ such that the order of every finite subgroup of $G$
  divides $d$. Then the ring theoretic version of the Atiyah Conjecture [...]
  for $G$ and hence the Atiyah Conjecture [...] for $(G,d,\bbC)$ are true."
- Remark (torsion-free case): "Let $G$ be a torsion-free group. Then the ring
  theoretic version of the Atiyah Conjecture reduces to the statement that
  $\cald(G)$ is a skewfield. In this case we can assign to every
  $\cald(G)$-module $N$ its dimension $\dim_{\cald(G)}(N) \in \bbZ \amalg
  \{\infty\}$ in the usual way and we get for every $\bbC G$-module $M$
  $\dim_{\caln(G)}(\caln(G) \otimes_{\bbC G} M) = \dim_{\calu(G)}(\calu(G)
  \otimes_{\bbC G} M) = \dim_{\cald(G)}(\cald(G) \otimes_{\bbC G} M)$."

**[FL]** S. P. Fisher and Y. Lodha, arXiv:2608.25988v1, TeX source, read
September 17, 2026. Lemma `lem:direct-union-homology`: "Suppose $G_0\leqslant
G_1\leqslant \ldots $ are groups, let $G=\bigcup_{i\in \N}G_i$, and let $M$ be
a fixed right $\C[G]$-module. Then $\homol_n(G;M)=\varinjlim_{i\in\N}
\homol_n(G_i;M)$". The paper attributes it to Brown, *Cohomology of Groups*,
Exercise V.5.3(a).

**[LN]** Graph node `lueck-dimension-additivity-cofinality-and-induction`
(ESTABLISHED): additivity, cofinality (directed unions of submodules), and
induction `dim_{N(G)}(N(G) ⊗_{N(H)} P) = dim_{N(H)} P` for `H ≤ G`.

**[G]** Graph node `fpbs-amen2-betti-cost-input` (ESTABLISHED): for an infinite
countable group, `β_1^(2)(Γ) ≤ C(a) − 1` for every free p.m.p. action `a`
(Gaboriau lecture notes Thm 2.64).

**[TD]** R. Tucker-Drob, *Shift-minimal groups, fixed price 1, and the unique
trace property*, arXiv:1211.6395, TeX source
`4_15_2012_Shift-minimal_groups.tex`, read September 17, 2026.
- Def 6.6 `def:pseudo`: "Let $E_0,E_1,E_2,\dots$, and $E$ be m.p.\ countable
  Borel equivalence relations on $(X,\mu )$. The sequence $(E_n)_{n\in \N}$ is
  called an \emph{exhaustion of $E$}, denoted $(E_n)_{n\in \N}\nnearrow E$, if
  $E_0\subseteq E_1\subseteq \cdots$, and $E=\bigcup _n E_n$. The
  \emph{pseudocost} of $E$, denoted $PC_\mu (E)$, is defined by $PC_\mu (E) =
  \inf \{ \liminf _n C_\mu (E_n) \csuchthat (E_n)_{n\in \N}\nnearrow E \}$. If
  $\bm{a}$ is a m.p.\ action of a countable group $\Gamma$ then define the
  pseudocost of $\bm{a}$ by $PC(\bm{a}):=PC_\mu (E_a)$."
- Cor 6.8 `cor:PC=C`: "Let $E$ be a m.p.\ countable Borel equivalence relation
  on $(X,\mu )$. (1) If $C_\mu (E) <\infty$ then $PC_\mu (E)=C_\mu (E)$. (2) If
  $E$ is treeable then $PC_\mu (E)=C_\mu (E)$. (3) $PC_\mu (E)=1$ if and only
  if $C_\mu (E) =1$."
- Prop 6.26 `prop:analogue`: "Let $\Gamma$ be a countably infinite group. (1)
  Suppose that $C(\Gamma )<\infty$. Then for any free m.p.\ action $\bm{b}$ of
  $\Gamma$, and any exhaustion $(E_n)_{n\in \N}$ of $E_b$, we have $\liminf
  _{n\ra\infty} C_\mu (E_n) \geq C(\Gamma )$. Hence $PC(\Gamma )=C(\Gamma )$."

## 2. A compressed exhaustion

**Lemma 2.1.** Let `Γ` be countably infinite and locally free. There are finite
sets `T_0 ⊆ T_1 ⊆ ⋯` and finitely generated subgroups `Δ_0 ≤ Δ_1 ≤ ⋯` such that
1. `T_n ⊆ Δ_n` and `rk Δ_n = c_{T_n} =: r_n ≥ 1`;
2. `⋃_n Δ_n = Γ` and `sup_n r_n = c*(Γ)`;
3. for all `n ≤ m`, `Δ_n` is compressed in `Δ_m`, and hence (by [JZ]) is
   `L²`-independent in `Δ_m`.

*Proof.* Enumerate `Γ = {g_1, g_2, …}` and let `T_0 = {g}` with `g ≠ 1`. Given
`T_n`, choose a finitely generated `Δ_n ⊇ T_n` of rank `c_{T_n}`, with a finite
generating set `S_n`. Put `T_{n+1} = T_n ∪ S_n ∪ {g_{n+1}}`.
- `Δ_{n+1} ⊇ T_{n+1} ⊇ S_n`, so `Δ_{n+1} ⊇ Δ_n`.
- `g_n ∈ Δ_n`, so the union is `Γ`.
- `Δ_n ∋ g ≠ 1` and `Γ` is torsion-free, so `r_n ≥ 1`.
- If `F` is finite then `F ⊆ T_n` for some `n`. Every `L ⊇ T_n` contains `F`,
  so `c_F ≤ c_{T_n}`. Hence `c* ≤ sup_n r_n ≤ c*`.
- Let `n ≤ m` and let `L` be finitely generated with `Δ_n ≤ L ≤ Δ_m`. Then
  `L ⊇ T_n`, so `rk L ≥ c_{T_n} = rk Δ_n`. So `Δ_n` is compressed in the free
  group `Δ_m`. [JZ] Cor `inertcompressed` gives `L²`-independence. ∎

## 3. L2-independent inclusions kill no L2-homology

Let `G` be a group, `V` a right `CG`-module, and `H ≤ F ≤ G` with `H` free on
`h_1, …, h_p` and `F` free on `f_1, …, f_q`.
- The augmentation ideal `I_{CH}` is a free left `CH`-module on the `h_i − 1`
  (Brown I.4.4). So `0 → I_{CH} → CH → C → 0` is a free resolution and
  `H_1(H; V) = ker(V ⊗_{CH} I_{CH} → V) = ker(V^p → V, (v_i) ↦ Σ_i v_i(h_i − 1))`.
- Write `h_i − 1 = Σ_j a_{ij}(f_j − 1)` with `a_{ij} ∈ Z[F]` (Fox derivatives),
  and let `A = (a_{ij})`. The inclusion-induced map
  `φ : H_1(H; V) → H_1(F; V)` is the restriction of
  `θ_V : V^p → V^q, v ↦ vA`. The augmentation `V^q → V` composed with `θ_V`
  is the augmentation `V^p → V`. So `ker φ = ker θ_V`.
- Let `M = CF^q / CF^p A`, a finitely presented left `CF`-module. Right
  exactness of `⊗` gives `coker θ_V = V ⊗_{CF} M`.

**Lemma 3.1.** If `H` is finitely generated and `L²`-independent in the
finitely generated free group `F ≤ G`, then
`dim_{N(G)} ker( H_1(H; N(G)) → H_1(F; N(G)) ) = 0`.

*Proof.*
1. Let `D_Q(F)` be the division closure of `Q[F]` in `U(F)` ([JZ]), and
   `D(F)` the rational closure of `CF` in `U(F)` ([L]). By Linnell's Theorem
   ([L]; `F` is in class `C` and torsion-free), `D(F)` is a skew field. A
   subring of `U(F)` that is a skew field is division closed in `U(F)`. So
   `D(F) ⊇ D_Q(F)`.
2. `L²`-independence says `θ_{D_Q(F)}` is injective. Here
   `D_Q(F) ⊗_{Q[H]} I_{Q[H]} = D_Q(F)^p`, since `I_{Q[H]}` is free on the
   `h_i − 1`, and the map is `v ↦ vA`. So the rows of `A` are left linearly
   independent over the skew field `D_Q(F)`.
3. Gaussian elimination over `D_Q(F)` gives `P ∈ GL_p(D_Q(F))` and
   `Q ∈ GL_q(D_Q(F))` with `PAQ = [I_p | 0]`. These are also invertible over
   `D(F)`, so `θ_{D(F)}` is injective. Hence
   `dim_{D(F)}(D(F) ⊗_{CF} M) = q − p`.
4. [L] Remark gives `dim_{N(F)}(N(F) ⊗_{CF} M) = q − p`. Since
   `N(G) ⊗_{CF} M = N(G) ⊗_{N(F)} (N(F) ⊗_{CF} M)`, induction ([LN]) gives
   `dim_{N(G)}(N(G) ⊗_{CF} M) = q − p`.
5. Additivity ([LN]) on the exact sequence
   `0 → ker θ → N(G)^p → N(G)^q → N(G) ⊗_{CF} M → 0` of left `N(G)`-modules gives
   `q − p = q − (p − dim ker θ)`. So `dim ker θ = 0`, and `ker φ = ker θ`. ∎

**Lemma 3.2.** For `H ≤ G` free of rank `p ≥ 1`, `dim_{N(G)} H_1(H; N(G)) = p − 1`.

*Proof.* The exact sequence `0 → H_1(H; N(G)) → N(G)^p → N(G) → H_0(H; N(G)) → 0`
and additivity give `dim H_1 = p − 1 + dim H_0`. Now
`H_0(H; N(G)) = N(G) ⊗_{CH} C = N(G) ⊗_{N(H)} (N(H) ⊗_{CH} C)`, so induction
gives `dim H_0 = dim_{N(H)}(N(H) ⊗_{CH} C)`. By [L] Remark for `H`, this is
`dim_{D(H)}(D(H) ⊗_{CH} C) = dim_{D(H)} D(H)/D(H)·I_{CH}`. But `h_1 − 1 ≠ 0`
lies in `I_{CH}` and is invertible in the skew field `D(H)`. So the module is
0. ∎

(Lemma 3.2 also follows from the consequence line of [LN] and the classical
`β_1^(2)(F_p) = p − 1`.)

## 4. Proof of Theorem L

Take the exhaustion of Lemma 2.1, and write `N = N(Γ)`. By [FL] Lemma,
`H_1(Γ; N) = colim_n H_1(Δ_n; N)` along the inclusion-induced maps
`φ_{n,m}`. Let `ψ_n : H_1(Δ_n; N) → H_1(Γ; N)` be the canonical maps.
1. For a sequential colimit of modules, `ker ψ_n = ⋃_{m ≥ n} ker φ_{n,m}`, an
   increasing union. By Lemma 2.1(3) and Lemma 3.1, each `ker φ_{n,m}` has
   dimension 0. Cofinality ([LN]) gives `dim ker ψ_n = 0`.
2. By Lemma 3.2 and additivity, `dim im ψ_n = r_n − 1`.
3. `H_1(Γ; N)` is the increasing union of the submodules `im ψ_n`. Cofinality
   gives `β_1^(2)(Γ) = dim_N H_1(Γ; N) = sup_n (r_n − 1) = c* − 1`. ∎

**Checks.**
- `Γ = F_r`: `c* = r`, and `β_1^(2) = r − 1`.
- `Γ = Q` (locally cyclic): `c* = 1`, and `β_1^(2) = 0`.
- Fisher–Lodha's `Γ_n` has `β_1^(2) = n` ([FL] Thm 1.2). So by Theorem L,
  `c*(Γ_n) = n + 1`, which matches their rank-`(n + 1)` stages.
- For `Γ_mal`, `c* = 2` (passage artifact §5.1), so `β_1^(2)(Γ_mal) = 1`.

**Remark (what fails without compression).** The proof uses only that some
exhaustion has `L²`-independent inclusions. Without them, the colimit can lose
`L²`-homology. Example: `H = ⟨a, bab⁻¹, b²⟩` has index 2 and rank 3 in
`F = ⟨a, b⟩`. Then `dim H_1(H; N) = 2 > 1 = dim H_1(F; N)`, so `ker φ` has
positive dimension. An arbitrary chain of finitely generated subgroups
exhausting `Γ` therefore does not compute `β_1^(2)`, but the compressed chain
of Lemma 2.1 does.

## 5. Proof of Theorem P and Corollary Q

Let `a` be a free p.m.p. action of `Γ` on `(X, μ)`. Take `Δ_n` from Lemma 2.1.
1. **Upper bound.** `a|Δ_n` is free. The `r_n` generators of `Δ_n` act as
   automorphisms of `X` and generate the orbit relation `E_{a|Δ_n}`, so
   `C(E_{a|Δ_n}) ≤ r_n ≤ c*`. The relations `E_{a|Δ_n}` increase and their
   union is `E_a`, so they form an exhaustion. [TD] Def 6.6 gives
   `PC(a) ≤ liminf C(E_{a|Δ_n}) ≤ c*`.
2. **Lower bound.** [G] and Theorem L give `C(a) ≥ 1 + β_1^(2)(Γ) = c*`.
3. **Dichotomy.** If `C(a) < ∞`, then [TD] Cor 6.8(1) gives
   `C(a) = PC(a) ≤ c* ≤ C(a)`. So `C(a) = c*`. Otherwise `C(a) = ∞`.
   (If `c* = ∞`, step 2 already forces `C(a) = ∞`.)
4. **Pseudocost when some cost is finite.** If some free action has finite
   cost, step 3 gives `C(Γ) = c* < ∞`. [TD] Prop 6.26(1) gives
   `PC(b) ≥ C(Γ) = c*` for every free `b`, and step 1 gives `PC(b) ≤ c*`. ∎

*Corollary Q.* By Theorem P the set of free-action costs is contained in
`{c*, ∞}`. So fixed price fails iff both values occur. ∎

**Consequences for the passage artifact.**
- In Theorem G, `1 + β_1(Γ) ≤ C(Γ) ≤ PC(s_Γ) ≤ c*(Γ)` collapses to equalities
  for locally free `Γ` with `C(Γ) < ∞`, by Theorem L. So shape (A) is
  impossible there, and (L) holds.
- A locally free group without fixed price has `C(Γ) = c* < ∞` and a free
  action `b` with `C(b) = ∞ > c* = PC(b)`. This is a positive, free-action
  answer to [TD] Q 7.6 (`Q:unions`). Conversely, any free-action instance of
  Q 7.6 at a locally free group that also has a finite-cost free action refutes
  fixed price.
- For `Γ_mal`, every free action has cost 2 or ∞. Whether `Γ_mal` has fixed
  price is exactly whether costs 2 and ∞ both occur.

## 6. Where this leaves the hole (not established)

The remaining statement for locally free groups, recorded as the OPEN node
`fpbs-locally-free-free-actions-have-finite-cost`: every free p.m.p. action of
a countable locally free group `Γ` with `c*(Γ) < ∞` has finite cost. By
Theorem P it implies that every locally free group has fixed price `c*`, and
then `β_1^(2)(Γ) + 1` equals the fixed price. Routes that do not work
directly:
- **Abért–Weiss plus weak-containment monotonicity.** Cost monotonicity under
  weak containment (`cost-weak-containment-monotonicity-citation`) is quoted
  for finitely generated groups only. For arbitrary groups, the passage
  artifact (§1, citing [TD] Cor 6.20) records monotonicity only for
  pseudocost, and Theorem P already determines pseudocost. So this route gives
  nothing beyond Theorem P.
- **Proposition F anchors.** A locally free group `Γ` that is neither finitely
  generated nor locally cyclic has no infinite finitely generated normal
  subgroup `Λ`. Suppose it had one. A nontrivial finitely generated normal
  subgroup of a free group has finite index (Karrass–Solitar). So for every
  finitely generated `Δ ⊇ Λ`, the index is finite.
  - If `rk Λ = 1`, every such `Δ` is cyclic, and `Γ` is locally cyclic.
  - Otherwise, Schreier's formula gives
    `[Δ : Λ] = (rk Λ − 1)/(rk Δ − 1) ≤ rk Λ − 1`. Then `Λ` has finite index in
    `Γ`, and `Γ` is finitely generated.

  (Commensurated and chain anchors were not analyzed in general. `Γ_mal` has
  none, by passage artifact §5.1.)
- **Treeability.** If `E_a` is treeable then `C(a) = PC(a) ≤ c*` by [TD] Cor
  6.8(2). So an infinite-cost free action of a locally free group is never
  treeable. This matches Theorem G(B).

A counterexample to the finite-cost statement is a locally free group `Γ` with
`c* < ∞` and a free action of infinite cost. By Theorem P, its orbit relation
is an increasing union of relations of cost at most `c*` whose union has
infinite cost. This is exactly a free-action instance of Tucker-Drob's Q 7.6 (and of
Gaboriau's lecture-notes Q 2.66, as cited in the passage artifact), in a class
where `β_1` is pinned to `c* − 1`.
