---
rg: 2
id: ambient-decomposition-kun-thom-normalization-audit
kind: route
title: Kun--Thom Theorem 4.1 uses the ambient group only through a Poincare partition of the given representation, and that partition is generator-independent
target: ambient-decomposition-kun-thom-normalization
requires: []
artifacts:
  - research/artifacts/kun-thom-2608-06222-section4-ambient-audit.md
  - research/artifacts/kun-thom-2608-06222-verified.md
  - GroupApproximation/KunThom/CompressorNormalizationAssembly.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyCore.lean
---

**Proof import with an audit.** This route imports the *proof* of Kun–Thom Theorem 4.1
(arXiv:2608.06222v1), not only its statement. It adds two short lemmas that are proved here
in full.

**Trust surface.** It is the one that `kun-thom-sofic-centralizer-normalization-citation`
already accepts: an unrefereed preprint. The audit checks *which hypotheses* each step of that
proof consumes. It does not re-verify the correctness of the steps, which the graph already
trusts through the Theorem 4.1 import.

The verbatim source excerpts, with line numbers in the arXiv e-print `secondpaper.tex`, are in
`research/artifacts/kun-thom-2608-06222-section4-ambient-audit.md`. Excerpt letters (A)–(J)
below refer to that file.

## Setting and notation

The hypotheses are those of (KT\*):
- `Gamma` is Kazhdan and infranormal in a finitely generated group `H`;
- `sigma : H -> S_U = prod_U Sym(Y_n)` is a sofic representation, with lifts
  `sigma_n(g) in Sym(Y_n)`;
- `T` is a finite generating set of `H`.

Recall the decomposition hypothesis on `T`. There are edited graphs `E'_n` on `Y_n` such that:
- `|E'_n Δ E_n(T)| = o_U(|Y_n|)`, where `E_n(T)` is the multiset of edges
  `{x, sigma_n(t)x}` for `t ∈ T` and `x ∈ Y_n`;
- the connected components of `E'_n` each have Cheeger constant `>= h > 0`.

For `f : Y_n -> R` and a finite `R ⊂ H`, put

```text
V_R(f) = sum_{r in R} sum_{x in Y_n} |f(sigma_n(r) x) - f(x)|.
```

A *median* of `f` on a finite set `A` is taken for the uniform vertex weight, as in
Lemma 2.3 (excerpt J).

**Definition (ambient Poincaré partition).** An *ambient Poincaré partition* for `(sigma, R)`
is a sequence of partitions `𝒜_n` of `Y_n`, together with a constant `c > 0` and numbers
`ε_n ->_U 0`, such that the following hold. Write `A_n(x)` for the cell of `x`.
- **(AP1)** `|{ x : A_n(sigma_n(r)x) != A_n(x) for some r in R }| <= ε_n |Y_n|`.
- **(AP2)** For every `f : Y_n -> [0,1]` and every choice of medians `m_A` of `f|_A`,
  `A ∈ 𝒜_n`:

  ```text
  c · sum_{x in Y_n} |f(x) - m_{A_n(x)}|  <=  V_R(f) + ε_n |Y_n|.
  ```

## Step 1. The decomposition hypothesis gives an ambient Poincaré partition for `(sigma, T)`

Let `𝒜_n` be the set of vertex sets of the components of `E'_n`, and put `c = h` and
`e_n = |E'_n Δ E_n(T)|`.

**(AP1).** Take an original edge `{x, sigma_n(t)x}` that lies in `E'_n`. It joins two vertices
of one component. So every `x` counted in (AP1) is an endpoint of an edge of
`E_n(T) \ E'_n`. There are at most `e_n = o_U(|Y_n|)` such `x`.

**(AP2).** Let `A` be a component and `m_A` a median of `f|_A`. Lemma 2.3 (excerpt J) applied
to the graph `E'_n|_A` gives

```text
h · sum_{x in A} |f(x) - m_A|  <=  sum_{{x,y} in E'_n, x,y in A} |f(x) - f(y)|.
```

Sum over the components; every edge of `E'_n` lies in exactly one of them. The right side
becomes the sum over all of `E'_n`. The edges of `E'_n` form a sub-multiset of `E_n(T)` plus at
most `e_n` extra edges, and `|f(x) - f(y)| <= 1` for `f` with values in `[0,1]`. So that sum is
at most `sum_{E_n(T)} |f(x) - f(y)| + e_n <= V_T(f) + e_n`.

A component with one vertex contributes `0` on both sides, so its Cheeger constant is
irrelevant. □

## Step 2. Generator independence

**Lemma.** Let `R, R'` be finite generating sets of `H`. An ambient Poincaré partition for
`(sigma, R)` is also one for `(sigma, R')`, with the same cells and a smaller constant `c'`.

*Word paths.* Fix `g ∈ H` and a word `g = r_1^{e_1} ... r_L^{e_L}` with `r_j ∈ R` and
`e_j = ±1`. Starting from `x`, define `y_0 = x` and `y_j = sigma_n(r_j)^{e_j} y_{j-1}`.

`sigma` is a homomorphism into `S_U`. So the Hamming distance between `sigma_n(g)` and
`sigma_n(r_1)^{e_1} ... sigma_n(r_L)^{e_L}` tends to `0` along `U`. Hence there is a set
`B_n(g)` with `|B_n(g)| = o_U(|Y_n|)` such that `sigma_n(g)x = y_L` for `x` outside it.

For each `j`, the map `x -> y_j` is a permutation of `Y_n`.

*(AP1) for `R'`.* Let `r' ∈ R'`, with a word of length `L` in `R^{±1}`, and let `x` lie
outside `B_n(r')`. If `A_n(sigma_n(r')x) != A_n(x)`, then some step changes the cell,
`A_n(y_j) != A_n(y_{j-1})`.
- If `e_j = +1`, then `y_{j-1}` is an (AP1)-exceptional point for `R`.
- If `e_j = -1`, then `y_{j-1} = sigma_n(r_j) y_j`, so `y_j` is one.

Each of the maps `x -> y_{j-1}` and `x -> y_j` is a permutation. So at most `2L ε_n |Y_n|`
starting points `x` see a crossing. Summing over the finitely many `r' ∈ R'` gives (AP1) with
an `o_U(1)` constant.

*(AP2) for `R'`.* Let `r ∈ R`, with a word of length `<= L'` in `R'^{±1}`. For `x` outside
`B_n(r)`, the triangle inequality along the path gives

```text
|f(sigma_n(r)x) - f(x)|  <=  sum_j |f(y_j) - f(y_{j-1})| + 1_{B_n(r)}(x)      (0 <= f <= 1).
```

Sum over `x`. Since `x -> y_{j-1}` is a permutation, the `j`-th term becomes
`sum_z |f(sigma_n(r'_j)^{e_j} z) - f(z)|`. For `e_j = -1`, substitute `z = sigma_n(r'_j) w`;
the term becomes `sum_w |f(w) - f(sigma_n(r'_j) w)|`. Either way it is at most `V_{R'}(f)`.
Hence

```text
V_R(f)  <=  |R| L' V_{R'}(f) + sum_{r in R} |B_n(r)|.
```

Substituting this into (AP2) for `R` gives (AP2) for `R'`, with `c' = c / (|R| L')` and an
`o_U(1)` error. □

**Consequence.** Under (KT\*), for *every* finite generating set `R` of `H`, the component
partition of the edited `T`-graph is an ambient Poincaré partition for `(sigma, R)`. In
particular this holds for `R = S_Γ ∪ {t_1^{±1}, ..., t_m^{±1}}`, for any finite family of
compressors that generates `H` together with `Gamma`.

## Step 3. The audit: what Kun–Thom's proof of Theorem 4.1 consumes

Read the proof of Theorem 4.1 with `G := H` and one fixed sofic representation `sigma`. The
whole argument, lines 692–1362, concerns that single `sigma`: the lifts, the partitions and
the error sequences are all indexed by `n` and taken along one ultrafilter `U`.

The hypothesis "both Γ and G have property (T)" (excerpt A) is consumed as follows. The
mechanical check in excerpt A shows that Section 4 has no other mention of (T), of `h_G`, or
of the ambient partition.

**(T) of `Gamma`.** It is used in two places:
- [Kun, Theorem 1] applied to `sigma|_Gamma` (excerpt C);
- the Alekseev–Thom cluster groupoid of a sofic approximation of the Kazhdan group `Gamma`
  (excerpts B and D).

Both are available in (KT\*), because `Gamma` is Kazhdan and `sigma|_Gamma` is a sofic
representation of `Gamma`. Lemma 4.2 also uses words for `t_ℓ s t_ℓ^{-1}` in `Gamma`, which
need only `t_ℓ ∈ P_Gamma` and that `sigma` is a homomorphism.

**Finite generation of `G`.** It is used only at lines 1107–1108 (excerpt H), to choose
`t_1, ..., t_m ∈ P_Gamma` with `G = <Gamma, t_1, ..., t_m>`. Such a family exists in (KT\*):
- `H` is generated by finitely many elements;
- each of them is a word in `P_Gamma ∪ P_Gamma^{-1}`, because `Gamma` is infranormal;
- take the `t_ℓ` to be the finitely many letters that occur, together with any prescribed
  compressor.

**(T) of `G`.** It is used only to have the ambient partition `𝒜_n` for the generating set
`S_G = S_Gamma ∪ {t_ℓ^{±1}}` of excerpt I. The partition is consumed in exactly three places.

1. *Convention* (excerpt E): `𝒜_n` lives on the original `Y_n`. This consumes no property.
2. *Lemma 4.3* (excerpt F) runs "the quantitative component matching used in the proof of
   Proposition 3.1" for the Γ-partitions `{u_n Q_{n,i}}` and `{Q_{n,j}}`. In that matching
   (excerpt I) `𝒜_n` enters in four ways:
   - through (AP1) for `S_G`: for the `S_Gamma`-edges at lines 533–536, for the `t_i`-edges
     at lines 541–542, and for the set `H_{i,n}` at lines 581–583;
   - through the median normalization `f_n = M_n / (M_n + m_A)`, which has values in `(0,1)`
     and median `1/2` on each cell;
   - through the step "total variation of `f_n` on the edited ambient graph is `o(|Y_n|)`,
     then Lemma 2.3 on every `A` and sum" (lines 559–566). Here the variation along the
     original `S_G`-edges is `V_{S_G}(f_n) = o_U(|Y_n|)`, and "accounting for the negligible
     ambient edge edit" is absorbed into the `ε_n` of (AP2). So this step is exactly (AP2)
     for `S_G`, giving `sum_x |f_n - 1/2| <= c^{-1}(V_{S_G}(f_n) + ε_n|Y_n|) = o_U(|Y_n|)`;
   - afterwards (lines 571–611), only through membership of two vertices in one cell,
     together with the concentration just obtained.
3. *Lemma 4.4* (excerpt G) introduces `𝒜_n` at lines 1031–1033 and uses it in four ways:
   - through (AP1) for the `t_ℓ`-edges (lines 1044–1047 and 1084) and for the Γ-edges
     (lines 1064–1066);
   - through the median normalization `H_n = f_n / (f_n + M_A)`, with values in `(0,1)`;
   - through the variation bound followed by "Lemma 2.3 applied on each ambient component
     and summed" (lines 1067–1074), which is (AP2) for `S_G` in the same way;
   - through the witness argument, which uses only "`x, u_{ℓ,n} x` lie in the same member of
     `𝒜_n`" and the concentration.

   The main proof reaches `𝒜_n` only through the two applications of Lemma 4.4 at line 1191
   (excerpt H). Its remaining steps use:
   - the cluster groupoids of `sigma|_Gamma`;
   - the functors of Lemma 4.3;
   - the algebraic reverse inclusion and generation, at lines 1342–1361 (excerpt H).

Nothing else is required of `𝒜_n`. In particular none of the following is used anywhere:
- that its cells are connected;
- that its cells are components of any particular graph;
- that the edited graph has bounded degree;
- that the Cheeger constant is for `S_G`, beyond the summed inequality (AP2).

**Conclusion of the audit.** The proof of Theorem 4.1 proves the following statement
verbatim. Suppose:
- `Gamma` is Kazhdan and infranormal in a finitely generated `G`;
- `sigma` is a sofic representation of `G`;
- for the generating set `S_G` of lines 1107–1108 and excerpt I, `(sigma, S_G)` has an
  ambient Poincaré partition.

Then `sigma(G)` normalizes `C_{S_U}(sigma(Gamma))`.

## Step 4. Proof of (KT\*)

Assume the hypotheses of (KT\*).
1. By Step 1, the edited `T`-components form an ambient Poincaré partition for `(sigma, T)`.
2. Choose `t_1, ..., t_m` as in Step 3.
3. By Step 2, the same partition is an ambient Poincaré partition for
   `(sigma, S_Gamma ∪ {t_ℓ^{±1}})`.
4. By the conclusion of the audit, `sigma(H)` normalizes `C_{S_U}(sigma(Gamma))`. □

**Main instance.** Take `H = <L, u>` with `u L u^{-1} <= L`, `L` Kazhdan, `Gamma = L` and
`T = S ∪ {u}`. The hypothesis of (KT\*) is then item 2 of
`bounded-cluster-period-preserves-kazhdan-fixed-algebras` under `BP_p`, whose Cheeger constant
is `min(h,1)/(8p)`. This is the use made in `bounded-period-compressors-no-defect-route`.

## Independent corroboration from the Lean assembly (not needed for the proof)

The sequential Lean formalization of Theorem 4.1 has the same dependency shape.
- In `GroupApproximation/KunThom/CompressorNormalizationAssemblyCore.lean`,
  `seqNormalizes_distinguished_of_guardedSteps` uses `hTG : HasKazhdanPropertyT G` only
  inside `(fun A ↦ exists_compressorDecomposition hTG hTΓ (normalizedSetup C hembed) A)`.
  That argument produces a `CompressorDecomposition` for the given approximation `A`.
- In `GroupApproximation/KunThom/CompressorNormalizationAssembly.lean`,
  `seqNormalizes_of_compressor_of_steps` opens with
  `refine hwrapper fun A v hv γ hγ ε hε hbound ↦ ?_`. Its commutation block
  `hcomm : A.AlmostCommutes (A.conjSeq t v) γ` uses `hdecomp A` for *that same* `A`, together
  with dischargers quantified over every approximation and decomposition.

So the formal proof is also per approximation: ambient (T) supplies a decomposition of the
approximation at hand and nothing else. This matches Step 3. The Lean statement itself
quantifies over all approximations, so it is not used as an import here.
