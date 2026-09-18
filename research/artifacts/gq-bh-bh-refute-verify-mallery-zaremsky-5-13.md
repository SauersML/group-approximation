# Adversarial check: Mallery–Zaremsky Question 5.13 answers (bh-refute, 2026-09-18)

Rotation item (b) (6d130b349, b6d9d8d45). Nodes checked:
- `strongly-shift-similar-point-stabilizers-are-copies-of-the-group`;
- `finitary-mixing-of-fp-highly-transitive-groups-is-fp`;
- `fp-strongly-shift-similar-groups-have-fp-houghton-like-groups`;
- `finitary-mixing-preserves-type-f-m`;
- `strongly-shift-similar-type-f-m-passes-to-houghton-like-groups`.

The Mallery–Zaremsky facts (arXiv:2202.00822: Lemma 3.19, Props 5.3 and 5.5, Obs 5.1) and the germ
isomorphism of `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group` were taken as cited.

Verdict: **PASS**. Q5.13's third sentence is answered yes (for finite presentation and for `F_m`). The first
two sentences are answered yes for strongly shift-similar and for finite `G`. The residual case is correctly
reduced to the OPEN `fg-infinite-shift-similar-groups-are-strongly-shift-similar`.

## Finite presentation (finitary mixing)

- **(R4) is finite.** Each `G_k ⊇ FSym(X_k)` is highly transitive, so `G`-orbits of ordered pairs of
  transpositions are determined by block membership and the coincidence pattern of at most 4 points.
- **Well-definedness (Step 2).** If `w, w'` both carry `(a,b)` to `(x_1, y_j)`, then `w'w^{-1} ∈ Stab_G(x_1, y_j)`,
  which is finitely generated because stabilizers are copies of `G`. So (R2) makes `w^{-1}t_jw` independent of
  `w`. The same argument works for `t_ij` via (R3).
- **Nit N1.** One needs a convention `i < j` for mixed transpositions between rays `i, j >= 2`, or a relation
  `t_ij = t_ji`. The latter follows from (R4), since `τ(σ) = σ` gives the conjugation identity, but it should
  be said.
- **Step 3.** `{τ^2 = 1, τστ = τ(σ)}` presents `FSym(X)` on all transpositions. It implies the Coxeter
  relations: commutation for disjoint transpositions, and the braid relation `s_i s_{i+1} s_i = (i,i+2) = s_{i+1} s_i s_{i+1}`.
- **Step 4.** `G ∩ FSym(X) = ∏ FSym(X_k)`, so the kernel dies in `K̃`. Correct.
- **Houghton step.** `B` is the preimage of `Germs(G)^n = ker(η_1,…,η_n)`, with `H/B ≅ Z^{n-1}`. P. Hall
  closure of finite presentation under extensions applies. Correct.

## Type `F_m` (balanced recoloring slice)

- **Height.** `h` is `M`-invariant. The identity `|c^{-1}(Y) ∩ S| − |Y ∩ S| = |D∩Z| − |D∩Y|` checks, and finitary
  `f` preserves `|c^{-1}(Y) ∩ S|` for `f`-invariant `S`.
- **Contractibility.** `L = h^{-1}(0)` is a directed union of the convex slices `L ∩ Cube_F`, so `L` is
  contractible and `L^{(m)}` is `(m−1)`-connected.
- **Cocompactness.** Every cube whose interior meets `L` has a level vertex, because `h` takes every integer value
  between its extremes on the vertices. Level vertices form one orbit, and cube orbits at `c_0` are indexed by
  `(|F∩Y|, |F∩Z|)`.
- **Stabilizers.** `K_Q = Fix_A(F∩Y) × Fix_C(F∩Z)` is re-derived: moving a point of `F` moves the one-flip vertex.
  It fixes every face of `Q_top`, so it lies in every flag stabilizer with finite index. Geoghegan 7.3.1 and 7.2.4
  then apply to the barycentric subdivision.
- **Closure in `𝔐_m`.** `Fix_M(F) = (Fix_A × Fix_C) · FSym(W∖F)`: correct a representative by `f' ∈ FSym(Y) × FSym(Z)`.
  This is again a two-block mixing, so the induction closes.
- **`F_m`-by-`F_m`** is Geoghegan §7.2 Ex. 1, correctly re-cited after the node's own correction.

## Attacks tried (all failed)

- **Houghton's `H_2`,** which has finitely generated stabilizers and a finitely presented germ quotient but is not
  finitely presented. It is excluded because `FSym` alone is not finitely generated. The node's calibration
  records this.
- **Brown's theorem.** `(H_a × H_b)·FSym` of type `F_{min(a,b)−1}` is consistent with `H_{a+b}` being `F_{a+b−1}`.

## Lesson for general BH

For permutation groups containing `FSym`, finiteness is a property of the tower of finite-set stabilizers. The
balanced-slice cube complex proves it with no Morse theory. This is the same data as a type (A) action:
finitely many orbits on tuples, plus finitely generated or `F_m` stabilizers. So finitary mixing is a closure
operation for type-(A)-style hosts, and it transfers finiteness verbatim. A BH envelope built from highly
transitive pieces needs its finiteness only once, in the pieces.
