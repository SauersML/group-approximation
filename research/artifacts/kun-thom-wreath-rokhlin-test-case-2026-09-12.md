# Kun–Thom wreath test case: what Seward gives, what transfers to partitions, and where a deficit must sit

Lane `gk-n-ae-decoder`, 2026-09-12. Supports:
- the Cairn claims `rokhlin-maximality-closed-under-local-embeddings` and
  `kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers`;
- the Attempts entry on `kun-thom-wreath-bernoulli-rokhlin-maximal`.

## Summary

The test case is `W = (Z/2) wr_(G/Γ) G` for a Kun–Thom Theorem E pair `Γ < G`. The actor is residually
finite, the lamp subgroup is locally finite abelian, and `W` is surjunctive and nonsofic. The question
is whether `h^Rok_W(A^W) = log |A|`. It is not decided here.

* **Seward.** No result in Krieger I, Krieger II or *Weak containment and Rokhlin entropy* bounds
  Rokhlin entropy through a normal subgroup, an amenable kernel or a quotient (Section 1). The
  extension structure of `W` is exactly what soficity fails to pass through, so there is no
  extension theorem to import.
* **Transfers.** Rokhlin-maximality is closed under local embeddings (Theorem 2.1), the same finite
  table closure that drives the surjunctivity proof for LEF lamps. So for every LEF lamp, maximality
  of the graph wreath reduces to maximality of graph wreaths with finite lamps over the same actor and
  graph.
* **Does not transfer.** Marked-site peeling and the coset-region lemma (Section 3). Stabilizer
  products are residually finite, so they give only the necessary condition.
* **Localization for W.** Every deficit witness over `W` generates a subgroup `K` whose actor image
  `π(K)` is nonamenable and has a lamp-site stabilizer that is not closed in the profinite topology
  of `π(K)` (Theorem 4.1). This is exactly where the Kun–Thom non-closedness of `Γ` enters.
* **Exact step** (Section 5). A deficit must save entropy along invisible lamp configurations. On the
  Bernoulli shift those carry independent symbols, and no measurable device is known that turns
  model-level collapse into a saving. Maximality would need a lower bound on configurations folding
  there, and no counting argument without models is known.

## 1. Source check: Seward on normal subgroups and quotients

Read on 2026-09-12 through the ar5iv HTML renderings. These readings are automated extractions, so
check the PDF before citing an absence.

* **Krieger I** (arXiv:1405.3604).
  * The relative finite generator theorem, Theorem 1.1: if `h^Rok_G(X, μ | F) < H(p̄)`, there is a
    partition `α` with `μ(A_i) = p_i` and `σ-alg_G(α) ∨ F = B(X)`.
  * The consequence that Rokhlin entropy equals Kolmogorov–Sinai entropy for free ergodic actions
    of amenable groups.
  * No statement about normal subgroups, quotients, extensions, restriction to subgroups, or lower
    bounds for a class of groups.
* **Krieger II** (arXiv:1501.03367).
  * Theorem 1.11 on products `P x G`.
  * The per-group chain INF ⟹ RBS ⟹ GOT + KAP, and the sofic case.
  * No statement about normal subgroups, amenable normal subgroups or quotients, and no
    Bernoulli result specific to nonsofic groups.
* ***Weak containment and Rokhlin entropy*** (arXiv:1602.06680). Only upper bounds (Theorems 1.4,
  1.5, Corollary 6.4), the finite-index formula of Theorem 1.6, and Theorem 1.7 on finite-index
  normal subgroups in a sofic setting. No lower bounds, and no amenable kernels or quotients.
* **Alpeev–Seward, Krieger III** (arXiv:1705.09707), abstract as recorded in
  `research/artifacts/rokhlin-lower-bound-mechanisms-2026-09-12.md`: non-ergodic generator theorem,
  subadditivity, semicontinuity, ergodic decomposition, inverse limits. No extension theorem.

**Reading for W.** `W` is locally-finite-abelian-by-residually-finite. Sofic groups are closed under
amenable extensions on top (sofic-by-amenable), but not under amenable kernels below
(amenable-by-sofic), and `W` itself shows the latter fails. Every known Rokhlin lower bound goes
through soficity, so no available theorem reduces `h^Rok_W` to the kernel and the quotient.

## 2. Local embeddings transfer to partitions

A group `H` *locally embeds* into a class `C` when, for each finite `S ⊂ H` containing `1`, some
`K` in `C` and injective `η: S -> K` satisfy `η(ab) = η(a)η(b)` whenever `a, b, ab ∈ S`.

**Theorem 2.1.** If every group in `C` is Rokhlin-maximal at `q`, so is every group that locally
embeds into `C`.

*Proof.* Let `(k, E, F, ψ)` be a configuration over `H`, with

    Φ = (1/k) [ H(ψ(x|_E)) + H( x(1) | (ψ((x(fe))_(e ∈ E)))_(f ∈ F) ) ]

as in `bernoulli-rokhlin-deficit-has-a-finitary-witness`. `Φ` depends only on the incidence pattern:
the map `(f, e) -> fe`, which products coincide, and which equal `1`. Put `S = {1} ∪ E ∪ F ∪ FE` and
take `η`. Then `η(1) = 1`, since `η(1)^2 = η(1)`. With `E' = η(E)`, `F' = η(F)` and `ψ'` the same
function with coordinates relabelled along `η`:
- `η(f)η(e) = η(fe)`;
- `η(f)η(e) = η(f')η(e')` exactly when `fe = f'e'`, by injectivity;
- `η(f)η(e) = 1` exactly when `fe = 1`.

So `Φ(k, E', F', ψ') = Φ(k, E, F, ψ)`. A deficit over `H` would be a deficit over `K`. QED

**Remarks.**
* Theorem 2.1 uses less multiplication data than the surjunctivity version (Lemma 3.1 of
  `research/artifacts/lef-graph-wreath-surjunctivity-2026-09-12.md`), which also needs the composition
  `SM` and a missing cylinder. It contains directed colimits and canonical hosts as special cases.
* **LEF lamps.** By Lemma 4.1 of the same artifact, every finite partial table of `Λ(A) ⋊ G` with `A`
  LEF embeds into `Λ(B) ⋊ G` with `B` finite, keeping the actor and the graph. So Rokhlin-maximality of
  all finite-lamp graph wreaths over `G` implies it for all LEF-lamp graph wreaths over `G`. In
  particular the Kun–Thom test case with any LEF lamp reduces to finite lamps.

## 3. What does not transfer

* **Transplants to coset spaces.** The surjunctivity proof passes an injective automaton to
  `H_U\W ≅ A^U x G` and uses that injectivity survives. The entropy analogue is a factor map or a
  coinduction. Both give upper bounds only, and Rokhlin entropy is not monotone under factors over
  groups containing `F_2` (already on the test-case node).
* **The coset-region lemma** is a rigidity statement: an injective finite-memory map that is the
  identity off finitely many cosets of a surjunctive `K` is bijective. It uses no counting. Rokhlin
  entropy has no chain rule over strata of infinite index that would let a partition be peeled stratum
  by stratum. Subadditivity, `h(X) <= h(F) + h(X | F)`, points the wrong way for a lower bound.
* **Stabilizer products** `A^U x G_U` are residually finite, hence sofic, hence Rokhlin-maximal.
  Maximality passes to subgroups (`bernoulli-rokhlin-maximality-passes-to-subgroups`), so this is
  consistent with maximality of `W`, and only necessary.

## 4. Localization over W: deficit witnesses need non-closed stabilizers

Let `G` be residually finite, `X` a `G`-set, `B` a nontrivial finite abelian group,
`W = B^(X) ⋊ G`, and `π: W -> G` the projection.

**Theorem 4.1.** Let `(k, E, F, ψ)` be a configuration over `W` with `Φ < log q`, and
`K = <E ∪ F>`. Then `π(K)` is nonamenable. Let `O_1, ..., O_m` be the `π(K)`-orbits of the finitely many
sites in the lamp supports of `E ∪ F`. For some `i`, the stabilizer `Stab_(π(K))(o_i)` of a point `o_i`
of `O_i` is not closed in the profinite topology of `π(K)`.

*Proof.*
1. **Where K sits.** Since `(n, g)(n', g') = (n + g.n', gg')` and `(n, g)^-1 = (-g^-1.n, g^-1)`, every
   lamp part of an element of `K` is supported in `O = O_1 ⊔ ... ⊔ O_m`. So `K <= V = B^(O) ⋊ π(K)`.
2. **Amenable image.** If `π(K)` is amenable, `K` is an extension of a locally finite group by an
   amenable one. It is amenable, hence sofic, and `sofic-radical-localizes-bernoulli-deficit-witnesses`
   excludes the witness.
3. **Closed stabilizers make V residually finite.** Suppose every `S_i = Stab_(π(K))(o_i)` is closed.
   `π(K)` is residually finite as a subgroup of `G`. Take `v = (n, g) != 1`.
   * If `g != 1`, a finite quotient of `π(K)` detects it.
   * If `g = 1`, let `T` be the finite support of `n`. Two distinct points `h o_i`, `h' o_i` in one orbit
     have `h^-1 h'` outside `S_i`. Closedness gives a finite-index normal `Δ` with `h^-1 h'` outside
     `S_i Δ`. Intersecting finitely many such `Δ` separates all pairs of `T`.
   * Put `Ō = ⊔_i π(K)/(S_i Δ)`, a finite `π(K)/Δ`-set: `Δ` acts trivially on it, because it is normal
     and contained in `S_i Δ`. The map `h o_i -> h S_i Δ` is well defined and equivariant, and it is
     injective on `T`.
   * Summing lamps over its fibres is an equivariant homomorphism `B^(O) -> B^Ō`, since `B` is abelian.
     It gives a homomorphism `V -> B^Ō ⋊ π(K)/Δ` into a finite group that does not kill `n`.
   * So `V` is residually finite.
4. **Conclusion.** Then `K` is residually finite, hence sofic, so `Rad(K) = 1`, and the localization
   theorem again excludes the witness. QED

**Remarks.**
* **Direction of closedness.** The profinite topology of `π(K)` is finer than the topology it inherits
  from `G`. A stabilizer `π(K) ∩ gΓg^-1` that is non-closed in `π(K)` therefore forces `gΓg^-1`, hence
  `Γ`, to be non-closed in `G`. For the Kun–Thom pair `Γ` is not closed
  (`kun-thom-wreath-bernoulli-rokhlin-maximal`, Attempts). Theorem 4.1 localizes a deficit to the
  subgroups where that non-closedness is visible.
* **Invisible lamps.** Let `Γ̂ = ∩_Δ ΓΔ`, the profinite closure of `Γ`. The fibre-sum maps
  `W -> (Z/2) wr_(G/ΓΔ) (G/Δ)` together kill exactly the lamp configurations with zero sum on every
  `Γ̂`-fibre of `G/Γ -> G/Γ̂`; call that subgroup `N_0`. The quotient `W/N_0 = (Z/2) wr_(G/Γ̂) G` is
  residually finite by step 3, so `Rad(W) <= N_0`. The rigid defect `a_(tΓ) a_(γtΓ)` lies in `N_0`.
* **LEF lamps.** Theorem 4.1 applies to the finite-lamp models of Section 2 with abelian lamps.

## 5. A deficit through invisible lamps: the ansatz and the exact step

**Ansatz.** Let `d = a_x a_y` be the rigid defect, with `x = tΓ` and `y = γtΓ`. The witness has points
`p` and `pd`, and `K = <E ∪ F>` contains the actor elements `t, γ` and a nonamenable part of `π(K)`
whose stabilizer at `x` is not closed (Theorem 4.1). `ψ` reads `x` on `E`, and the `F`-translates are
meant to decode `x(1)` with conditional entropy below the entropy `ψ` spends.

**Where it dies.**
* **Why models exist but do not help.** The counting proof fails on such patterns because every
  almost-action on a finite set identifies `p` and `pd` on most points. There one symbol serves both
  points, and the count sees redundancy that is not there.
* **On the shift itself.** `p` and `pd` are distinct coordinates with independent uniform symbols. A
  deficit would have to be a measurable coding on the actual shift. The obstructions of
  `research/artifacts/measurable-alphabet-compression-2026-09-12.md` apply over every group:
  - routing preserves the measure;
  - coset factors with infinite stabilizers are constant;
  - homomorphic codes collide.
* **Along N_0.** The restriction of the Bernoulli `W`-shift to `N_0` is a Bernoulli action of a
  locally finite group with infinite base. Every finite subgroup of `N_0` acts freely with iid symbols
  on its orbits, so there is no structure in `N_0` alone to save on. Any saving has to couple the
  invisible lamps with a nonamenable actor part through a non-closed stabilizer. No such device is
  known.
* **Maximality.** A proof would need a lower bound for configurations whose generated subgroup has a
  non-closed stabilizer, without sofic models of that subgroup. Section 1 found no source device, and
  Section 3 shows the surjunctivity machinery supplies none.

**Status.** `kun-thom-wreath-bernoulli-rokhlin-maximal` stays OPEN. Established here:
- closure of Rokhlin-maximality under local embeddings, which reduces LEF lamps to finite lamps;
- the non-closed-stabilizer localization over `W`.
