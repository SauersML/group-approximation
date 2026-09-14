---
rg: 2
id: template-constituents-primitive-or-small-minimal-degree-proof
kind: route
title: Characters of induced representations see only fixed blocks, fixed points push down to primitive sections, and a finite section of a simple group cannot see the relators
target: template-constituents-primitive-or-small-minimal-degree
requires: [fp-simple-models-concentrate-on-template-constituents]
---

**Primitive sections exist.** Let `Q` act transitively on `Ω` with `|Ω| ≥ 2`. The `Q`-invariant partitions with at least 2 parts
form a nonempty set, since the partition into points is one. Choose one whose blocks are as large as possible. `Q` acts
primitively on its blocks: a nontrivial invariant partition of the blocks would give a coarser invariant partition of `Ω`, still
with at least 2 parts.

**Lemma 1 (fixed points push down).** Let `𝓑` be an invariant partition of `Ω` into blocks of size `s`. If `q` fixes a point, it
fixes that point's block. So `|Fix_𝓑(q)| ≥ |Fix_Ω(q)|/s`, and `fpr_𝓑(q) ≥ fpr_Ω(q)`, where `fpr = |Fix|/(number of points)`.

**Lemma 2 (relators are seen).** Let `Q_k = ⟨φ_k(X)⟩` act transitively on `Ω`, and let `𝓑` be an invariant partition with at
least 2 blocks. Then some relator `W_k(r)` acts nontrivially on `𝓑`.
- Otherwise `x ↦ (action of φ_k(x) on 𝓑)` kills `R`, and defines a homomorphism from `S` to the finite group `Sym(𝓑)`.
- It is trivial, because `S` is infinite and simple.
- So every `φ_k(x)`, and hence `Q_k`, acts trivially on `𝓑`. But `Q_k` is transitive on `Ω`, hence on `𝓑`, and `|𝓑| ≥ 2`.
  Contradiction.

**(U).** Let `σ ∈ T_k(θ,D)` act on `V`, and suppose `σ = Ind_H^{Q_k} τ` with `H` proper.
- Then `V = ⊕_{ω ∈ Ω} V_ω` with `Ω = Q_k/H`, `|Ω| = t ≥ 2`, `dim V_ω = n/t`, and `σ(q) V_ω = V_{qω}`. `Q_k` acts
  transitively on `Ω`.
- *Character bound.* In a basis adapted to the blocks, only blocks fixed by `q` contribute to the trace, and
  `|Tr(σ(q)|_{V_ω})| ≤ n/t` for a unitary on an `(n/t)`-dimensional space. So `|χ̃_σ(q)| ≤ |Fix_Ω(q)|/t = fpr_Ω(q)`.
- Let `𝓑` be a primitive section. By Lemma 1, for every relator `r`,
  `fpr_𝓑(W_k(r)) ≥ fpr_Ω(W_k(r)) ≥ |χ̃_σ(W_k(r))| > θ`. So every relator moves fewer than `(1−θ)|𝓑|` blocks.
- By Lemma 2, some relator has nonidentity image in `Q_k^𝓑`, with support smaller than `(1−θ)|𝓑|`. So
  `μ̂(Q_k^𝓑) < 1 − θ`.
- A nonidentity permutation moves at least 2 points, so `2 < (1−θ)|𝓑|`.

**(P).** A template orbit `Ω_j` is transitive under `Q_k`, and every relator has `fpr_{Ω_j} > θ`.
- If the action on `Ω_j` is primitive, `𝓑 = Ω_j`, and some relator acts nontrivially by the definition of a template orbit.
- Otherwise use Lemmas 1 and 2 as in (U).

**Corollary.**
- (P) With `θ > 1 − c`, a template orbit would give a primitive section with `μ̂ < 1 − θ < c`, so there are no template orbits.
  This contradicts `fp-simple-models-concentrate-on-template-constituents` (template orbits weigh at least `η > 0`).
- (U) With `θ > 1 − c`, an induced template constituent would give such a section. So every template constituent is primitive.
  By the template theorem they weigh at least `η²/4`. ∎
