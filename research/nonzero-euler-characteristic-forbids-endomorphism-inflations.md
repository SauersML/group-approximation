---
rg: 2
id: nonzero-euler-characteristic-forbids-endomorphism-inflations
kind: claim
title: A group of type VF with nonzero Euler characteristic has no injective endomorphism with proper finite-index image, so no subshift over F_2 × F_2 (or over Λ_1 × Λ_1 with χ(Λ_1) ≠ 0) admits a compressing endomorphism inflation; unlabelled compression there must be non-endomorphic
distinct_from:
  substitution-inflation-hosts-are-full-contracting-rsgs: that uses the inflation of a box substitution over Z^d (Euler characteristic 0, with the endomorphism v ↦ kv) to obtain finitely coded hosts; this shows that the endomorphism form of inflation is unavailable whenever χ(Λ) ≠ 0, whether or not the endomorphism is expanding, which includes the first Track A test group F_2 × F_2.
---

**ESTABLISHED** (lane bh-invent-06b, 2026-09-18). The group theory is standard: multiplicativity of the Euler
characteristic (K. Brown, *Cohomology of Groups*, IX.7, recalled, not re-read). The consequence for codings is an
elementary lane proof. No priority is claimed.

## Setting

An **endomorphism inflation** of a `Λ`-subshift `X` is a homeomorphism `ι` from `X` onto a clopen subset,
together with an injective endomorphism `φ : Λ → Λ`, such that:
- `ι ∘ t_λ = t_(φ(λ)) ∘ ι` for all `λ`;
- `X = ⊔_(g ∈ R) t_g ι(X)` for a set `R` of left coset representatives of `φ(Λ)`.

Constant-shape substitutions over `Z^d` are exactly of this form, with `φ(v) = kv`, `R = [0,k)^d`, and recognizability
supplying the disjoint union. Their inflation germs are unlabelled, and they compress
(`substitution-inflation-hosts-are-full-contracting-rsgs`).

## Statement

1. If `Λ` has type VF and `χ(Λ) ≠ 0`, then every injective endomorphism `φ` with `[Λ : φ(Λ)] < ∞` is an
   automorphism.
2. So every endomorphism inflation of a subshift over such `Λ` has `|R| = 1` and `ι(X) = t_g^(−1) X = X`. The
   pieces `t_g ι^n(X)` never branch, and endomorphism inflations generate no finite coding and no contracting
   loop.
3. **Instances.** This applies to `F_n × F_m` (`n, m >= 2`, with `χ = (1−n)(1−m)`), to surface groups, and to
   `Λ_1 × Λ_1` whenever `χ(Λ_1) ≠ 0`. It does not apply to `Z^d` (`χ = 0`), nor to `Λ_1 × Z` (`χ = 0`). There
   `id × (×k)` is a partial inflation along the `Z` factor only.

## Proof

1. **Euler characteristic.**
   - `φ(Λ) ≅ Λ` is a subgroup of finite index `m`.
   - For a finite-index subgroup `H` of a VF group, `χ(H) = [Λ : H]·χ(Λ)`. Hence `χ(Λ) = χ(φ(Λ)) = m·χ(Λ)`.
   - Since `χ(Λ) ≠ 0`, `m = 1`.
2. **No branching.**
   - `t_(g φ(λ)) ι(X) = t_g ι(t_λ X) = t_g ι(X)`, so the pieces are indexed by cosets. `R` is finite, since the
     pieces are disjoint nonempty clopen sets covering a compact space. So the index is finite, and by (1)
     `|R| = 1`.
   - Then `X = t_g ι(X)`: `ι` is a homeomorphism of `X` intertwining `Λ` with its `φ`-twist. Every piece of every
     level is all of `X`.
   - A finite coding needs partitions into at least two pieces with mesh tending to 0 (the definition in
     `free-sft-hosts-admit-no-finite-type-coding`). So `ι` contributes none, and no bisection built from `ι` and
     the translations has `b(U) ⊊ U` shrinking to a point. ∎

## Consequences for Track A (F_2 × F_2 and Λ_1 × Λ_1)

By `labelled-hosts-of-free-actions-have-no-contracting-loops`, a finitely coded host over a free, measured or
distal `X` needs unlabelled compressing germs. Over `F_2 × F_2` this node excludes the endomorphism form of such
germs, expanding or not. What remains is exactly three designs:
- **(i) Compression by `Λ` with isotropy.** Boundary-type codings, gate E3′. This is labelled, so it needs a
  non-free `X`.
- **(ii) Non-intertwining unlabelled germs.** Telescope/seed maps as in Conjecture SS, or substitutions whose
  supertiles are not cosets of a subgroup. An example would be hierarchical tilings of the Cayley tree with growing
  supertiles, whose inflation is only a quasi-isometric self-embedding. Nothing is known here.
- **(iii) Mixed products.** `Λ = Λ_c × Z^j`: the `Λ_c` directions are compressed by (i) and the `Z^j` directions
  by inflation, which needs no rigidity. The product engine required is the open product theorem recorded in
  `v-times-inflation-host-full-groups-are-finitely-presented`.

## Lesson for general BH

Self-similarity by a group endomorphism is an Euler-characteristic-zero phenomenon. Over the non-amenable,
nonzero-`χ` groups that Track A uses, inflation cannot come from the acting group. Any unlabelled compression must
be geometric (a quasi-isometric, non-coset hierarchy) or dynamical (seeds), and neither has been built. So the
honest shape of E3 over `F_2 × F_2` has two branches:
- the topologically free E3′, which is proved for boundary codings;
- a genuinely new non-coset hierarchy on the tree, which is the first object to construct if one wants to keep
  freeness.
