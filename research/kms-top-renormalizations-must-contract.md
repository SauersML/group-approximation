---
rg: 2
id: kms-top-renormalizations-must-contract
kind: claim
title: For K >= 2, the counter renormalization of a faithful self-similar action of the KMS top B_K has no unipotent part, its lamp map extends to all of R_K by Hartogs, and every non-contracting renormalization of Frobenius-Möbius type is unfaithful; so a hard KMS lift must use a virtual endomorphism that does not restrict to the top
distinct_from:
  kms-configuration-lift-needs-non-contracting-counters: that sketches (conditionally, per bh-ref-q11 b5cae104ff) why contracting renormalizations cannot carry a hard machine, and asks for a non-contracting one; this shows non-contracting renormalizations of the top itself are unfaithful, which moves the crux off the top.
  two-counter-kms-top-has-no-affine-self-similar-action: that treats the case with all counters in the domain; here the domain meets the counters in U^(p^e), and the tool is Hartogs extension rather than the affine digit map.
  kms-tops-embed-in-fp-self-similar-metabelian-groups: that is the contracting (Kochloukova–Sidki) example this theorem allows.
---

**ESTABLISHED as a lane proof (bh-kd2p, 2026-09-19) for parts (b) and (c); part (a) is a sketch. Not
independently reviewed. **Referee (bh-ref-q11, 2026-09-19): (b) and (c) PASS; (a) graded a sketch.**

## Setting

- `K ≥ 2`, `R = R_K`, `U = U_K` and `B_K = R ⋊ U`, as in `kms-tops-embed-in-fp-self-similar-metabelian-groups`.
- `f : H → B_K` is a simple virtual endomorphism, meaning its action is faithful and transitive.
- `M = H ∩ R` has finite index, and `U_H` is the image of `H` in `U`.
- `ψ : U_H → U` is the counter part of `f`, and `S = F_p[U_H] ⊆ R`.
- As in `kms-configuration-lift-needs-non-contracting-counters`:
  - `f(M) ⊆ R`, since `R` is the torsion of `B_K`;
  - `f(u·m) = ψ(u) f(m)`;
  - `ψ` extends to an injective ring homomorphism `ψ̃ : S → R`, because faithfulness gives `f(M) ≠ 0` and
    `R` is a domain.

## (a) Sketch: no unipotent part

- `ψ̃^*` is dominant with finite fibres. So `Ψ = ψ ⊗ ℝ` maps the Bieri–Groves (tropical) set `Trop(R) = T^K ⊆ ℝ^{2K}`
  onto itself. Here `T` is the tropical line with rays `(1,0)`, `(0,1)`, `(−1,−1)`.
- A linear automorphism preserving `|T^K|` permutes its `3K` rays, respecting the triples that sum to 0.
- So `Ψ` is monomial: a permutation `π` of the `K` factors, times on each factor a positive scalar `λ_i` times an
  element of `S_3` permuting the three rays.
- The unit equation `u + v = 1` in `F_p^× U` has only Frobenius-twisted Möbius solutions `μ(t^{p^k})`. So the
  scalars are powers of `p` divided by index contributions.
- **Consequence.** "Frobenius plus a non-contracting unipotent part" does not occur. A renormalization is
  contracting, isometric or expanding according to `Λ = ∏ λ_i` over each cycle of `π`.

## (b) Lemma: Hartogs extension

**Statement.** `f|_M` extends uniquely to an additive, `ψ̃`-semilinear map `f̂ : R → R`.

**Proof.**
- `R/M` is finite, so it is killed by an ideal `I ⊆ S` of finite codimension. Since `K ≥ 2`, `I` has height
  `K ≥ 2`.
- Let `R_ψ` be `R` viewed as an `S`-module through `ψ̃`. It is finite over the finite-index subring
  `F_p[ψ(U_H)] ≅ S`, and `R` is Cohen–Macaulay of dimension `K`. So `depth_I R_ψ ≥ 2`, and
  `Ext^0_S(S/I, R_ψ) = Ext^1_S(S/I, R_ψ) = 0`. Hence every `S`-map `I → R_ψ` is multiplication by a unique element.
- For `r ∈ R`, the map `i ↦ f(ir)` is `S`-linear from `I` to `R_ψ`. So `f(ir) = ψ̃(i)·x_r` for a unique `x_r ∈ R`.
- Put `f̂(r) = x_r`. Uniqueness shows that `f̂` extends `f` and is additive and `ψ̃`-semilinear. ∎

## (c) Theorem: non-contracting Frobenius–Möbius renormalizations are unfaithful

**Statement.** Suppose `U_H = U^{p^e}`, so that `S = Frob^e(R)`. Suppose also that for some `j ≥ 0` and some ring
automorphism `σ` of `R` we have `ψ̃(a^{p^e}) = σ(a)^{p^{e+j}}` for all `a ∈ R`. This is the isometric case
`j = 0` or the expanding case `j > 0`. Then `f` is not simple.

**Proof.**
- `M` contains the `U`-invariant, finite-index subgroup `⋂_{u∈U/U_H} uM`, which is an ideal. So `M` contains
  `𝔞 = ∏_{z∈Z} 𝔪_z^N` for a finite set `Z` of closed points and some `N`.
- Enlarge `Z` to the set of all closed points with residue field of order at most `p^r`, for `r` large. This set
  is finite, and `σ` is defined over `F_p`, so `σ(Z) = Z` and `σ(𝔞) = 𝔞`.
- Put `𝔟 = Frob^e(𝔞)·R`. It is a nonzero ideal, and `𝔟 ⊆ 𝔞 ⊆ M`.
- For `c = a^{p^e}` with `a ∈ 𝔞`, and `r ∈ R`: `f(cr) = f̂(cr) = ψ̃(c) f̂(r) = σ(a)^{p^{e+j}} f̂(r)`.
  Since `σ(a) ∈ 𝔞` and `𝔞^{[p^{e+j}]} ⊆ Frob^e(𝔞)`, this lies in `𝔟`.
- So `f(𝔟) ⊆ 𝔟`. Every ideal is normal in `B_K`, so `𝔟` lies in the `f`-core. ∎

**The contracting case escapes.** Kochloukova–Sidki's `x_1^p ↦ x_2` is the case `j = −1` in the `x_1`-direction.
There `Frob^{-1}(𝔞) ⊄ 𝔞`, and the invariant ideal disappears.
- The expected general statement is that on every cycle of `π` with `Λ ≥ 1` an invariant ideal exists, uniformly
  in mixed exponents. It is not proved here: the proof above uses a uniform `e` and `j`.

## Consequence for KD2_p

**A top-preserving lift must contract (within the Frobenius–Möbius class of (c)).** Combine (c) with `kms-configuration-lift-needs-non-contracting-counters`.
- Suppose the self-similar structure of `G(M)`, or of an overgroup, restricts to a self-similar structure on the
  top factor `B_0`, i.e. `F(H ∩ B_0) ⊆ B_0`.
- Then the renormalization of `B_0` must contract, in the Frobenius–Möbius class.
- By the Part 3 sketch of that node (conditional on its unconstructed lift and its unproved bounded-coefficient step), a contracting renormalization makes configuration equality polynomial, which is too easy for a hard machine.

**So, conditionally on that sketch and on the Frobenius–Möbius class, a hard lift should not preserve the top.** The virtual endomorphism must send some lamps of the top into the
configuration module `T`, or out of `G(M)`. That is allowed: the torsion of `G(M)` contains both `T` and the top
lamps, so the torsion argument no longer separates them.

**The crux now.** Find a virtual endomorphism of `G(M)`, or of an overgroup, mixing top lamps with
configurations, e.g. `F(A_0) ∈ T·A_0`. It must be compatible with G5–G8 and non-contracting on the counters.
The increment-only machines of bh-birget's open case (c) are the natural test.

## Lesson

**On the top, faithfulness forces contraction (proved in the Frobenius–Möbius class), and contraction should kill hardness (sketch). Hardness should enter through
renormalizations that mix the top into the configuration module.**

## Referee (bh-ref-q11, 2026-09-19): (b) PASS, (c) PASS, (a) a sketch; the b5cae104ff repairs are confirmed applied

**The setting.**
- `ψ` is well defined, because two lifts of `u ∈ U_H` differ by `M`, and `f(M) ⊆ R`.
- `f(M) ≠ 0`: otherwise `∩_(u∈U/U_H) uM`, a nonzero ideal, lies in the core.
- `ψ̃` is injective: if `ψ̃(s) = 0`, the nonzero ideal `(∏_u us)𝔞 ⊆ ker f|_M` lies in the core.

**(b) Hartogs extension: PASS. It applies over `R_K`.**
- `R/M` is a finite `S`-module, so its annihilator `I ⊆ S` has finite codimension. `S = F_p[U_H]` is a finitely generated domain of dimension `K`, and `R` is integral and finite over it. So `ht I = K ≥ 2`.
- `ψ` is injective, so `ψ(U_H)` has full rank `2K` in `U`, and `R` is finite over `ψ̃(S) = F_p[ψ(U_H)] ≅ S`.
- `R_K` is regular, hence Cohen–Macaulay. For the finite map, `depth_I(R_ψ) = depth_(IR)(R) = ht(IR) = K ≥ 2`.
- So `Ext^0` and `Ext^1(S/I, R_ψ)` vanish, and `Hom_S(I, R_ψ) = R_ψ`.
- `i ↦ f(ir)` is `S`-linear, since `IR ⊆ M` and `f` is `ψ̃`-semilinear on `M`. So `f̂` exists, is unique, extends `f`, and is additive and semilinear.
- For `K = 1` the height is 1 and the argument fails, correctly (compare `D(f) = (f−f(0))/X`).

**(c): PASS under its hypotheses** (uniform `e` and `j`, and a global Frobenius–Möbius form).
- `S = Frob^e(R)`, because `R` is the `F_p`-span of `U` and Frobenius is additive.
- `σ` is `F_p`-linear, so it permutes the finite set of closed points of residue degree `≤ r`. Hence `σ(𝔞) = 𝔞`.
- `𝔟 = Frob^e(𝔞)R ⊆ 𝔞 ⊆ M`. `ψ̃(a^(p^e)) = (σ(a)^(p^j))^(p^e) ∈ Frob^e(𝔞)`, so `f(𝔟) ⊆ 𝔟`.
- `𝔟` is a nonzero ideal, hence normal in `B_K`, and it lies in the core.

**(a): a SKETCH, as labelled.** It needs two things that are plausible but not proved:
- a precise functoriality statement: `Ψ` maps the Bieri–Groves set `Σ^c = T^K` onto itself under a finite dominant `ψ̃^*`;
- that a linear automorphism of `R^(2K)` preserving `|T^K|` is monomial (it permutes the `3K` rays).

The unit-equation step is only indicated.

**The repairs from my b5cae104ff review of `kms-configuration-lift-needs-non-contracting-counters` are all applied** in this landing: the Part 0 statement, the Part 2 "informal" status, the Part 3 "sketch" status, and the title.
