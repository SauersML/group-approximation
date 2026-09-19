---
rg: 2
id: ledrappier-square-free-commutant-review
kind: claim
title: Referee review of 54ed6d2fe (Ledrappier's square) — GL_2(A) does act on X_L^2 by shift-commuting, Haar-preserving automorphisms containing F_2, and X_L^2 is quantum rigid in the (RA) sense, but via the permutive-triangle node, not product stability (which is about external products over Λ_1 × Λ_2); monotonicity and the time-lift transfer hold for subshift rows; the non-hierarchical claim holds in the stronger form "every fibre over the MEF is infinite"
distinct_from:
  algebraic-rows-carry-rigid-free-commutants-but-never-minimality: that is the lane node under review; this checks it item by item, repairs one citation and one proof step, and resolves its caveat.
  quantum-rigidity-is-product-stable: that concerns X ⊠ Y over Λ_1 × Λ_2; this records that it does not apply to the diagonal self-product X_L × X_L over Z^2.
  permutive-triangle-sfts-are-quantum-rigid: that proves rigidity of triangle-permutive Z^2-SFTs over any alphabet; this applies it to X_L^2 with alphabet F_2^2.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of the lane proof 54ed6d2fe by bh-invent-16).** No
priority claimed. Nodes read at source on origin/main:
- `ra-forces-amenable-commutants-of-uniquely-ergodic-rigid-rows`;
- `time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows`;
- `deterministic-time-lifts-inherit-quantum-rigidity`;
- `quantum-rigid-subshifts-cluster-the-modifications-of-each-point`;
- `quantum-rigidity-is-product-stable`;
- `permutive-triangle-sfts-are-quantum-rigid` (with its referee PASS);
- the SYNTHESIS v9.1 (RA) status, fact 7.

## Verdicts

| claim | verdict |
|---|---|
| (1) `X_L^2` is rigid in the (RA) sense | **PASS, citation repaired** |
| (2) `GL_2(A)` acts on `X_L^2` by automorphisms of the `Z^2`-system, `F_2` inside, Haar-preserving | **PASS** |
| (3a) closed invariant subsets inherit rigidity | **PASS** |
| (3b) time lift of such an `M` is a minimal free rigid subshift (the caveat) | **PASS**: the transfer never uses finite type |
| (3c) freeness of the lift | **PASS** (uses faithfulness (ii)) |
| (4) `M` must be non-hierarchical | **PASS with a repaired step**, in a stronger form |

## (1) Rigidity: the right sense, the wrong citation

**The sense matches.** "Rigid" is `D`-quantum rigidity over a field, as defined by (Q1)–(Q3) of
`fp-v-times-subshift-full-groups-force-quantum-rigidity`. (Q3) runs over the `B_D`-patterns absent from the
subshift. The clustering node makes this explicit for arbitrary subshifts. This is the notion in (RA_free):
"every minimal, free, quantum-rigid subshift action is topologically amenable".

**The citation is wrong.**
- The node derives rigidity of `X_L^2` from `quantum-rigidity-is-product-stable`. That node concerns
  `X ⊠ Y ⊆ (A × B)^(Λ_1 × Λ_2)` over the **product group**, and its own calibration line reads "products … of
  Ledrappier's shift are rigid over `Z^2 × Z^2 = Z^4`".
- `X_L^2` here is the **diagonal** self-product: `Z^2` acts on both coordinates at once, with alphabet `F_2^2`.
  That is a different system, and product stability says nothing about it.
- A diagonal product of rigid systems is not rigid for formal reasons. The marginal families are commutative, but
  cross-commutation of the two marginals at far sites is not implied.

**The correct citation.**
- `X_L^2 = {u ∈ (F_2^2)^(Z^2) : u(z + e_2) = u(z) + u(z + e_1)}` is triangle-permutive: any two of
  `u(z), u(z+e_1), u(z+e_2)` determine the third, by the group law.
- So `permutive-triangle-sfts-are-quantum-rigid`, item 1, gives `D`-rigidity for every `D ≥ 1` over every field.
  That item was refereed PASS by bh-ref-ffwz, and it holds for any alphabet.
- The conclusion of (1) stands.

## (2) The free commutant lands in `Aut(X_L^2, Z^2)`

**The algebra.**
- Let `R = F_2[s^(±1), t^(±1)]`, with `s, t` the shifts by `e_1, e_2`.
- The defining rule is `t·x = x + s·x`, so `X_L` is killed by `t − 1 − s` and is a module over
  `A = R/(t − 1 − s) ≅ F_2[s^(±1), (1+s)^(-1)]`.
- Every element of `A` is represented by a Laurent polynomial in `s, t`, since `(1+s)^(-1) = t^(-1)`. So it acts on
  `X_L` as a finite `F_2`-sum of shifts: a linear cellular automaton.

**Shift commutation.**
- `g = [[a, b], [c, d]] ∈ GL_2(A)` acts by `(x, y) ↦ (ax + by, cx + dy)`, a linear cellular automaton on `X_L^2`.
- The diagonal `Z^2`-action is by the scalar matrices `s·I` and `t·I`. These are central in `GL_2(A)`, because `A`
  is commutative. So every `g` commutes with the `Z^2` shift.
- `g^(-1)` has entries in `A`, so it is an inverse cellular automaton, and `g ∈ Aut(X_L^2, Z^2)`.

**Faithfulness.**
- If `g` acts trivially, each entry of `g − I` annihilates `X_L`.
- `X_L` is the Pontryagin dual of the `R`-module `A`, so its annihilator is the annihilator of `A`, which is 0.
  (Also, `A` is a domain, being a localization of `F_2[s]`.) So `g = I`.

**Haar measure.** Continuous surjective automorphisms of a compact group preserve Haar measure.

**The free group.**
- Units of `F_2[s]` are trivial, so `GL_2(F_2[s]) = SL_2(F_2[s])`.
- By Nagao's theorem it is `GL_2(F_2) *_(B(F_2)) B(F_2[s]) ≅ S_3 *_(Z/2) (F_2[s], +)`, since the diagonal entries are units, hence 1. Here `B` is the upper
  triangular subgroup.
- The amalgamated subgroup has index 3 and index `∞` in the two factors, so the amalgam contains a nonabelian free
  subgroup.
- `F_2[s] ⊆ A` gives `F ≅ F_2 ≤ GL_2(A)`. **PASS.**

## (3) Closed invariant subsets and the time lift

**(3a) Monotonicity (clustering node, Corollary 4).** A `D`-family for a closed invariant `M ⊆ X_L^2` vanishes on
every `B_D`-pattern absent from `M`, in particular on those absent from `X_L^2`. So it is an `X_L^2`-family, and
it commutes. **PASS**, at every `D ≥ 1`.

**(3b) The caveat resolves positively.** The rigidity transfer is item 2 of
`deterministic-time-lifts-inherit-quantum-rigidity`, and it uses only two things:
- that `B_D`-patterns forbidden in the row are forbidden in the lift, so the restricted row family satisfies
  (Q3) for the row;
- the local CA rules, which give `C_(gs) = C_g`.

Finite type of the row is never used. So for a closed subshift `M` with `F` acting by restrictions of cellular
automata, the lift over `F × Z^2` is a `max(D, R+1)`-rigid **subshift**, not an SFT. That is the object
(RA_free) quantifies over. Item 1 of the commutant node transfers the same way: its proof uses only the
conjugacy `x ↦ x(1, ·)` and the measure.

**(3c) Freeness.**
- The fixed set of `gσ_p` is closed and `Z^2`-invariant, so by minimality it is empty or all of `M`.
- If it is all of `M`, then `g|_M ∈ σ(Z^2)|_M`. That subgroup is central in `Aut(M)`, hence central in
  `F|_M ≅ F_2` (by (ii)), hence trivial.
- So `g|_M = id`, and `g = 1` by (ii). Finally `p = 0` by freeness of `Z^2` on `M`. **PASS.**

**Scope note (not a defect).** On main, rigidity ⇒ finite presentation (`sft-crossed-product-fp-iff-quantum-rigid`,
`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`) is stated for SFTs.
- So a non-SFT `M` would refute (RA_free) as stated for subshifts.
- It would **not** by itself give a finitely presented V-full group or crossed product. A consumer on the BH
  route that needs finite presentation should ask for `M` of finite type, or re-prove sufficiency for subshifts.

## (4) Non-hierarchical: the conclusion holds, one proof step repaired

**The step that fails.** The proof says a Toeplitz or substitutive minimal subset is "an almost 1-1 extension of
its odometer". That is right for Toeplitz, but not for substitutions in general.
- Constant-shape substitutions are finite-to-one over their maximal equicontinuous factor (MEF), with a.e. fibre
  size equal to the column number.
- The column number can exceed 1, as for Thue–Morse type examples, and then no fibre is a singleton.

**Repair, which gives more.** Suppose some fibre of `π : M → M_eq` is finite.
- By the fibre bound (item 2 of the time-lift node), the fibre-preserving part `Aut_0(M)` is finite. A
  fibre-preserving automorphism is determined by one image, and it injects into a fibre.
- `Aut(M)/Aut_0(M)` embeds in the translations of `M_eq`, which form an abelian group.
- `F ≤ Aut(M)` would then meet `Aut_0(M)` in a finite normal subgroup of `F_2`, which is trivial. So `F` would embed
  in an abelian group, which is impossible.
- Hence **every** fibre of `M` over its MEF is infinite. This excludes Toeplitz, substitutive and every other
  finite-to-one hierarchical minimal set at once, with no appeal to the profinite collapse.

## Lesson for general BH

- **Two kinds of product.** A diagonal self-product is not an external product. Rigidity of `X × X` over the same
  group needs a local mechanism in the joint alphabet, here triangle permutivity, which linear rules supply for
  free.
- **The sharp form of T1.** Find a free minimal uniquely ergodic subset of a rigid algebraic row, invariant under a
  free group of its algebraic automorphisms, all of whose fibres over the MEF are infinite. By the scope note, it
  should be of finite type if the BH consumer needs finite presentation.
