---
rg: 2
id: pro-unipotent-magnus-steps-put-one-relators-in-h
kind: claim
title: When both extreme letters of a Magnus rewrite have nonzero exponent sum, solving for the top letter in the rational pro-unipotent completion of the free window gives an edge-injective target, so the Magnus HNN step is a strict reduction to its base; this puts all 128 length-15 one-relators of the (3,1,3) shape in H, the 32 unit-monodromy words included, and leaves 26 open words through length 15, all with e_0 = e_m = 0
distinct_from:
  edge-injective-quotients-give-hughes-free-division-rings: its item 2 reduces a Magnus HNN of span one to its base through a map to Z; item 1 here is the same reduction for every span m with e_0 e_m ≠ 0, with a target that is not finitely generated and not residually nilpotent. Its item 4 (root towers) needs a_m in a single syllable; here a_m may occur anywhere.
  magnus-segment-steps-put-one-relator-groups-in-h: its rule 1 and the retract rule climb segments along cyclic edges with maps to Z; here the whole HNN step is taken at once, along the rank-m window, and every map to Z may kill a.
  malcev-root-steps-put-commutator-root-one-relators-in-h: its rule N solves for a root in a Mal'cev completion of a free nilpotent group with unipotent shift; here the completion is of the window and the shift acts on H_1 by the companion matrix of e_m x^m + ... + e_0. Its item 3 frontier (e = (0, ε, 0)) is exactly what is left, and item 3 here says why no target of this kind reaches it.
  mapping-torus-targets-fail-rank-2-window-one-relators: that excludes residually torsion-free nilpotent targets and mapping tori with finitely generated fibre for 96 of the 128 words, and leaves 32 open; the target here has a fibre that is not finitely generated, and certifies all 128.
  bg-shift-chains-die-in-residually-linear-alphabets: that kills forward BG chains in residually solvable groups; item 3 here is the same kind of statement for G(1,k) and the class 𝒮, recorded to answer which targets item 3 of the Mal'cev node leaves.
  kaplansky-zero-divisor-conjecture: no case of the conjecture changes; torsion-free one-relator groups already satisfy it (Higman; Brodskii, Howie).
artifacts:
  - experiments/non-residually-solvable-targets-2026-09-18/prounipotent_step_certify.py
  - experiments/non-residually-solvable-targets-2026-09-18/ruleS-L14-L15.txt
  - experiments/non-residually-solvable-targets-2026-09-18/periodic_quotient.py
  - experiments/non-residually-solvable-targets-2026-09-18/unit-L15.json
  - experiments/non-residually-solvable-targets-2026-09-18/periodic-quotient-Phi3.txt
---

**ESTABLISHED** (written proof, unreviewed) by [[pro-unipotent-magnus-steps-put-one-relators-in-h-proof]].
Item 1 is a new rule, item 2 is its count on the census, and items 3 and 4 say where it stops. Nothing is new for
the zero-divisor conjecture.

**Setting.** As in [[malcev-root-steps-put-commutator-root-one-relators-in-h]]:
- `𝓗` is the class of [[vertex-injective-quotients-give-hughes-free-division-rings]]: closed under subgroups,
  extensions and directed unions, and containing every residually torsion-free nilpotent group.
- `G = <a, t | r>` with `t` of exponent sum `0`. The Magnus rewrite is `r' ∈ F(a_0, …, a_m)`, with
  `a_i = t^{-i} a t^i`, cyclically reduced and involving `a_0` and `a_m`. Its exponent vector is
  `e = (e_0, …, e_m)`, and `f(x) = e_m x^m + … + e_1 x + e_0`.
- `B = <a_0, …, a_m | r'>` is the Magnus base. `G` is the HNN extension of `B` along the window
  `A = <a_0, …, a_{m-1}>`, with `t^{-1} a_i t = a_{i+1}`. `A` and `<a_1, …, a_m>` are free of rank `m`
  (Freiheitssatz).

## Theorem

1. **Rule S (pro-unipotent step).** Let `m ≥ 1` and `e_0 e_m ≠ 0`. Then `G ∈ 𝓗` if and only if `B ∈ 𝓗`.
   - The target. `L̂` is the completed free Lie algebra over `Q` on `X_0, …, X_{m-1}`, and `Û = exp(L̂)` is the
     group of group-like elements of `Q<<X_0, …, X_{m-1}>>`.
   - There is a unique `Z ∈ L̂` with `r'(e^{X_0}, …, e^{X_{m-1}}, e^Z) = 1`. Its linear part is
     `Z_1 = −(1/e_m) Σ_{i<m} e_i X_i`.
   - The continuous Lie map `T` with `X_i ↦ X_{i+1}` (`i < m − 1`) and `X_{m-1} ↦ Z` is an automorphism of `L̂`.
     On `H_1` it is the companion matrix of `f/e_m`, with determinant `(−1)^m e_0/e_m`.
   - `a ↦ e^{X_0}`, `t ↦ s` defines `φ: G -> Û ⋊_T Z`, with `s^{-1} u s = T(u)`. It sends `a_i` to `e^{X_i}`
     for `i < m` and `a_m` to `e^Z`. It is injective on `A`, since it sends a basis of `A` to a basis of a free
     group (Magnus).
   - `φ(G) ∩ Û` is residually torsion-free nilpotent and `φ(G)/(φ(G) ∩ Û)` is cyclic, so `φ(G) ∈ 𝓗`. Item 1 of
     [[edge-injective-quotients-give-hughes-free-division-rings]] gives `G ∈ 𝓗` when `B ∈ 𝓗`.
   - For `m = 1` the target is `Q ⋊_{−e_0/e_1} Z`, and this is the span-one reduction of item 2 there. For
     example, `BS(2, 3)` reduces to the trefoil group.
2. **Census** (`prounipotent_step_certify.py`, output `ruleS-L14-L15.txt`). The script checks the hypotheses,
   solves for `Z` in `Q<X>` truncated at degree 6, and checks that the relation holds to that degree, that `Z`
   is primitive (coproduct test) and that `det T ≠ 0`.
   - **All 128 words of the `(3, 1, 3)` shape at length 15** (`w313-L15.txt`) are certified. Their base is
     `F(a_0, a_2)`, because `a_1` occurs once. So all 128 lie in `𝓗`. This covers the 32 KILL words, the 64
     ASC words and the 32 UNIT words of [[mapping-torus-targets-fail-rank-2-window-one-relators]].
   - Of the 136 open words of `frontier-L15.txt`, 128 are certified. The 8 left have `e = (0, −3, 0)`.
   - None of the 18 words of `frontier-L14.txt` is certified. In a basis with a letter of exponent sum `0`
     (after a Nielsen move for 10 of them) their rewrite has `e = (0, ±2, 0)`.
   - So **26 words of length at most 15 remain open** (18 of length 14, 8 of length 15). For all of them
     `e_0 = e_m = 0`, `f` is a monomial, and `H_1(ker(G -> Z); Q) = 0`. Since rule S forces this module to have
     dimension `m ≥ 1`, rule S applies to them in no basis.
3. **Baumslag–Gersten targets are not residually 𝒮.** Let `𝒮` be the class of item 3 of the Mal'cev node:
   groups with a finite normal series with torsion-free abelian factors. Let
   `G(1, k) = <a, b | (a^b)^{-1} a (a^b) = a^k>` with `k ≠ 1`.
   - Every map from `G(1, k)` to a group in `𝒮` kills `a`. So `G(1, k)` is not residually 𝒮.
   - [[baumslag-gersten-group-is-hughes-free-embeddable]] puts `G(1, k)` in `𝓗` for every `k ≠ 0`.
   - So item 3 of the Mal'cev node does not exclude family C targets of Baumslag–Gersten type. It excludes
     every target of item 1's kind: `Û ⋊_T Z` is residually 𝒮, because `T` preserves the degree filtration.
4. **Periodic fibres fail for the `Φ_3` words** (`periodic_quotient.py`, output `periodic-quotient-Phi3.txt`).
   For the 8 UNIT words with `f = ±Φ_3 = ±(x^2 + x + 1)`:
   - `N_3 = <a_0, a_1, a_2 | the three cyclic shifts of r', indices mod 3>` has `H_1 = Z^2`. Tietze moves
     eliminate `a_2` and leave two nonempty reduced relators in `a_0, a_1`. So `F(a_0, a_1) -> N_3` is not
     injective.
   - So no map `φ` with `φ(t)^3` centralising `φ(a)` is injective on `A`. The target of item 1 has `T^3`
     unipotent on `Û`, not trivial.
   - For `Φ_6` the analogous `N_6` has a 3-generator presentation with `H_1 = Z^2`, and nothing is claimed.

## What is new, and what is not

- **Nothing for the zero-divisor conjecture**, as for the other segment nodes: torsion-free one-relator groups
  are locally indicable.
- **Hughes-free existence** in characteristic `p` and for crossed products over every division ring, for the
  128 length-15 words of item 2. By item 4 of the Mal'cev node none of them passes C'(1/6), so none is known
  to be virtually compact special.
- **The mechanism.** A map to `Z` cannot see the window when `a` is torsion in `H_1(G)`. A nilpotent target
  cannot either, because the shift must act unipotently. The completed free group of the window solves for the
  top letter as soon as `e_m ≠ 0`, and the shift is invertible as soon as `e_0 ≠ 0`. Its action on `H_1` is
  the companion matrix of `f`, so its eigenvalues are the roots of `f`. For the UNIT words these are the
  cube or sixth roots of unity or the golden units that item 3 of the mapping-torus node asks for. The fibre
  is not finitely generated, which is what that node leaves open.
- **The census.** The open part of the census through length 15 drops from 154 words to 26.

## Where it stops

- **The 26 words.** All have `e_0 = e_m = 0`. The top letter then enters `log r'` only through brackets and
  cannot be solved for in degree one.
  - By item 3 of the Mal'cev node a target for their steps is not residually 𝒮. Every completion whose shift
    preserves a filtration with torsion-free abelian layers is residually 𝒮, so no variant of item 1 works.
  - Candidate targets must be in `𝓗` but not residually 𝒮. Examples are `G(1, k)` (item 3) and the
    elementary amenable, locally-solvable-by-`Z` group of
    [[baumslag-gersten-elementary-amenable-quotient-keeps-a]], if it lies in `𝓗`.
- **More generators.** Item 1 is stated for two-generator groups. The Magnus hierarchy of a longer relator
  passes through bases with more generators. There the analogue would solve for every top letter at once,
  and it needs a nonzero exponent condition for each generator.
