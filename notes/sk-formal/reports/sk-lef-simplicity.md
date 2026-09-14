# sk-lef-simplicity

This lane was launched 2026-09-13 ~21:22 CDT by the session -49 lead and resumed at 23:15 after the coordinator restarted. Its brief is the sk-lef-simplicity row of ct/ROSTER-sk.md, as updated by the 23:15 resume note.

## Scope (re-scoped 23:15 to the tip 37551fd93: 767 lines, md5 b55c0d23b8c59e66d36df004a1df608b; census 649cb1f80)

The note was restructured at c8b6021ca. Its "Simplicity" subsection (≈ l.151–209) now proves the simplicity clause of thm:general:

> Let a finitely generated group Λ act minimally and topologically freely on a Cantor set Z, and let R = LC(Z, F₂) ⋊ Λ … Then for every n ≥ 3, EL_n(R) is … simple …

This lane owns the general proof: every sentence of l.151–209, at Λ-generality and for every n ≥ 3 ("replace 3 by n throughout", l.131).
- skf-consequences absorbs the ℤ-case drafts (TowerCopy, SimplicityNormalSubgroup, …) and agrees the split directly with this lane.
- ct-bilateral-mf's ℤ drafts (SimplicitySmallSets, SimplicitySmallRoot, SimplicityCommutationCriterion) stay theirs. Their proof shapes are mirrored here, not imported, while they remain unlanded.

The 21:3x scope was cor:lef l.309–317 at 9047d0d3c ("the proof of Section 1 applies word for word"). That text was replaced by thm:general, so it is superseded.

## Ownership check (23:3x)

- **origin/main:** no crossed product for a group action and no group-action simplicity proof. `ClopenCrossedProduct`, `Pestov91.CrossedProduct` and `Pestov91.WitnessRing` are all over `Multiplicative ℤ`.
- **sk-lef-action:** empty `.files`, no report on origin, no crossed-product module.
- **Shared tree:** no draft with a group-action coefficient ring.

## Route and spelling

- **Ring:** `SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ`, with an instance argument `[MulSemiringAction Λ (LocallyConstant Z (ZMod 2))]` and the hypothesis `(ξ • f) z = f (ξ⁻¹ • z)`. This is exactly the printed multiplication `(f u_ξ)(f′ u_η) = f (f′∘ξ⁻¹) u_{ξη}`. Any type synonym of `LocallyConstant Z F₂` with that action (such as sk-lef-action's proposed `ActionCoeff`) specializes to it by definitional unfolding.
- **Ball:** a finite set `B ∋ e` closed under inverses, containing every ξ with u_ξ occurring in the entries of g and g⁻¹. Smallness is required over `B * B ∖ {e}` (the printed B_{2w} = B_w B_w for word-length balls), and d = n|B|. Word balls of a finitely generated Λ are instances, so this is at the printed generality or above.
- **Topological freeness,** as printed: for ξ ≠ e the fixed set {z | ξ • z = z} has empty interior.
- **Minimality:** every orbit is dense.

Paper model tests of the hypotheses:
- Λ trivial, acting on a point: R = F₂ and EL₃(F₂) is simple. Calibration only.
- Λ finite, acting freely and transitively: R ≅ M_{|Λ|}(F₂) and EL₃(R) = SL_{3|Λ|}(F₂) is simple.
- ℤ/2 acting trivially on a point: freeness fails, and EL₃(F₂[ℤ/2]) is not simple (augmentation ideal). So freeness carries the weight.

## Split with skf-consequences (agreed 23:4x)

There is one proof at Λ-generality, for every n ≥ 3.
- **This lane:** l.151–172 and 188–196. Small sets, topological freeness gives small subsets, the noncommuting root h = e_ij(e_V), k = [g,h], fu_a e_V f′u_b ∈ {0, ε_{a,b⁻¹}}, and k − I, k⁻¹ − I ∈ M_n(A_V). It produces the witness for the concrete ring.
- **skf-consequences:** l.176–186 and 197–208. ε_ab, A_V, H_V ≤ G, k ∈ H_V, H_V ⊆ K, J, the cover, K = G, `IsSimpleGroup`.
- **Interface (skf-consequences, `Manuscript/SimpleKazhdanSofic/GeneralSimplicityStatement.lean`):** an abstract covariant pair (coeff, u) and `GeneralCommutatorWitness coeff u n`. This lane instantiates it with coeff = single 1 and u ξ = single ξ 1.

## Claims

CLAIM l.152–159 GroupApproximation/Manuscript/SimpleKazhdanSofic/GeneralSmallSets.lean
CLAIM l.161–172 GroupApproximation/Manuscript/SimpleKazhdanSofic/GeneralRoot.lean (with GeneralRootCoefficients.lean)
CLAIM l.188–196 GroupApproximation/Manuscript/SimpleKazhdanSofic/GeneralCommutatorSpan.lean
Withdrawn: GeneralTower.lean and GeneralSimplicity.lean, which are skf-consequences' half.

## Sentence ledger (tip 37551fd93, keys from census 649cb1f80)

| key | l. | sentence (abridged) | carrier | status |
|---|---|---|---|---|
| a90478fb4258 | 152–154 | 1 ≠ K ⊴ G, 1 ≠ g ∈ K, w bounds the word lengths | binders of the producer; the ball B | to build |
| ac63c30b67dd | 154–156 | V small | `GeneralSmallSets.IsSmall` | to build |
| f759c1db71a3 | 157–159 | fixed sets have empty interior; moved points dense; small subsets exist | `GeneralSmallSets` | to build |
| 54ceec15a5e0 | 161 | some h = e_ij(e_V), V small, does not commute with g | `GeneralRoot` | to build |
| 9c94086f2a8c … 01c951f8d2f2 | 161–174 | commutation criterion, c e_V and e_V c, diagonal, g = cI, c = 1 | `GeneralRoot` | to build |
| 2e100de03692 … 16fd7b95d922 | 176–186 | d = n\|B\|, ε_ab, products, A_V ≅ M_B(F₂), H_V ≤ G | `GeneralTower` | to build |
| fd2fdac50185 … 46368870a699 | 188–209 | k = [g,h], the display, k ∈ H_V, H_V ⊆ K, J, cover, K = G | `GeneralSimplicity` | to build |

## Progress log

- 21:3x: ledger for the cor:lef scope at 9047d0d3c; interface messages to sk-lef-action, ct-bilateral-mf and skf-consequences.
- 23:3x: resumed and re-scoped to thm:general's Simplicity at 37551fd93; claims landed; split proposed to skf-consequences.
