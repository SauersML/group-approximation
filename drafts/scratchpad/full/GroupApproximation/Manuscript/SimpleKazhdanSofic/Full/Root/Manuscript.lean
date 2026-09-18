import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Main
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Proof
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Corollaries
import GroupApproximation.Meta.AxiomGuard

/-!
# Root audit for `simple_kazhdan_sofic_group.tex`

This module imports the three root audit files and collects every printed label of
`simple_kazhdan_sofic_group.tex` into the single closed theorem `manuscript`.

| tex label / passage | tex lines | root theorem |
|---|---|---|
| abstract | 32–47 | `abstract_claims` |
| `thm:main` | 69–80 | `thm_main` |
| Brown's form of `thm:main` | 82–84 | `thm_main_brown_form` |
| definitions after `thm:main` | 86–109 | `thm_main_definitions` |
| the ingredients of the proof | 113–135 | `proof_ingredients` |
| `fig:models` | 137–164 | `fig_models` |
| `thm:general` | 172–187 | `thm_general` |
| remark after `thm:general` | 191–195 | `general_remark` |
| `tab:props` | 197–213 | `tab_props` |
| `eq:elementary` | 231 | `eq_elementary` |
| `sec:proof`, the ring and property (T) | 222–239 | `proof_ring_T` |
| `sec:proof`, simplicity | 240–316 | `proof_simplicity` |
| `sec:proof`, finite simple models | 317–343 | `proof_finite_models` |
| `sec:proof`, Brown's formulation | 344–355 | `proof_brown_formulation` |
| `sec:main`, proof of `thm:main` | 357–392 | `sec_main_proof` |
| `sec:main`, sharpness | 393–407 | `sec_main_sharpness` |
| `sec:main`, the Fibonacci example | 408–440 | `sec_main_example` |
| `cor:lef` | 453–461 | `cor_lef` |
| `cor:host` | 463–470 | `cor_host` |
| route of `sec:lef` | 484–488 | `sec_lef_route` |
| `lem:nn` | 489–492 | `lem_nn` |
| `lem:host` | 527–537 | `lem_host` |
| `lem:halfline` | 605–611 | `lem_halfline` |
| `cor:wp` | 683–690 | `cor_wp` |
| proof of `cor:wp` | 692–726 | `cor_wp_proof` |
| `sec:questions` | 728–738 | `sec_questions` |

Each root theorem is a conjunction of the types of landed `Full` endpoints, and `manuscript` is the
conjunction of the types of the root theorems, so every statement collected here is literally the
statement of a landed endpoint.
-/

universe u v

namespace GroupApproximation.Full.SKRoot

/-- **`simple_kazhdan_sofic_group.tex`, every printed label** (tex l.32–738): the abstract,
`thm:main` with Brown's form and the definitions, `thm:general` with its remark, `tab:props`,
`fig:models`, `eq:elementary`, the proof in `sec:proof` and `sec:main` (sharpness and the Fibonacci
example), `cor:lef`, `cor:host`, `lem:nn`, `lem:host`, `lem:halfline`, `cor:wp`, and
`sec:questions`. -/
theorem manuscript :
    type_of% @abstract_claims ∧
    type_of% @thm_main ∧
    type_of% @thm_main_brown_form ∧
    type_of% @thm_main_definitions.{u} ∧
    type_of% @thm_general.{u, v} ∧
    type_of% @general_remark ∧
    type_of% @tab_props ∧
    type_of% @proof_ingredients ∧
    type_of% @fig_models ∧
    type_of% @eq_elementary ∧
    type_of% @proof_ring_T ∧
    type_of% @proof_simplicity.{u, v} ∧
    type_of% @proof_finite_models ∧
    type_of% @proof_brown_formulation.{u} ∧
    type_of% @sec_main_proof ∧
    type_of% @sec_main_sharpness ∧
    type_of% @sec_main_example ∧
    type_of% @cor_lef ∧
    type_of% @cor_host.{u} ∧
    type_of% @sec_lef_route ∧
    type_of% @lem_nn ∧
    type_of% @lem_host ∧
    type_of% @lem_halfline ∧
    type_of% @cor_wp ∧
    type_of% @cor_wp_proof ∧
    type_of% @sec_questions.{u, v} :=
  ⟨@abstract_claims, @thm_main, @thm_main_brown_form, @thm_main_definitions.{u},
    @thm_general.{u, v}, @general_remark, @tab_props, @proof_ingredients, @fig_models,
    @eq_elementary, @proof_ring_T, @proof_simplicity.{u, v}, @proof_finite_models,
    @proof_brown_formulation.{u}, @sec_main_proof, @sec_main_sharpness, @sec_main_example,
    @cor_lef, @cor_host.{u}, @sec_lef_route, @lem_nn, @lem_host, @lem_halfline, @cor_wp,
    @cor_wp_proof, @sec_questions.{u, v}⟩

end GroupApproximation.Full.SKRoot

#audit_closed_axioms GroupApproximation.Full.SKRoot.manuscript
