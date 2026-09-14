# sk-strong-4 plan: the sharp boundaries of the note's method

Lane lens (ROSTER-D): exactly where the method stops — acting groups, coefficients, ranks,
approximation types — stated as clean iff theorems.

## What is already owned (I will cite, not redo)
- **Acting group Z, the hypotheses on X.** `subshift-elementary-group-simple-iff-infinite-minimal`
  and `crossed-product-el-kazhdan-iff-finite-field-and-subshift` (sk-hypotheses-sharp, 156ccae476):
  simplicity iff infinite minimal; (T) and finite generation iff finite field and subshift;
  `crossed-product-gl-n-has-infinite-cyclic-index-quotient` for EL versus GL.
- **Beyond Z.** `finite-model-subshift-elementary-groups-simple-kazhdan-lef`,
  `free-subshift-with-finite-models-forces-rf-group`,
  `rf-groups-have-free-minimal-subshifts-with-finite-models` (sk-general-actions-a, e3d0976807).
- **The converse direction.** `lef-el-groups-force-exactly-matricial-simple-ring` (rank N ≥ 4),
  `window-lef-subshifts-give-matricial-crossed-products`, and sk-general-actions-b's virtually
  cyclic conjecture (f140bf629d, cefce10e0a).
- **Coefficients.** sk-coefficients (5776c97bfc): every F_q and n ≥ 3 modulo a finite centre;
  the exact centre; infinite fields lose finite generation.
- **Rank 2.** sk-el2 owns EL_2. sk-hypotheses-sharp settled the cyclic-factor case.
- **Approximation types.** `steinberg-elementary-groups-are-simple-mod-centre`,
  `free-group-cantor-elementary-group-lef-iff-invariant-measure`, the paradoxical side
  (S_∂ nonsofic), `gap-sofic-approximations-are-local-embeddings` (sk-fp-sofic-a).

## The gap I take
`finite-model-subshift-elementary-groups-simple-kazhdan-lef` ends with the scope sentence
"Topological freeness is not enough for the tower partition; for that case use
`steinberg-elementary-groups-are-simple-mod-centre`." Every lane downstream inherits that
freeness hypothesis: sk-universal-embedding-a had to prove `rf-toeplitz-subshifts-act-freely`
at every point, because Theorem T supplies only a free dense orbit.

**My claim: the freeness is an artifact of one step, and the sharp hypothesis is topological
freeness.** The tower partition is indeed unavailable — a point with a nontrivial stabilizer has
no small neighborhood — but the proof never needs a partition. It needs enough small clopen sets
to kill locally constant coefficients, and the small sets cover a dense open set, which is enough
because a locally constant function vanishing on a dense set vanishes.

## Targets
1. **Tower lemma, as an iff.** For a countable group acting on a Cantor set, TFAE: the action is
   topologically free; for every finite `F ⊆ Γ \ {e}` and every nonempty open `U` there is a
   nonempty clopen `V ⊆ U` with `γV ∩ V = ∅` for all `γ ∈ F`. This is the exact boundary of the
   tower construction, and the failing direction is one line.
2. **Simplicity under topological freeness, by the note's own argument.** Minimal plus
   topologically free plus `F_2` gives `EL_n(LC(X,F_2) ⋊ Γ)` simple with trivial centre, `n ≥ 3`,
   with no freeness anywhere. The replacement for the partition step is the density argument above.
3. **The iff for the group.** For `n ≥ 3`: `EL_n(LC(X,F_2) ⋊ Γ)` is simple iff the action is
   minimal and topologically free. Necessity: a proper closed invariant set or a fixed clopen set
   gives a proper nonzero ideal, and a proper nonzero ideal gives a proper nontrivial normal
   subgroup. This is the general-`Γ` form of sk-hypotheses-sharp's Z theorem.
4. **The consequence other lanes want.** A dense free orbit implies topological freeness in one
   line, so sk-universal-embedding-a's freeness lemma is not needed and Theorem T is enough as it
   stands.
5. **A boundary map** of every iff above with its owner node, marking which direction is proved,
   which is open, and where each hypothesis is used.

## Not in scope
EL_2 (sk-el2), the centre formula (sk-coefficients), rank 3 versus 4 in the LEF converse
(recorded as open, not attacked), the Z^2 soficity question (sk-fp-sofic-b).

## Deliverables
`research/artifacts/sk-strong-4-boundaries-2026-09-13-part{1,2}.md`, the claims and routes for
targets 1–3, a §6 proposal, and review requests in `sk/queue/sk-verify-4.txt`.
