# Fleet traps (cross-lane, append-only)

One line per trap: `- (lane, date) symptom → cause → fix.` Lanes APPEND at the end; never edit or
reorder another lane's line; the lead merges duplicates. Before a SECOND failed probe on the same
error, grep this file for a word from the error message. Cross-lane facts belong here, not only in
your lane report (a lane report is read by people already looking at that lane).

## Elaboration and names
- (cc-thom, cc-relative, 09-06) `Functor.map_id` rewrites a pattern shaped like `id <$> x` → under `open CategoryTheory` the name also resolves to Lean's monad `Functor` → write `CategoryTheory.Functor.map_id` in full and prove the fact once.
- (cc-relative, cc-bundle, 09-06) heartbeat timeouts at UNRELATED lines, or "function expected" → an unimported name was auto-bound as a variable by `autoImplicit` → look for the missing import; never raise `maxHeartbeats` for this.
- (cc-relative, cc-bundle, 09-06) a correct file fails under the probe flags with a message that reads like a style note → deprecation renames are ERRORS under `-DwarningAsError` → grep the failed log for `deprecated` before reading it. Known at the pin: `push_neg`→`push Not`, `continuous_finset_sum`→`continuous_finsetSum`, `finRotate_succ_apply`→`finRotate_apply`, `Fin.coe_castSucc`→`Fin.val_castSucc`.
- (cc-bundle, 09-06) `unknown free variable _fvar.NNN` on a membership proof written inline in an anonymous constructor → extract it as a named lemma and pass it.
- (cc-lix-odd, 09-06) bare failure to synthesize an instance at an application, naming neither the class nor the definition → the top space is a plain `def`, which instance search does not unfold → ascribe the instance on the unfolded product, or make the def reducible.
- (cc-lix-odd, 09-06) contractibility transfers along a homeomorphism from the TARGET to the source; the wrong direction is a bare instance failure with no direction signal.
- (cc-lix-odd, 09-06) two subtypes of propositionally equal sets (e.g. `U ∩ V` vs `V ∩ U`) do not compose; bridge with the set-congruence homeomorphism.
- (cc-projective, 09-06) a `Fin` sum cannot become a range sum while the summand's cast depends on the `Fin` bound → give the coefficient family a TOTAL form first; an index step whose coefficient type moves with the index is a dependent rewrite → transport lemma by `subst` + proof irrelevance, not `rw`; `Fin.ext` on a raw arithmetic equation leaves both indices as metavariables → name the equation in a `have` with explicit values; an anonymous `Fin` constructor's coercion is its value definitionally but `omega` treats it as an atom → restate the degree goal first; `Finset.range_subset` does not take an inequality at this pin.
- (cc-cartan, 09-06) `map_add` does not fire on the cochain coboundary (not a bundled additive map at that spelling) → `cochainCoboundary_add`; a `by omega` bound inside a `Fin` literal captures hypotheses and blocks a later `subst`; omega cannot see through the successor on a `Fin`; a rewrite whose pattern is visibly present can still fail to match → supply the same equation as a congruence term.
- (cc-thom, 09-06) the ambient of a relative pair must be a `TopCat`, not a bare type (a subset cannot recover `TopCat.of`).
- (cc-bundle, 09-06) a Python end-marker search without a start offset can match an EARLIER occurrence, and `str.replace("", new)` silently PREPENDS → symptom: parse error at line 1 plus "import must be first"; pass the start index and grep the file head before probing.

## Library facts at the pin
- (cc-relative, 09-06) the usable five lemma is `LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective` in `Mathlib/Algebra/FiveLemma.lean` (unbundled ALGEBRA file), NOT in `CategoryTheory/Abelian/DiagramLemmas/Four.lean` (third slot only) → for anything over `ModuleCat`, grep the unbundled algebra files too; three lanes concluded absence by searching only the categorical half.
- (cc-relative, 09-06) no five lemma reaches degree zero of a pair sequence (nothing to the left of the relative group) → degree zero needs its own argument (injectivity of `relToAbs` there).
- (cc-bundle, 09-06) no continuous inverse square root of a positive matrix field, no polar decomposition, no tensor product / dual / Hom of bundles in the projection model; at RANK ONE normalise `A·p` by its Hilbert–Schmidt norm instead (`lineIntertIso`, hypotheses: carries into the fibre, does not kill it). "The invertibles are connected" gives a path POINTWISE only.
- (cc-cohom-api, 09-06) `Nontrivial (TotalH X)` is `nontrivial_totalH_inst` from `[Nonempty X]`; `Nonempty (Proj p)` is `RelativeSupport.nonempty_proj` from `0 < p.rank x` (not an instance: introduce by `haveI`).

## Statements and seams
- (cc-thom, cc-lix-odd, cc-cohom-api, 09-06) two green files can be about DIFFERENT SPACES and no probe detects it (total-space pair vs projectivised pair; `(Y × S⁵) × S¹` vs `S¹ × (S⁵ × Y)`) → rule 17: read both statements verbatim from origin and name the space, map, class and index each carries, before either side builds on the other.
- (cc-bundle, cc-projective, cc-wu, 09-06) a hypothesis that occurs exactly ONCE in the body is the tell of an over-ask (a structure requested where a property is consumed); a Leray–Hirsch structure for a flag TOWER cannot exist (free on monomials in several classes) → rule 16.
- (cc-cohom-api, cc-thom, 09-06) model-test index arithmetic before proving: the restriction one degree below the top of an LH column is a BIJECTION between families of equal size, not a projection; truncated subtraction makes the statement FALSE at rank zero → carry `1 ≤ r`. Transports hurt when the index changes VALUE, not type.
- (cc-bundle, cc-wu, cc-lix-odd, 09-06) state a rank relation ADDITIVELY (`rank + n = r`), never as a natural subtraction; a dimension that is right but asserted rather than derived is invisible to review.
- (cc-lix-odd, cc-thom, 09-06) a file visible on the shared disk is not a file landed on the branch → `git cat-file -e origin/main:<path>`; an absence claim names the search that was run and the time (rules 14, 15).
- (cc-cartan, 09-05) a lemma whose hypothesis occurs only in its conclusion is unusable as a rewrite rule and fails by doing nothing; a definition is pinned down only by the first property distinguishing it from its neighbours — prove that property EARLY (composite B lacked its middle transposition through four green probes).
- (cc-relative, cc-thom, 09-06) an isomorphism in a slot that the chain needs as a MAP discharges nothing; the content is the equation identifying the composite.
