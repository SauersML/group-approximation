import GroupApproximation.GGT.HullSCRelatorSeparation2NoCommute

/-!
# The two-subgroup relator chain: what it rests on

A reader's map of `GGT/HullSCRelatorSeparation2*.lean`, written so that the
manuscript's debt file can cite one place for the chain's standing hypotheses
rather than tracing them through fifty modules.  Nothing is proved here.

## What the chain delivers

`HullSC.HullTheorem51Statement₂` -- Hull's Theorem 5.1 over two hyperbolically
embedded subgroups -- from the corrected separation, `HullConeOffStatement₂`,
and DGO's Theorem 5.3.  The relator is `relatorWord₂`: a base spelling of `t⁻¹`
followed by an alternating run of deep powers of two independent loxodromics.

## The standing hypotheses, and who owes them

**1. The isolated-component bound, at four sides.**  `hgeo` and `hgeoInv` --
that a short conjugation carrying one deep power onto another leaves both
conjugators in the subgroup -- are no longer hypotheses of this chain.  They
reduce to fp-geometry's `IsolatedComponentBound`, through
`GGT.OsinComponents.mem_fam_of_conj_of_deep` and the bridge
`HullSC.exists_hgeo_of_bound`, which produces them in the shape
`HullSC.exponent_eq_of_blockMatch₂` and
`HullSC.exponent_eq_of_mirroredBlockMatch₂` consume.  What the bridge asks in
their place is that the quadrilateral `px ++ [a_s^i] ++ rx ++ revWord [a_s^j]`
be quasi-geodesic -- the same species as (2), and what the polygon theory is
built to consume.  The depth radius is the reduction's: it yields a `C` and
wants `4C ≤ rho`, so a caller designs at `max rho (4C)` and weakens with
`HullSC.notMem_relBall_of_le`.

**2. `hcount` -- the block count.**  That the distance between two vertices of
the relator is at least the number of block letters between them, less a
constant fixed before the relator is chosen.  Consumed by
`HullSC.quasiGeodesic_relatorWord₂_of_blockCount`, which is what makes the
relator `(1, |p| + c)`-quasi-geodesic.  Open, and genuinely geometric: the
four-gon material consumes quasi-geodesicity rather than producing it.

**3. The packaged polygon theorem -- Olshanskii's step (a).**  That a long
`eps`-match between two members of the symmetrized closure produces matched
blocks, with the two gaps of `GGT.OsinComponents.exists_block_span_conj` short.
The identity is landed; the bounds are fp-geometry's Cut, applied once per
orientation, each gap being an innermost end-to-start element for one of them.

**4. `HullConeOffStatement₂` and `DGOQuotientStatementGeodesic`.**  Citations:
Hull's §5, that the cone-off along a pair exists with the data
`HullSC.ConeOffData₂` records; and DGO's Theorem 5.3 in the repaired form that
carries a geodesic, `GGT/HullSCDGO.lean` having refuted the transcribed one.

**5. Torsion-freeness.**  A hypothesis about the groups the manuscript studies,
not a leaf, and the chain's only use of it is
`HullSC.noCommute_of_torsionFree`.

## What is discharged, and by what

* The diagonal of the separation -- no short pair carries a deep power onto
  itself -- from torsion-freeness, `HullSC.noCommute_of_torsionFree` over
  `GGT/OsinTheorem54SepElementaryBall.lean`.  It holds for every loxodromic;
  nothing has to be chosen.
* The rigidity input, from the bound: `HullSC.exists_hgeo_of_bound`.  Its
  degenerate branch needs no geometry -- with the second conjugator trivial,
  `x · a^i · 1 = a^j` gives `x = a^j (a^i)⁻¹`, a product of peripheral
  elements -- and the norm bounds on the conjugators are not used at all:
  the reduction wants them base-spelled, and shortness enters only through the
  quadrilateral's quasi-geodesicity.
* The same-side exclusion at adjacent components, from a deep power not lying
  in the other subgroup: `HullSC.notMem_fam_of_crossDeep`.
* The same-side exclusion over the window, from the design:
  `HullSC.exists_separated_exponents_window`, with
  `HullSC.exists_listVal_run_segment` translating the polygon's vertices into
  the run's own vocabulary.
* All four cases of step (c): `HullSC.listVal_conj_of_alignedMatch`,
  `HullSC.listVal_conj_of_mirroredAlignedMatch` and `HullSC.not_mixedMatch`,
  dispatched by `HullSC.listVal_conj_of_sym_cases`.
* `0 < |p|`, which the wrap-around argument of
  `GGT/HullSCRelatorSeparation2Locate.lean` spends, from
  `HullSC.exists_long_base_spelling`.

## Four refutations that shaped the chain

They are recorded because each closed a route that looks reasonable on paper.

* `HullSC.RelatorSeparation` as transcribed is FALSE: it quantifies over the
  diagonal `w' = w`, and a conjugator inverting the loxodromic refutes it
  (`GGT/HullSCRelatorSeparationRefuted.lean`).  The repair restores Olshanskii's
  exclusion clause `w' ≠ w`.
* The single-subgroup relator is not quasi-geodesic: its run is one component,
  and the defect grows with the exponents
  (`GGT/HullSCRelatorSeparationNotQG.lean`).  That is why the model has two
  subgroups and an alternating run, and it is also why the relator is aperiodic
  (`GGT/HullSCRelatorSeparation2Aperiodic.lean`).
* The four-gon's closing clause `r = p⁻¹` is FALSE
  (`fourGon_closing_clause_fails`), and equivalent to a centralizer claim about
  the piece's own connector -- the equivalence is
  `HullSC.conj_rotate_iff`.  The aligned case does not need it: the vertex form
  pins the connector to the four-gon's own first side, which is
  `HullSC.listVal_conj_of_rotate_eq_of_vertex_eq`.
* Lemma 4.21 in the start-to-start form is FALSE; only the innermost
  end-to-start element is bounded.  The rigidity consumes exactly two such, one
  per orientation of the boundary.
-/
