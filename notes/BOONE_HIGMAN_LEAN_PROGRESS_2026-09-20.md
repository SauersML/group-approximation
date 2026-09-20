# Boone–Higman Lean progress — September 20, 2026

The combined headline theorem is **not yet proved in Lean or ready for Palomar**.
This records checked development progress, not a completed submission. No new
axioms, `sorry` proofs, or assumed literature theorems were added to certify an
unconditional endpoint.

## Checked mathematical progress

| Development | Checked result | What it does not yet prove |
| --- | --- | --- |
| [Local–global](../GroupApproximation/BooneHigmanLinear/Tulenbaev/LocalGlobal.lean) | `stAtMaximalFiniteStage` proves that an element killed over `A_M[X]` is killed over `A_s[X]` for some `s ∉ M`, for any commutative ring and rank. Its former hypothesis is removed from the local–global consumers. | The dilation principle remains an input. |
| [Finitary descent](../GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Cor29Finitary.lean) | The coefficient-localization lift and subsequent nonzero-denominator killing step prove `cor29FinitaryAt`; `Cor29Wire` now uses this proof directly. | The geometric injectivity corollary still needs excision and monic injectivity. |
| [Zariski excision](../GroupApproximation/BooneHigmanLinear/PaninAffine/PatchWire.lean) | `stZariskiExcisionAt` is proved without an excision hypothesis; the Tulenbaev/relative-presentation patching chain compiles. The checked `K2Poly/P1Core` now supplies excision and finitary descent internally. | P1 still takes dilation, the field coset step, and local Horrocks. |
| [Building stabilizer](../GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainStabilizer.lean) | Determinant valuation turns homothety into equality of lattices and proves the standard-vertex stabilizer consists exactly of integral determinant-one matrices. `buildingInputs_of` now supplies this proof. | Triangle normal forms, building-specific descent/simple connectivity, and the separate characteristic-zero nil argument remain. |
| [Higman conjugation](../GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCCommonConj.lean) | Deep splitting and reassembly prove arbitrary-depth conjugation when prefixes change with every suffix preserved. The kernel-centrality proof consumes this stronger theorem. | Centrality does not imply the kernel is trivial; H1 remains open. |
| [Diagonal cloning](../GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCSwindleDiag.lean) | Proved commutation of arbitrary elements cloned into distinct first-letter cones, constructed the diagonal homomorphism, and proved its boundary cone action and preservation of the evaluation kernel. | The diagonal has not been proved to fix that kernel pointwise. Coherent finite shuffles and their expansion identities remain. |
| [Finite shuffle algebra](../GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCSwindleShuffle.lean) | Defined the explicit free-group shuffle lift; proved incomparable-middle commutation, exact diagonal conjugation, ordered-product insertion and preservation of naturality under a matched expansion. | The shuffle's full boundary action, canonical code lifts, adapted finite tables and the final kernel identity remain. |
| [Relative automorphism action](../GroupApproximation/BHPalomar/GraphProducts/RelativeAction.lean) | Constructed the substitution action, proved transitivity, proved MIF implies faithfulness, and reduced stabilizer finite generation to the identity substitution. | The simple MIF envelope, finite presentation of the relative automorphism group, finite generation of that stabilizer, and finite diagonal-orbit count remain. |

The field-symbol generation, field-centrality, geometric presentation, and P1
reduction modules were also checked against the warm MSI dependencies. Several
previously unbuilt sources needed explicit imports, type annotations, or
corrections to dependent rewrites. These were compilation repairs, not new
assumptions or changes to their mathematical conclusions.

## Remaining headline obligations

The existing [route without Suslin absorption](../GroupApproximation/BooneHigmanLinear/CharZero/RouteNoSuslin.lean)
needs **P1, Z1 and H1** for the BH linear/metabelian conclusions. Its self-similar
host theorem needs P1 and Z1. The older four-input route is not the shortest
current route.

- **P1:** dilation, the field coset step, and local Horrocks. The core interface
  uses `FieldCosetAt` directly; the stronger wide normal form implies it but is
  not needed as a separate import. None of these three remaining statements is
  claimed proved by merely naming it as an input.
- **Z1:** finish the building argument for the base part and the independent
  nil part. Proving the standard stabilizer closes only one geometric input.
- **H1:** prove triviality of the all-swaps evaluation kernel. A central kernel
  and involutory generators alone do not establish this.
  The [finite shuffle plan](BOONE_HIGMAN_H1_SHUFFLE_PLAN.md) gives the proposed
  next proof, with its unformalized coherence and table obligations explicit.
- **PBH and graph products:** finish the action/envelope constructions and the
  four finiteness/embedding obligations above.
- **Ascending HNN extensions:** formalize the Hall/HNN reduction and its host
  machinery, then expose the intended unconditional endpoint.

These are mathematical proof obligations, not permission or compute blockers.
The combined Comparator manifest still selects the earlier four-theorem
checkpoint; the headline results have not been silently replaced by conditional
submission theorems.

## Verification and development speed

All Lean execution in this work used MSI `acn112`, the existing project/Mathlib
cache and isolated output directories under
`/projects/standard/hsiehph/sauer354/bh-finalize-20260920/`. Probes used two Lean
threads, bounded heap limits and short per-file timeouts. No local builds,
tmpfs build storage, broad cache replacement, or unrelated job termination was
used.

Moving foundational statements out of the endpoint assembly reduced the
uncached dependency closure of `K2Poly/Statements` from **137 modules to 5**.
`PolyFpK2Core`, `ElemFPK2RingEquiv` and `LocalizationStatements` hold the moved
declarations; the consumers import them directly. The shorter checked
`K2Found/Cor29Finitary` proof replaces the duplicate, now-unused
`PaninAffine/Cor29Finitary` development, which was removed after its consumer
was rewired. Proof splitting and local
opacity for large finite products resolved elaboration timeouts without
raising the heartbeat budget for those proofs.

The checked declarations' transitive axiom guards admit only `propext`,
`Classical.choice` and `Quot.sound`. A clean axiom list does not discharge a
theorem's explicit hypotheses. A combined MSI import and axiom check of the
P1 core, building inputs, H1 centrality and graph-envelope interfaces passed
in 19.9 seconds; its printed signatures retain the outstanding inputs.
Full endpoint assembly, the combined release
build, statement matching, Comparator and NanoDa replay remain release checks;
targeted development compilation does not replace them.

Logs are retained in the MSI task directories `root/logs`, `charzero`, `graph`
and `higman`/`higman-patch/logs` under the path above.

The subsequent H1 continuation checked `EnvelopeHigmanVCSwindleDiag` in 12.7
seconds and its updated consumer `EnvelopeHigmanVCSwindleProd` in 13.7 seconds.
The product-forcing statements now use the actual `higSw_diag` homomorphism;
the substantive fixed-kernel hypothesis remains explicit. All seven new
declarations and both forcing theorems passed their classical-axiom guards.
The prefix-map and independence prerequisites were also compiled in this
isolated MSI output tree. No full release build or kernel-triviality proof
is implied by these checks.

The finite-shuffle module subsequently passed in 14.9 seconds on MSI, with
eight theorem axiom guards admitting only the same three classical axioms.
Its conjugation law uses the checked diagonal cone action, and its insertion
and expansion theorems consume the new commutation and conjugation proofs.
These are constructive algebraic steps of the H1 plan, not an assertion of
the still-missing canonical code-shuffle theorem.

The next three modules checked the boundary and tree-action parts of that plan.
`EnvelopeHigmanVCSwindleAction` proves the finite pair permutation and the
shuffle's framed-cone action (MSI, 21.0 seconds).
`EnvelopeHigmanVCSwindleSupport` proves that cones belonging to incomparable
middle words are fixed (21.0 seconds).
`EnvelopeHigmanVCSwindleCodeAction` consumes both to prove the action update
under a single leaf expansion and existence of a lift for every finite expansion
tree (16.7 seconds). Their theorem guards admit only the same three classical
axioms. The construction still needs a canonical lift with exact coherence;
the existence theorem does not discharge that obligation or prove H1.

`EnvelopeHigmanVCSwindleSeed` then checked exact seed conjugation and naturality
in 25.0 seconds on MSI. It consumes the code-action interface, splits the leaf
swap into child swaps, and applies the presented group's exact cone-conjugation
theorem to each factor. Both theorem axiom guards passed. The remaining H1 work
is canonical code-lift coherence, compatible refinement tables and the final
kernel telescope; seed algebra is no longer a pending proof step.
