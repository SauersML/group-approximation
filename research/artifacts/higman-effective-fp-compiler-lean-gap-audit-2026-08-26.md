# Lean audit: from an r.e. normal subgroup to an explicit finite presentation

**Snapshot:** 2026-08-26.  **Method:** declaration-by-declaration repository
audit; no external theorem is accepted as an input.  This note corrects the
finite-output conclusion of
`fp-mf-pi2-compiler-audit-2026-08-25.md`: the research-level Mikhailova/rope
claims have no corresponding Lean implementation and do not inhabit the
finite-output compiler interface.

## 1. The exact endpoint that is still uninhabited

The recursive switch is fully explicit up to a standard recursively enumerated
presentation:

```lean
ParametricRecursiveSwitchPresentation.parametricSwitchEnumeratorCode
ParametricRecursiveSwitchPresentation.standardCarrierEquivParametricSwitch
```

The finite-output endpoint is only an interface:

```lean
structure HereditaryPropertySwitchCompleteness.FinitePresentationSwitchCompiler
    (P : (H : Type) -> [Group H] -> Prop) where
  compile : Code -> PresentationCodes.PresentationCode
  computable_compile : Computable compile
  correct : forall c, AdianRabinGeneral.codeProperty P (compile c) <->
    InfiniteDomain c
```

There is no inhabitant.  In particular, no Lean file implements a Mikhailova
compiler (there is no Lean declaration or module named `Mikhailova`).

For an embedding compiler, `correct` is too weak: the negative branch needs
the source group to inject.  The missing proof-relevant output should carry a
finite code and target words for the source generators.  For a fixed finite
source rank `n`, the useful kernel statement is of the following form.  If
`N_e` is the normal closure of the relators enumerated by program `e`, then

```text
targetValue (compile e) (substitute (embedRaw e) v) = 1
  <-> rawToFree n v belongs to N_e.
```

Here `compile : Code -> PresentationCode` and
`embedRaw : Code -> Nat -> RawWord` must both be computable.  This single iff
defines the homomorphism on the quotient, proves that its kernel is exactly
`N_e`, and makes the embedding words explicit.  No current structure states
this.

## 2. What the semantic Higman lane actually proves

The existing endpoint is semantic and existential:

```lean
structure REBenign where
  benign : forall n N, N.Normal ->
    REPred (fun v : RawWord => rawToFree n v ∈ N) -> Benign N

structure REBenignTF where
  benign : forall n N, N.Normal ->
    REPred (fun v : RawWord => rawToFree n v ∈ N) ->
    Nonempty (TorsionFreeBenignWitness N)

theorem fpOvergroup_of_fgRecursive
    (h : REBenign) (p : FGRecursive G) : Nonempty (FPOvergroup G)
```

These declarations do **not** expose an enumerator index, a relator list, a
presentation code, or target words.  `BenignWitness` and `FPOvergroup` carry an
abstract type `K`, a `Group K` instance and an `IsFinitelyPresented K`
instance.  `fpOvergroup_of_benign` constructs another abstract HNN carrier.
Consequently even a future inhabitant of `REBenign` would prove existence of a
finitely presented host, not a computable finite-output compiler.

`PresentationCodes.exists_code_mulEquiv` cannot repair this: it uses classical
existence to choose a code for an already finitely presented semantic group.
It is not uniform in an r.e. index.  `PresentationCodeList.codeOfList` is the
correct computable final constructor, but it applies only after an explicit
finite relator list has been constructed.

## 3. Status of the four requested Higman components

### `REBenign` / `REBenignTF`

Neither structure is inhabited.  `reBenign_of_reBenignTF` is only a forgetful
adapter.  `reBenignTF_of_inputs` is conditional on the three structures below.
There are no `sorry`, `admit`, or axioms in this lane; the missing statements
are represented honestly as uninhabited structures.

### `OperationClosures`

The old summary is stale in several favorable ways:

* `Seq.benignTF_ASub_Sset` proves the base `S` case.
* `operationClosures_rho` proves `rho`.
* `benignTF_rowSub_piV` proves the positive half-row.
* `operationClosures_of_five_inputs` removes the base from the input list.

The sharp full constructor still needs:

```text
Omega.OmegaInput
forall B, BenignTF (ASub B) -> BenignTF (ASub (tauOp B))
BenignTF (Agree.rowSub Agree.zetaV)
BenignTF (Agree.rowSub (ker (Split.killOn Seq.evenIdx)))
```

The last two have only transfer lemmas from the corresponding basis-image
subgroups:

```lean
benignTF_rowSub_zetaV
  : BenignTF (Agree.zetaV.map Row.basisHom) -> ...

benignTF_rowSub_ker_killOn_evenIdx
  : BenignTF ((ker (Split.killOn Seq.evenIdx)).map Row.basisHom) -> ...
```

`OmegaTowerInput` is only a repackaging of `OmegaInput`; it too is uninhabited.
The swap/carrier files reduce the `tau` route to further witness structures but
do not construct one.

There is a genuinely shorter route.  `TauRouteC.lean` defines
`OperationClosuresTF`, omitting `tau`, and
`operationClosures_of_inputs_tauFree`.  With the now-proved base and half-row,
its open closure inputs are exactly:

```text
Omega.OmegaInput
BenignTF (Agree.zetaV.map Row.basisHom)
BenignTF ((ker (Split.killOn Seq.evenIdx)).map Row.basisHom)
```

This avoids the general `tau` closure.

### `HigmanTheoremThree`

It is still uninhabited.  The reduction to
`EnumeratedRangeGenerated` is proved, and the computable trace relation is now
proved by `TraceRelationRE.reset_blockPairSet_traceRel`.  Explicit traces give
the range-to-projection half.  Two substantive items remain:

1. `BoundedWindowRE`:

   ```lean
   generated : forall n B, REset B -> B ⊆ Seq.windowSupport n ->
     Seq.HigmanGenerated B
   ```

2. the reverse trace projection statement: every anchored trace determines
   one enumeration index and hence projects to `seqOfList (c r)`.

The newer atom, variable, addition and primitive-recursion modules build a
large finite-coordinate calculus, but no theorem compiles an arbitrary
`REPred` into `CoordHigman`; equivalently, no term inhabits `BoundedWindowRE`.

`TauRouteC.HigmanTheoremThreeTF` is also uninhabited.  Repository search finds
no use of the `tau` constructor in the newer arithmetic/trace modules, but all
those theorems currently return `Seq.HigmanGenerated`, not
`Seq.HigmanGeneratedTF`.  There is only a map TF-to-full, not full-to-TF.
Thus route C requires retyping or abstracting that proof chain; absence of a
textual `tau` use does not itself produce the strengthened theorem.

### `TransportSectionFive`

`transportSectionFive_of_parts` reduces this structure exactly to:

```lean
Transport.CodeRE
Transport.CompletionLemma
Transport.UnConjugation
```

Their fields are respectively:

```text
code_re    : r.e. membership in N -> REset (codeSet n N)
section_mem: w ∈ N -> sectionHom n w ∈ codeSub n N
unconj     : BenignTF (Seq.ASub B) ->
             BenignTF (closure (Seq.bElt '' B))
```

None is inhabited.  `TransportStar.unConjugation_of` reduces the third to the
single fixed subgroup statement `ConjugatorGraph.graph_benign`; that structure
is likewise uninhabited.  The smallest isolated open obligation in the entire
semantic chain is `CodeRE` (pure coding/computability).  The narrowest open
free-group obligation is `CompletionLemma`.  Closing either alone does not
close Section 5.

## 4. The shortest zero-literature semantic route

For a normal subgroup already lying in a finite-rank free group, the shortest
current route is:

1. Prove the two basis-image row benignness statements and `OmegaInput`.
2. Retype the Section 2 arithmetic/trace development to
   `HigmanGeneratedTF`, prove the reverse projection identity, and close the
   finite-coordinate r.e. compiler (`BoundedWindowRETF`).
3. Prove `CodeRE`, `CompletionLemma`, and `ConjugatorGraph.graph_benign`.
4. Add the one-line missing tau-free assembly

   ```text
   h3.transport (benignTF_ASub_of_re_tauFree h1 h2) : REBenignTF.
   ```

5. Apply the already-proved rope normal forms.

This avoids `tau` completely.  It still lands only in an abstract
`Nonempty (FPOvergroup ...)`.

If the source is the repository's actual parametric event-ray presentation,
there is an earlier countable-to-finite-rank step.  `BridgeEffective` remains
conditional on `BridgeWordProblem.ExtPresentation`:

```lean
pres : forall A g w,
  evalRaw (extGen g) w = 1 <->
    freeEval w ∈ Subgroup.normalClosure (relSet g)
```

This structure is uninhabited.  Therefore the current countably generated
switch cannot simply be fed to the finite-rank `REBenign` statement.

## 5. Additional work required for an actual finite-output compiler

After the semantic route is closed, a separate effective reification is still
necessary:

* replace bare `REPred` hypotheses by explicit program/search indices;
* make every direct product, amalgam and HNN presentation constructor return
  an explicit finite generator count and relator `List`;
* propagate explicit words for every embedding through those constructors;
* prove the final raw-word kernel iff;
* feed the resulting list to `PresentationCodeList.codeOfList` and prove the
  compiler and embedding-word maps computable.

This is not bookkeeping already supplied by `IsFinitelyPresented`: that class
forgets the chosen finite presentation, and `Nonempty`/classical choice forgets
uniformity.  It is also exactly the data needed by the Mikhailova fiber-product
proposal, so that proposal cannot be used to bypass this layer.

## 6. Bottom line

The repository now has a complete explicit **recursive-presentation** switch
and significant first-principles pieces of Higman's semantic construction.  It
does not yet have either:

1. an unconditional term of `REBenign`/`REBenignTF`; or
2. a computable map from the recursive switch to
   `PresentationCodes.PresentationCode` with embedding words.

The tau-free route is the shortest semantic path.  The effective finite-code
reification is an independent required layer, not a consequence of closing
the semantic structures.
