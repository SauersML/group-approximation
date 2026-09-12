# leavitt-ge: Tits' lemma and the GHB(7) coset complex (CCKW T2)

Target T2 is `Systolic.SimplyConnected KMSGroup.CCKW.cosetComplex`, where the coset complex is the
Tits complex of `GHB(7)` with vertex groups `⟨a, b⟩`, `⟨c, b⟩` and `⟨c, a⟩`.

## Modules

| module | content | state |
|---|---|---|
| `Kazhdan/CCKWTitsMoves.lean` | `titsComplex G H`, the relation `Rep`, adjacency and triangles through a common representative, destuttering, and `simplyConnected_of_moves` | compiled; on main |
| `Kazhdan/CCKWTitsTypedWords.lean` | typed letters `Letter H`, `val`, `BaseMove` (merge, drop, retype), `TypedMove`, `simplyConnected_of_typedWordProblem`, `connected_of_generated` | compiled (probe 0912-004542-21107); on main, unverified |
| `Kazhdan/CCKWTitsPresentation.lean` | `VertexPresentation`, the letter-by-letter lift of free-group words, `typedWordProblem`, `simplyConnected_of_vertexPresentation`, `connected_of_vertexPresentation` | fix landed 5bef74495; probe of Presentation and GHB running |
| `Kazhdan/CCKWTitsGHB.lean` | `ghbVertexPresentation` (every relator lies in one vertex group) and the two endpoints | fix landed 5bef74495; probe running |

## Endpoints

```lean
theorem GroupApproximation.CCKWTits.cckwCosetComplex_simplyConnected :
    Systolic.SimplyConnected KMSGroup.CCKW.cosetComplex
theorem GroupApproximation.CCKWTits.cckwCosetComplex_connected :
    KMSGroup.CCKW.cosetComplex.G.Connected
```

Both come from the general statements:

```lean
theorem simplyConnected_of_vertexPresentation (V : VertexPresentation R H) [DecidableEq S] :
    SimplyConnected (titsComplex (PresentedGroup R) H)
theorem connected_of_vertexPresentation (V : VertexPresentation R H) [DecidableEq S] :
    (titsComplex (PresentedGroup R) H).G.Connected
```

A `VertexPresentation R H` gives, for each `i`, a set `Stype i` of generators such that
`H i = (closure (of '' Stype i)).map (PresentedGroup.mk R)`. It also gives a type `τ s` with
`s ∈ Stype (τ s)` for every generator, and puts every relator in `closure (of '' Stype j)` for
some `j`. There are no literature inputs.

## Probe history

- 0912-004542-21107: CCKWTitsMoves and CCKWTitsTypedWords compiled. CCKWTitsPresentation was red with
  - an unused `DecidableEq S` on `memH` and `mk_eq_one_of_mem`;
  - the reverted hypothesis in `tw_of_red`;
  - "Unknown identifier `V`" in `typedWordProblem`, `generated` and both endpoints;
  - the `mk (x :: L)` split in `val_liftT`.

  CCKWTitsGHB was not built. All four were fixed in 5bef74495.
