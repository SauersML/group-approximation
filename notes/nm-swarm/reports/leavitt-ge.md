# leavitt-ge: Tits' lemma and the GHB(7) coset complex (CCKW T2)

Target T2 is `Systolic.SimplyConnected KMSGroup.CCKW.cosetComplex`, where the coset complex is the
Tits complex of `GHB(7)` with vertex groups `⟨a, b⟩`, `⟨c, b⟩` and `⟨c, a⟩`. It is proved, with
no literature inputs.

## Modules

All four compiled in probe 0912-094055-42831 (PROBE GREEN, BUILT `GroupApproximation.Kazhdan.CCKWTitsGHB`,
base 8836fadca). Their bytes on main equal the compiled bytes. None is wired into the root.

| module | content |
|---|---|
| `Kazhdan/CCKWTitsMoves.lean` | `titsComplex G H`, the relation `Rep`, adjacency and triangles through a common representative, destuttering, and `simplyConnected_of_moves` |
| `Kazhdan/CCKWTitsTypedWords.lean` | typed letters `Letter H`, `val`, `BaseMove` (merge, drop, retype), `TypedMove`, `simplyConnected_of_typedWordProblem`, `connected_of_generated` |
| `Kazhdan/CCKWTitsPresentation.lean` | `VertexPresentation`, the letter-by-letter lift of free-group words, `typedWordProblem`, `simplyConnected_of_vertexPresentation`, `connected_of_vertexPresentation` |
| `Kazhdan/CCKWTitsGHB.lean` | `ghbVertexPresentation` (every relator lies in one vertex group) and the two endpoints |

## Endpoints

```lean
theorem GroupApproximation.CCKWTits.cckwCosetComplex_simplyConnected :
    Systolic.SimplyConnected KMSGroup.CCKW.cosetComplex
theorem GroupApproximation.CCKWTits.cckwCosetComplex_connected :
    KMSGroup.CCKW.cosetComplex.G.Connected
```

Both pass `#audit_closed_axioms` with `[propext, Classical.choice, Quot.sound]`. They come from the
general statements:

```lean
theorem simplyConnected_of_vertexPresentation (V : VertexPresentation R H) [DecidableEq S] :
    SimplyConnected (titsComplex (PresentedGroup R) H)
theorem connected_of_vertexPresentation (V : VertexPresentation R H) [DecidableEq S] :
    (titsComplex (PresentedGroup R) H).G.Connected
```

A `VertexPresentation R H` gives, for each `i`, a set `Stype i` of generators such that
`H i = (closure (of '' Stype i)).map (PresentedGroup.mk R)`. It also gives a type `τ s` with
`s ∈ Stype (τ s)` for every generator, and puts every relator in `closure (of '' Stype j)` for
some `j`.

## Census

`non_mf_groups_exist.tex` never mentions the coset complex, Tits' lemma or simple connectivity. T2
feeds kh-cckw's discharge of `hsc`/`hconn`, so this lane adds no census rows.

## Probe history

- 0912-004542-21107: CCKWTitsMoves and CCKWTitsTypedWords compiled. CCKWTitsPresentation was red with
  - an unused `DecidableEq S` on `memH` and `mk_eq_one_of_mem`;
  - the reverted hypothesis in `tw_of_red`;
  - "Unknown identifier `V`" in `typedWordProblem`, `generated` and both endpoints;
  - the `mk (x :: L)` split in `val_liftT`.

  All four were fixed in 5bef74495.
- 0912-093840-19657: CCKWTitsPresentation compiled. CCKWTitsGHB was red only on
  `Subgroup.map_closure`, which is `MonoidHom.map_closure` at the pin; fixed in 8836fadca.
- 0912-094055-42831: PROBE GREEN; CCKWTitsGHB BUILT.
