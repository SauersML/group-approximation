# Lane go-sr1: report

Non-MF verbatim formalization swarm, 2026-09-12.

## Scope

This lane builds the minimal-disc layer for the Kotowski–Ollivier route (hyperbolicity of
`GHB(7)`). It feeds kh-hyperbolic's `ChainFillingBound X.G.Adj X.Tri 6`.

| item | content | module |
|---|---|---|
| HC2 | the one-edge disc | `GGT/SystolicDiscFilling` |
| HC3 (a)–(d) | the four boundary moves, stated as Props | `GGT/SystolicDisc` |
| HC4 | filling from simple connectivity | `GGT/SystolicDiscFilling` |
| HC6 | the mirror fold, stated as a Prop | `GGT/SystolicDisc` |
| HC10 | a least disc has large typed links | `GGT/SystolicDisc`, closed form in `GGT/SystolicDiscFilling` |
| HC11 | typed count, `F + 12 ≤ 6B` | `GGT/SystolicDiscCounts` |
| HC12 | boundary sums | `GGT/SystolicDiscCounts` |

The producers live in other lanes:
- HC3(a)–(c): kh-torsion. `attachTriangleStatement` and `insertChordStatement` are in `GGT/SystolicDiscMovesChord`; `attachPendantStatement` is in `GGT/SystolicDiscMovesAdapter`.
- HC3(d) `ZipSpurStatement`: kh-ejz.
- HC6 `MirrorFoldStatement`: fff-periodic.

If any Prop spelling below changes, tell kh-torsion, kh-ejz, fff-periodic and kh-hyperbolic first.

## Statements

```lean
namespace GroupApproximation.Systolic
universe u
variable {V : Type u} {X : TriangleComplex V} {γ : List V}

-- GGT/SystolicDisc.lean (compiled, green)
structure TriangulatedDisc (X : TriangleComplex V) (γ : List V)
  -- fields: map : CombMap.{0}, planar, outer, vtx, adj, tri, base, base_outer, boundary
def AttachTriangleStatement (X) : Prop := ∀ (p q : List V) (u v w : V), X.Tri u v w →
  TriangulatedDisc X (p ++ u :: w :: q) → Nonempty (TriangulatedDisc X (p ++ u :: v :: w :: q))
def InsertChordStatement (X) : Prop := ∀ (p q : List V) (u v w : V), X.Tri u v w →
  TriangulatedDisc X (p ++ u :: v :: w :: q) → Nonempty (TriangulatedDisc X (p ++ u :: w :: q))
def AttachPendantStatement (X) : Prop := ∀ (p q : List V) (u v : V), X.G.Adj u v →
  TriangulatedDisc X (p ++ u :: q) → Nonempty (TriangulatedDisc X (p ++ u :: v :: u :: q))
def ZipSpurStatement (X) : Prop := ∀ (p q : List V) (u v : V),
  TriangulatedDisc X (p ++ u :: v :: u :: q) →
    Nonempty (TriangulatedDisc X (p ++ u :: q)) ∨ p ++ u :: q = [u]
def FillingStatement (X) : Prop := ∀ (v : V) (l : List V), List.IsChain X.G.Adj (v :: l ++ [v]) →
  l ≠ [] → Nonempty (TriangulatedDisc X (v :: l ++ [v]))
def MirrorFoldStatement (X) : Prop := ∀ (γ : List V) (D : TriangulatedDisc X γ) (d : D.map.Dart),
  D.map.faceOf d ≠ D.outer → D.map.faceOf (D.map.alpha d) ≠ D.outer →
  D.vtx (D.third d) = D.vtx (D.third (D.map.alpha d)) →
    ∃ D' : TriangulatedDisc X γ, D'.innerFaceCount + 2 ≤ D.innerFaceCount
theorem exists_leastDisc_typedLinks (hfill : FillingStatement X) (hfold : MirrorFoldStatement X)
    {n : V → ℕ} (hL : LinksLargeAt X n) {v : V} {l : List V}
    (hl : List.IsChain X.G.Adj (v :: l ++ [v])) (hne : l ≠ []) :
    ∃ D : TriangulatedDisc X (v :: l ++ [v]),
      (∀ D' : TriangulatedDisc X (v :: l ++ [v]), D.innerFaceCount ≤ D'.innerFaceCount) ∧
      ∀ w : D.map.Vertex, D.Interior w → n (D.vtx w) ≤ D.map.vertexDegree w

-- GGT/SystolicDiscFilling.lean
def TriangulatedDisc.oneEdge {u v : V} (h : X.G.Adj u v) : TriangulatedDisc X [u, v, u]
theorem fillingStatement_of_simplyConnected (hsc : SimplyConnected X)
    (ha : AttachTriangleStatement X) (hb : InsertChordStatement X)
    (hc : AttachPendantStatement X) (hd : ZipSpurStatement X) : FillingStatement X
theorem exists_leastDisc_typedLinks_of_simplyConnected (hsc : SimplyConnected X)
    (ha : AttachTriangleStatement X) (hb : InsertChordStatement X)
    (hc : AttachPendantStatement X) (hd : ZipSpurStatement X)
    (hfold : MirrorFoldStatement X) {n : V → ℕ} (hL : LinksLargeAt X n) {v : V} {l : List V}
    (hl : List.IsChain X.G.Adj (v :: l ++ [v])) (hne : l ≠ []) :
    ∃ D : TriangulatedDisc X (v :: l ++ [v]),
      (∀ D' : TriangulatedDisc X (v :: l ++ [v]), D.innerFaceCount ≤ D'.innerFaceCount) ∧
      ∀ w : D.map.Vertex, D.Interior w → n (D.vtx w) ≤ D.map.vertexDegree w

-- GGT/SystolicDiscCounts.lean   (D : TriangulatedDisc X γ)
theorem TriangulatedDisc.exists_typedCounts (τ : V → Fin 3)
    (hτ : ∀ {x y z}, X.Tri x y z → τ x ≠ τ y ∧ τ y ≠ τ z ∧ τ x ≠ τ z)
    (hdeg : ∀ w, D.Interior w → typedGirth τ (D.vtx w) ≤ D.map.vertexDegree w) :
    ∃ C : TypedTriangularDiscCounts,
      C.faceCount = D.innerFaceCount ∧ C.boundaryLength = D.map.faceDegree D.outer
theorem TriangulatedDisc.abs_boundarySum_le (I : V → V → ℤ) (hanti : ∀ x y, I y x = -I x y)
    {C₀ : ℕ} (htri : ∀ {x y z}, X.Tri x y z → |I x y + I y z + I z x| ≤ C₀) :
    |(List.zipWith I γ γ.tail).sum| ≤ C₀ * D.innerFaceCount
```

## Commits and status

| module | last commit | status |
|---|---|---|
| `GGT/SystolicDisc` | 2cf6d1248 | compiled in probe 0912-092123-9062 |
| `GGT/SystolicDiscFilling` | 4c12845a1 (first landed cf71506a5) | GREEN, probe 0912-103604-11425 |
| `GGT/SystolicDiscCounts` | 4c12845a1 (first landed b139e9695) | GREEN, probe 0912-103604-11425 |

Probe 0912-103604-11425 (base 3221a02ea) built both modules with exit 0 and also compiled `SystolicDisc`. The probed files match origin/main: `SystolicDisc` a79432f8, `SystolicDiscFilling` f5f0eb23, `SystolicDiscCounts` 3330bc17.

Probe 0912-092123-9062 was red on `SystolicDiscFilling`. 4c12845a1 fixes those errors and the ones in `SystolicDiscCounts`.
- **Filling.** `rintro (hlen | ⟨D⟩)` bound `D` to the `Nonempty` proof; it now reads `⟨⟨D⟩⟩`. It also drops an unused simp argument.
- **Counts.** Four fixes:
  - use `List.sum_toFinset` and `Fin.sum_ofFn`;
  - pass explicit arguments to `getElem_toList`;
  - rewrite the boundary under `conv_lhs`, because `D` depends on `γ`;
  - close the triangle through `facePerm (facePerm² d) = d`.

Consumers: kh-hyperbolic's `Kazhdan/GHBHyperbolicDiscCounts` imports both modules. systolic-counts will re-probe it once both are green.
