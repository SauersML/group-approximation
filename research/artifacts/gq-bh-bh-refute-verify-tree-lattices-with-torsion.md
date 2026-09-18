# Adversarial check: `cocompact-tree-product-lattices-lie-in-type-a-class` (bh-refute, 2026-09-18)

Rotation item (a) (d9d0fb5d0). Focus, as requested: steps T3 and T6 of
`tree-lattice-with-torsion-via-zappa-szep-kgraphs`, i.e. how Li's Zappa–Szép Example (III) is applied.
Source: Li, arXiv:2110.04505v2, TeX read locally (`gq/src/kep/li-garside-II-2110.04505v2.tex`).

Verdict: **PASS**, with one wording nit (N1). The rest of the chain is not independently reviewed on main:
the torsion-free power-phase route and `stabilized-kgraph-full-group-clopen-action-proof`. I checked it only
to the extent T5–T6 lean on it.

## What Li's Example `ex:ZS` (III) needs (TeX l.2371–2380), and where each is met

| hypothesis in Li | met by |
|---|---|
| §Gars-deg setting: cancellative small category `C`, degree map to `P = Z_{>=0}^k`, finite `C^0`, `v·d^{-1}(p)` finite (the assumptions of Thm `thm:deg`) | `C_N × O_2` is a finite `(k+1)`-graph (T1, T4, T6) |
| self-similar action `G ↷ C` with `d(g.a) = d(a)` | T2: `g·λ = ĝλ` preserves grid shape; on `O_2` the action is trivial, which is a valid self-similar action on the product |
| (then automatic, per the Example) `D = C ⋈ G` right cancellative up to `=*`, `G.S ⊆ S C^*`, and (Inv) | stated in the Example itself (l.2372) |
| `#v d^{-1}(ε_j) v >= 2` for all `v`, `j` | T4 (colours `1..k`) and the two `O_2` loops (colour `k+1`) |
| `X ⊆ Ω_∞` closed invariant | `X = ∂Ω`, as in the torsion-free route's use of `thm:k-graphs` (l.2124), which has the same hypothesis |
| **condition (F) for `D`** | T3; see below |
| `D^*(w,w)` of type `F_n` | Remark `rem:ZS-Stab` (l.2358): since a k-graph has `C^* = C^0`, `D^*(v,v) = St(G,v) = G(v,v)`, a finite group |

## T3: condition (F), checked against Li's definitions

- **Definition (l.1454).** For `a, b ∈ D^*(v,v)` and `U = X(v;e) ∈ 𝔛̃`, `[a,U] = [b,U]` implies `a = b`.
  By l.2296, `𝔛̃ = {Ũ : U ∈ 𝔛}`, where `𝔛` is built for `C`.
- **Which `U` occur.** Li's corollary after Thm `thm:deg` (l.2082–2085): "For `X = ∂Ω`, we always have
  `∂Ω(v; e) = ∅` unless `e = ∅` … we have `𝔛 = {(∂Ω(v_i))_i}`". So the only `U` are the vertex boundaries,
  exactly as T3 says.
- **The implication.** `[g,U] = [h,U]` means that at every `χ ∈ ∂Ω(v)` the germs agree, i.e. `g` and `h` agree
  as partial bijections on some ideal `λD` with `χ ∈` its cylinder. So `g.λ = h.λ` and `g|_λ = h|_λ`, which
  means they agree as homeomorphisms on the sub-box of `λ`. Compactness gives agreement on all of `B_(c_v)`.
  `G(v,v)` is *defined* as the image in `Homeo(B_(c_v))` (T2), so `g = h`.
- **Well-definedness in T2.** An element of `Stab(c_v)` acting trivially on the box fixes every grid from
  `c_v`. In a leafless tree every vertex of a half-tree lies on a ray to an end of its shadow, and this
  holds factorwise. So sections are trivial too, and the germ maps do not depend on the lift.
- **Effectiveness,** needed for T6's "faithful" step: the same argument shows that a germ acting trivially
  near `χ` is a unit.

## T6: the conclusion drawn

The Example's "in particular" gives `F((I_l(D) ⋉ X̃)_Ỹ^Ỹ)` of type `F_∞`, for `Y` a union of vertex boundaries.
Taking all vertices gives the full group `D''` on `Z × {0,1}^N`.

Steps 2–4 of `stabilized-kgraph-full-group-clopen-action-proof` (pieces, type-vector comparison, the type (A)
action on clopen sets) use only:
- cylinders;
- prefix-replacement bisections;
- direct-factor splitting of stabilizers.

The units of `G` fix cylinders and vertices. So these steps transfer, **provided** the full group acts by
homeomorphisms, which is the effectiveness of T3. `Γ_0 ≤ D''` via `g ↦ g × id` (T5), and finite-index
overgroups stay in `B_A`.

## Nit

- **N1 (T4).** "A common multiple `N` of the periods gives at least two loops of every colour at every vertex"
  should read "a sufficiently large common multiple". Irreducibility with spectral radius `> 1` gives
  `>= 2` closed walks of length `n` only for large `n` in the period class. This is harmless.

## Attacks tried (all failed)

- **(F) on smaller sets `X(v;e)`, where two elements of a finite stabilizer could agree on a sub-box.** This
  would have been a real gap. It is excluded by Li's corollary that `∂Ω(v;e) = ∅` for `e ≠ ∅`.
- **Non-effective groupoid making the full group act non-faithfully.** Excluded by faithfulness on boxes.
- **Whether `X̃` is `I_l(D)`-invariant (Li warns this can fail for images of invariant sets).** Here
  `X = Ω_{C,∞}` is everything, and its image is `Ω_{D,∞}`, which is invariant.
