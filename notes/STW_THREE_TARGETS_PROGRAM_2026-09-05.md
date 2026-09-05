# Three-target unconditional formalization program (2026-09-05)

USER ORDER: formalize all three in Lean **fully unconditionally, no literature
inputs**.

| # | Problem | STW no. | State on entry |
|---|---|---|---|
| 1 | Is every amenable trace quasidiagonal? **No.** | X(1) | refuted + formalized (`ProblemX.lean`); needs verification/hardening |
| 2 | Trace Problem for factorial tracially complete C*-algebras. **No.** | XXII | assembled; conditional on ONE named Prop `CommonZeroProperty` |
| 3 | Are all unital simple C*-algebras K1-injective? **No.** | LIX | complete proof in `research/artifacts/stw59-*`; ZERO Lean |

## Standing discipline (every lane)

1. **Never run Lean locally.** The only build is
   `scripts/remote-build.sh <Lean.Module.Name>` (syncs the shared tree, holds
   the fleet mutex, builds on acn112 against the 24 GB warm `.lake`). Batch
   your probes; author a lot between them. Never `lake` on this Mac.
2. **Mathlib names are checkable.** Pinned rev `81a5d257`
   (toolchain v4.32.0). Exact:
   `git -C /Users/user/mathlib4 show 81a5d257:Mathlib/<path>`;
   search at the pin: `git -C /Users/user/mathlib4 grep -n <pat> 81a5d257 -- Mathlib`.
   `rg` reads the NEWER checkout — wrong revision. `to_additive` names and
   structure fields have no `theorem` line. Deprecated aliases are build
   ERRORS here (`-DwarningAsError=true`).
3. **No `sorry`, no `admit`, no `axiom`, no `opaque`.** A residue you cannot
   prove becomes a **named `Prop`** with a docstring saying exactly what would
   discharge it — never a hypothesis smuggled into an endpoint statement.
   Endpoint statements must not mention such a Prop.
4. **Lanes never edit `GroupApproximation.lean`.** Author orphan modules; the
   lead wires root imports.
5. **Commit and push as you go** (small commits, main branch). Never
   `git reset`/`amend`/`stash`/`revert`/worktrees/branches. Recover forward.
6. Force-probe after landing: a stale remote olean can replay and report a
   false green. If the job count does not move on a real change, the probe
   did NOT rebuild.
7. Do not oversubscribe acn112/acn116; never write build output to `/tmp`
   (RAM-backed tmpfs shared with other users).

## Target 2 critical path (XXII)

`GroupApproximation/Topology/TautologicalCommonZero.lean` defines

    CommonZeroProperty : Prop

`TautologicalAntipodal.commonZeroProperty_of_antipodalObstruction` already
reduces it to

    AntipodalObstruction : Prop   -- no continuous nowhere-zero ODD map
                                  -- (C^{N+1} \ 0) -> (κ -> C) when card κ ≤ N

and `ThirdParty/HamSandwich/SphereOddDegree/BorsukUlam.lean` already proves

    no_odd_map_sphere_succ : C(Sphere (n+1), Sphere n) odd -> False

So the whole gap is: **finish the v4.32 port of the HamSandwich closure, then
transport `AntipodalObstruction` onto it** (complex realification + normalize
to the unit sphere + equatorial drop from S^{2N+1} to S^{2k}).

## Target 3 architecture (LIX)

Source proof: `research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`.
The Lean re-cut avoids all bundle/Chern libraries by using **concrete
projections over concrete compact spaces**:

* `CP^d := {q : Matrix (Fin (d+1)) (Fin (d+1)) ℂ // q = qᴴ ∧ q*q = q ∧ trace q = 1}`
  with the subspace topology — no quotient topology, and the tautological line
  is the *identity* projection-valued map.
* `S^n := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`.
* `Γ(X, End E) := p • Matrix (Fin N) (Fin N) C(X,ℂ) • p` for an explicit
  projection `p`; bundle isomorphism := **Murray–von Neumann equivalence of
  projections** in the matrix algebra. Pure C*-algebra, no bundle theory.
* `F` over `S^5 ⊂ ℂ³` is the explicit projection `x ↦ 1 - x xᴴ`.

Everything above is elementary. The one genuinely topological ingredient is
the **parity obstruction** (manuscript Lemmas 2–3).

## Mandate amendment (user, 2026-09-05, mid-wave)

> "we need literally all of it" / "if u need to do megaproject foundations
> then get opus on it"

**No named-`Prop` residue is an acceptable stopping point.** Rule 3 above still
governs *intermediate* work — an unproved step is a named Prop, never a
`sorry` — but a target is not finished until every such Prop is a theorem.
Where Mathlib lacks the foundation, the foundation gets built.

Seven Opus foundation lanes were added for the target-3 obstruction, which is
the only place a residue was going to survive:

| lane | owns | namespace |
|---|---|---|
| `found-bundle-calculus` | complex vector bundles AS continuous projection-valued maps (Serre–Swan as the definition): pullback, ⊕, ⊗, rank, **homotopy invariance**, complements, clutching, nowhere-zero sections | `AlgTop/BundleCalculus*` |
| `found-cohomology-ring` | integral singular cohomology, cup product, spheres, free-case Künneth | `AlgTop/{SingularCohomology,CupProduct,Spheres,Kunneth}` |
| `found-cpn-cohomology` | even-cell filtration of `CP^n`; `H^*(CP^n;ℤ)=ℤ[h]/(h^{n+1})`; products; torsion-freeness of `H^*(S^1×S^5×Y)` | `AlgTop/ComplexProjective*` |
| `found-chern-classes` | total and virtual Chern classes, Whitney sum, `c_1(L_j)=h_j`, vanishing above rank and above dimension, splitting principle | `AlgTop/Chern*` |
| `found-ktheory-bott` | `K^0`/`K^1`, split restriction sequence, free-case Künneth, `K^*(∏CP^d)`, Chern character with the integral normalization on `S^1`,`S^5` | `KTheory/*` |
| `found-euler-class` | Euler class, Euler = top Chern, local index at a transverse zero, the mapping-torus bundle `W_g`, Lemma 2's ±1 count | `AlgTop/Euler*` |
| `found-mapping-torus-parity` | Lemma 3, incl. the pure-algebra core `c_q(δ)=(-1)^{q-1}(q-1)!·ch_q(δ)` and the evenness of `(|b|+2)!/∏b_j!` | `AlgTop/MappingTorusParity` |

Two scope restorations follow: `K_1(A)=0` and "order exactly two" are back in
scope for target 3 (they are part of the printed Theorem 1), and the
`u ⊕ 1` null-homotopy is proved elementarily — define `u` as the seam
discrepancy `s₊(x)⁻¹s₋(x)` of hemisphere sections of `U(3) → S^5`, `a ↦ a e₃`;
it lands in `U(2)` because it fixes `e₃`, and it contracts in `U(3)` because
`s₋` extends over its disc. No Bott, no homotopy groups.

**Four collision risks** across lanes, all owned by `lix-design` to arbitrate:
the projection model of a bundle, the `CP^n` model, the clutching
construction, and the sphere models. One of each, campaign-wide.

## Standing rule added mid-wave: nobody deletes a peer-facing module

**A lane must never delete a module on the grounds that a peer has a better
one.** Report the duplicate to the lead, who checks the other copy actually
exists, and decides which survives.

This fired three times in one hour on 2026-09-05, and twice it produced a hole
rather than a redundancy:

* `lix-obstruction` deleted three modules (`LIXObstructionTautSection`,
  `TautChart`, `Segment`) because `found-euler-class` had built them better —
  at the same moment the lead had told `found-euler-class` that
  `lix-obstruction` owned that chain and not to build into it.
  `found-euler-class` then proposed retiring their own copies. Had they done
  it, the campaign would have had **no** proof that the section over `CP^d`
  has exactly one zero, and nothing would have flagged it, because each
  deletion is locally correct. Caught only because that lane refused to delete
  a file on a ruling without checking.
* `found-chern-classes` deleted `ChernParityCoefficient` and
  `ChernNewtonSquareZero` as duplicates of `ChernParityAlgebra`, while the
  parity lane deleted `ChernParityAlgebra` and rewrote `MappingTorusParity` to
  import the two just-deleted files. Dangling import; both restored.
  That lane *did* grep for importers first — ten minutes before the import was
  added.

The general hazard: on a shared tree, "this duplicates a peer's file, delete
mine" and "this duplicates a peer's file, delete mine" run concurrently and
both files vanish. A grep for importers is not sufficient, because it races.
Deletion is the one operation where mutual deference subtracts instead of
duplicating, and neither deleter can see it happening.

## Standing rule: a green claim carries its job count

**"It builds" is not a result. `Build completed successfully (N jobs)` with a
moved count, or a `Built <module> (Ns)` line with a real time, is the result.**

The count is the *only* thing distinguishing a genuine rebuild from a replayed
`.olean`. Without it a downstream reader has to re-run the build to learn what
the builder already knew, and on a fleet this size that is the difference
between one acquisition of a 20-deep mutex and two.

This applies symmetrically, and both halves have now cost the campaign a day's
confusion:

* **Greens.** A module reported green with no count may have been replayed.
  `remote-build.sh` `touch`es every synced file so lake re-hashes, but a target
  that was never named and was only reached incidentally proves nothing about
  the bytes you have on disk. Name your targets explicitly.
* **Reds.** A probe result carries the timestamp of its *source sync* and stops
  being evidence the moment any commit touches its closure. Two stale reds
  propagated today: one from a sweep-committed mid-write file that a lane then
  reported as a peer's broken module, and one from a probe whose sync predated
  the fix by five minutes. Date every error list you send.

Corollary for anyone reading a lane report: `--run` (i.e. `lake env lean`)
produces **no** job count at all, so a driver result is a genuine machine
result but cannot certify that its inputs were re-elaborated rather than read
from cache.
