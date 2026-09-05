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
