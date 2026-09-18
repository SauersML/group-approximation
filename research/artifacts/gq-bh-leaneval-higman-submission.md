# lean-eval `higman_infinite_simple`: what a submission needs

Lane `bh-pal-leaneval`, 2026-09-18. Nothing has been submitted or posted anywhere. The user submits.

## The problem, as lean-eval states it

Source: `leanprover/lean-eval`, `generated/higman_infinite_simple/` (read 2026-09-18).

```lean
theorem higman_infinite_simple :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧ IsSimpleGroup (PresentedGroup rels) ∧
        Infinite (PresentedGroup rels)
```

- Workspace pin: `lean-toolchain` = `leanprover/lean4:v4.34.0`, Mathlib rev `5ed2965256430c3649e86755f9576b54eca72435`.
  The leaderboard page and the manifest notes still say "Mathlib v4.32.2". That is out of date, because the
  workspace moved on. The repo is on v4.32.0.
- `config.json`: permitted axioms `propext`, `Quot.sound`, `Classical.choice`. `lake test` runs comparator, and the
  harness forces the nanoda kernel on for every problem.
- Only `Submission.lean` and `Submission/**/*.lean` are overlaid on a pristine copy of the workspace. The lakefile
  cannot be changed, so the proof may import Mathlib and Lean only.

## Blocker: the problem is archived

`manifests/problems/higman_infinite_simple.toml` has `status = "archived"`, effective 2026-08-20, reason `policy`. This
comes from lean-eval PR #568 ("Align catalog lifecycle with v1 publication"). That PR archived all 179 pre-freeze
formalization problems that are not in the v1 set, and `boone_higman_embedding` and `boone_higman_simple` are among
them. The submission service accepts only formalization problems that are **visible and active**, so this problem
cannot be submitted now. lean-eval's lifecycle has a `restoration` reason category. Asking the maintainers to
restore the problem is an external request, so it is the user's decision.

## The proof in this repository

- `GroupApproximation.HydeLodha.higman_infinite_simple`, in
  `GroupApproximation/GroupTheory/HydeLodha/HigmanInfiniteSimple.lean`, landed at `b6bd1be9b` and imported from the root.
  Its statement is lean-eval's, term for term.
- Proof: `finitelyPresentedInfiniteSimple_closed` (Hyde–Lodha `Q₂ = [Γ₂, Γ₂]`), then
  `Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup`. Simplicity transfers by `MulEquiv.isSimpleGroup`
  and infinitude by `Infinite.of_injective`.
- Trusted MSI build (`scripts/remote-build.sh`, fleet mutex): 4490/4490 jobs, no warnings.
  `#audit_closed_axioms` reports `[propext, Classical.choice, Quot.sound]`.
- The combined BH Palomar config states the same theorem as `BooneHigman.exists_finitely_presented_infinite_simple`
  (lane `bh-pal-surface`).

## What a submission would still take: a self-contained port

A lean-eval workspace cannot import this repository, so the proof has to be copied into `Submission/`.
Measured on MSI by walking the kernel constant closure of `higman_infinite_simple`:

| | |
|---|---|
| constants in the closure (including Mathlib and core) | 14,758 |
| repository constants | 1,216 |
| repository modules containing them | 67 (41 `HydeLodha`, 17 `HigmanThompson`, 8 other `GroupTheory`, 1 `Manuscript.NonMF`) |
| lines in those declarations | about 10,250 |
| lines in those 67 files, whole | about 14,800 |

From the `Manuscript.NonMF` module only the definition `FinitelyPresentedInfiniteSimpleStatement` is needed. The
rest of that file can be dropped. The port has to compile on Lean v4.34.0 with Mathlib `5ed29652`, two releases
newer than the repo pin, so expect Mathlib renames and deprecations to need fixing.

## Steps once the problem is active again

1. Fork `leanprover/lean-eval`, or copy `generated/higman_infinite_simple/` into your own repository.
2. Put the ported modules under `generated/higman_infinite_simple/Submission/`, renamed to `Submission.*`
   module paths, and use this `Submission.lean`:

   ```lean
   import Mathlib
   import Lake.Toml
   import Lake.Util.Message
   import Lean
   import Submission.Helpers
   import Submission.HigmanInfiniteSimple

   namespace Submission

   theorem higman_infinite_simple :
       ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
         rels.Finite ∧ IsSimpleGroup (PresentedGroup rels) ∧
           Infinite (PresentedGroup rels) :=
     GroupApproximation.HydeLodha.higman_infinite_simple

   end Submission
   ```

3. Check that `lake build Solution` is green, then run `lake test`. That needs `comparator`, `landrun`,
   `lean4export` and `nanoda` on `PATH`, as described in the lean-eval README.
4. Commit the files and record the 40-character commit sha.
5. Install the GitHub Apps "Lean Eval Source Reader" and "lean-eval-bot" on the repository.
6. Submit through the service at `lean-eval-submission-server.lean-eval.workers.dev`: sign in with GitHub, give the
   problem id `higman_infinite_simple`, the commit and the model or system that produced the proof, and accept the
   release terms. Accepted source is published under Apache 2.0 two calendar months after acceptance, unless the
   repository is private and you choose to withhold it.
