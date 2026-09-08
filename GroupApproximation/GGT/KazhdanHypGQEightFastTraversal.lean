import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.GGT.KazhdanHypGQEightTableFormat

/-!
# A traversal the kernel can afford, and the bridge back to `allFinN`

Lane `lix-hres`.

`KazhdanHypGQEightTableFormat` evaluates its Boolean clauses with

```text
allFinN (n + 1) p = p 0 && allFinN n (fun i => p i.succ)
```

which accumulates one `Fin.succ` wrapper per level, so applying the predicate at
depth `k` costs `O(k)` and a single traversal costs `O(n²)` applications.  The
verifier nests two of them, so the inner traversal pays the outer's wrapper
depth as well.

That is not a theoretical worry.  Measured on the node, at `n = 585`, one loop,
the same argument-forcing predicate for both:

```text
allFinN    585 (forcing 585) = true   ->  32.4 s
allFinFast 585 (forcing 585) = true   ->   0.22 s
```

a factor of about `144` on a single loop, before nesting.  For comparison,
`localCheck` on a 585-point table did not finish in **one hour** with
`maxHeartbeats 0`.

The predicate has to force its index or the measurement is vacuous: with
`fun _ => true` the application `(fun i => p i.succ) j` beta-reduces without
ever walking the wrapper chain, and the comparison then measures recursion
depth rather than the thing at issue.

## What this file does and does not do

It supplies a traversal with no accumulated wrappers, proves it satisfies the
same specification as `allFinN`, and proves the two are **equal**.  The
equality is the point: every soundness theorem in
`KazhdanHypGQEightTableSoundness` is stated about the original clauses, so
rewriting a clause into its fast form changes how the Boolean is computed and
not what it asserts, and nothing downstream needs restating or reproving.

It does **not** make the verifier tractable on its own.  `pairCoverCheck`
rescans all `m` rows for each of the `n²` ordered pairs, which at the W(8)
parameters `n = 585`, `m = 1755` is about `6 · 10⁸` elementary steps however
fast the traversal is; that is an algorithmic question and is left open here.
`lambdaCheck`, which decides bijectivity of a `Fin 585 → Fin 585` map, is also
untouched.  So this file buys a large constant factor on every clause and
removes no asymptotic obstacle.

## Main declarations

* `allFinFast` — the traversal, over `List.finRange`.
* `allFinFast_eq_true_iff` — its specification, matching `allFinN_eq_true_iff`.
* `allFinN_eq_allFinFast` — **the bridge**: the two are equal.
* `pairCoverCheckFast`, `rowCompatibilityCheckFast`, `noCubeCheckFast`,
  `positiveCheckFast`, and the four theorems identifying each with the
  original clause.
-/

namespace GroupApproximation
namespace KazhdanHyp
namespace GQEightTableFormat

/-! ## The traversal -/

/-- Universal quantification over `Fin n` as a Boolean, traversing an explicit
list so that no `Fin.succ` wrappers accumulate. -/
def allFinFast (n : ℕ) (p : Fin n → Bool) : Bool :=
  (List.finRange n).all p

theorem allFinFast_eq_true_iff (n : ℕ) (p : Fin n → Bool) :
    allFinFast n p = true ↔ ∀ a, p a = true := by
  constructor
  · intro h a
    exact List.all_eq_true.mp h a (List.mem_finRange a)
  · intro h
    exact List.all_eq_true.mpr fun a _ => h a

/-- **The bridge.**  The two traversals are equal, so a clause may be evaluated
in the fast form and consumed by a soundness theorem stated in the slow one. -/
theorem allFinN_eq_allFinFast (n : ℕ) (p : Fin n → Bool) :
    allFinN n p = allFinFast n p := by
  rw [Bool.eq_iff_iff, allFinN_eq_true_iff, allFinFast_eq_true_iff]

/-! ## The clauses that use it

Each fast clause is the original with `allFinN` replaced, and each theorem
below says the two Booleans are equal.  Nothing about what is checked
changes. -/

/-- `pairCoverCheck` with the fast traversal.  Both loops, since the inner one
pays the outer's wrapper depth. -/
def pairCoverCheckFast {n m : ℕ} (T : Table n m) : Bool :=
  allFinFast n (fun x => allFinFast n (fun y => decide
    (pairCoverCount T x y = if member T x y = true then 1 else 0)))

theorem pairCoverCheckFast_eq {n m : ℕ} (T : Table n m) :
    pairCoverCheckFast T = pairCoverCheck T := by
  unfold pairCoverCheckFast pairCoverCheck
  simp only [allFinN_eq_allFinFast]

def rowCompatibilityCheckFast {n m : ℕ} (T : Table n m) : Bool :=
  allFinFast m (fun j => rowCompatible T (T.rows j))

theorem rowCompatibilityCheckFast_eq {n m : ℕ} (T : Table n m) :
    rowCompatibilityCheckFast T = rowCompatibilityCheck T := by
  unfold rowCompatibilityCheckFast rowCompatibilityCheck
  simp only [allFinN_eq_allFinFast]

def noCubeCheckFast {n m : ℕ} (T : Table n m) : Bool :=
  allFinFast m (fun j => decide
    (¬ ((T.rows j).x = (T.rows j).y ∧
      (T.rows j).y = (T.rows j).z)))

theorem noCubeCheckFast_eq {n m : ℕ} (T : Table n m) :
    noCubeCheckFast T = noCubeCheck T := by
  unfold noCubeCheckFast noCubeCheck
  simp only [allFinN_eq_allFinFast]

def positiveCheckFast {n m : ℕ} (T : Table n m) : Bool :=
  allFinFast m (fun j => allFinFast 3 (fun k =>
    decide ((triangles T j k).2 = true)))

theorem positiveCheckFast_eq {n m : ℕ} (T : Table n m) :
    positiveCheckFast T = positiveCheck T := by
  unfold positiveCheckFast positiveCheck
  simp only [allFinN_eq_allFinFast]

/-! Audited on every build: `#audit_axioms` prints the axiom closure and
**fails the build** if it leaves the classical allowlist, which `#print axioms`
does not. -/

#audit_axioms allFinN_eq_allFinFast

#audit_axioms pairCoverCheckFast_eq

end GQEightTableFormat
end KazhdanHyp
end GroupApproximation
