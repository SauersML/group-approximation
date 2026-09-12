# Stability of the corona trace-kernel: a third invisibility criterion (2026-09-12)

Lane `quasitrace-corona-kernel`, swarm 6. Task: decide whether the trace-kernel
ideal `K` of the corona `A` of Ozawa's `SL(3,Z)` block algebra `B` is invisible to
bounded 2-quasitraces, and thereby settle STW Problem I on this host, or record the
precise obstruction.

Notation is that of `research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md`:
`B = C*(⊕_k σ_k(SL(3,Z))) ⊂ ∏_k M_{n_k}`, `I = ⊕_k M_{n_k}`, `A = B/I`, the unique
tracial state `τ_0`, and `K = N_{τ_0} = ker(A → C*_r(SL(3,Z)))`, a nonzero ideal
with no bounded trace. "Quasitrace" means bounded 2-quasitrace; `QL(D)` means every
bounded 2-quasitrace on `D` is a trace.

## Outcome

Not settled. `QL(B)` and its negation are both still open, and STW Problem I is
untouched. What is new is a **third sufficient condition** for the invisibility of
`K`, cleaner than the two recorded in the corona artifact (`K` exact; `K_+` Cuntz
infinitesimal) because it reduces to an already-established general theorem:

> **If `K` is stable, then `QL(B)`.**

This turns the host question into a single standard question — *is the ideal `K`
stable?* — a Hjelmborg–Rørdam stability problem for one concrete ideal, rather than
an exactness or comparison problem about a non-exact algebra.

## 1. The criterion

**Proposition 1.1.** If `K` is a stable C*-algebra, then every bounded 2-quasitrace
on `A` vanishes on `K`; hence `QL(A)` and `QL(B)`.

*Proof.*
1. Let `σ` be a bounded 2-quasitrace on `A`. Its restriction `σ|_K` is a bounded
   2-quasitrace on the ideal `K`: the quasitrace axioms (monotonicity, additivity on
   commuting positives, the `M_2` extension condition) are inherited by any
   C*-subalgebra, and `M_2(K) ⊂ M_2(A)`; boundedness is inherited. No unitality of
   `K` is used.
2. `K` stable ⟹ `σ|_K = 0`, by the established
   `stw01-stable-algebras-are-bounded-quasitrace-invisible` (every bounded
   2-quasitrace on a stable C*-algebra is zero; no unitality/exactness/separability
   needed).
3. So every bounded 2-quasitrace on `A` vanishes on `K`. By the established
   equivalence `sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible`, this is
   exactly condition (2) there, which gives `QL(B)`. ∎

**Remark 1.2 (same conclusion via the extension principle).** The extension
`0 → K → A → C*_r(SL(3,Z)) → 0` has `A/K = C*_r(SL(3,Z))` exact (property A of
`SL(3,Z)`), hence quasitrace-linear by Haagerup. So if `K` is stable, the
established `stw01-stable-ideal-extensions-force-qt-linearity` gives `QL(A)`
directly, and Corollary 1.3 of the corona artifact gives `QL(B)`. Proposition 1.1
and this route agree; both need only that `K` be stable.

## 2. Where stability sits among the three conditions

The three now-recorded sufficient conditions for invisibility of `K` are
independent packagings of the same intuition ("`K` has no bounded quasitrace mass"):

- **`K` exact** (corona artifact Prop. 4.2): Haagerup on `C*(K,1)` plus trace
  extension. Blocked: no ambient exactness (expander uniform Roe algebra), and the
  extension by `I` need not be locally split.
- **`K_+` Cuntz infinitesimal in `W(A)`** (Prop. 4.1): `m·[(a−ε)_+] ≤ [1_A]` for all
  `m`. Blocked: the witnessing partial isometries live in `∏M`, not `A`.
- **`K` stable** (Proposition 1.1): reduces to
  `stw01-stable-algebras-are-bounded-quasitrace-invisible`.

Stability is genuinely different from the other two: it neither implies nor is
implied by exactness, and it is a structural property of `K` alone (no reference to
`W(A)` or to comparison witnesses that must lie in `A`).

## 3. Is `K` stable? Heuristic and the wall

By Hjelmborg–Rørdam, a `σ`-unital C*-algebra `D` is stable iff for every `a ∈ D_+`
and `ε > 0` there is `b ∈ D_+` with `‖ab‖ < ε` (approximate orthogonality) and
`a ≾ b` in `W(D)`.

**Heuristic for stability of `K`.** Elements of `K` are trace-thin: for `a ∈ K_+`,
`d_{τ_0}(a) = 0`, so in block `k` the compression `a_k` has rank `o(n_k)` on
average, while `n_k = p_k² + p_k → ∞`. There is therefore asymptotically unbounded
room in each block to place an orthogonal copy `b_k` of comparable rank. This is the
same growing-block room that makes the displacement estimate
`approximately-orthogonal-unitary-translates-kill-quasitraces` fire.

**The wall.** The halving witness `b` must lie in `K` (equivalently: be a genuine
element of `A` that maps to `0` in `C*_r(SL(3,Z))`), not merely in the ambient
corona `∏M/⊕M`. This is the identical membership obstruction that blocks the
infinitesimality route: orthogonal room exists in `∏M/⊕M`, but an element realizing
it inside `A` is exactly what is not produced. So stability of `K` is **not proved
here**; it is a reformulation that is cleaner (a named, standard property of one
ideal) but hits the same underlying wall.

**Whether stability could FAIL.** `K` is non-unital, consistent with stability. A
nonzero projection in `K` that is finite and full would obstruct stability; whether
`K` contains such a projection (e.g. a bounded-rank "second-eigenspace" ghost that
survives into `A`) is not determined here. The constant-function ghost projection is
absent, since `σ_k` acts on `ℓ²(X_k) ⊖ C1`.

## 4. Cairn integration

- New OPEN claim `sl3z-ozawa-corona-trace-kernel-is-stable`: `K` is a stable
  C*-algebra. Attempts record §3.
- New route `sl3z-ozawa-block-qt-via-stable-kernel` into the open
  `sl3z-ozawa-block-algebra-quasitraces-are-traces`, requiring the (open) stability
  claim together with the two established lemmas of Proposition 1.1. Because the
  stability requirement is open, the route does not fire; `QL(B)` and STW Problem I
  stay OPEN.

## 5. Source status and novelty

- `stw01-stable-algebras-are-bounded-quasitrace-invisible` and
  `stw01-stable-ideal-extensions-force-qt-linearity` are established on main and were
  used as stated; not re-derived here.
- The stability criterion (a stable ideal is quasitrace-invisible, and the Hjelmborg–
  Rørdam characterization) is standard (Rørdam; Hjelmborg–Rørdam 1998). No novelty is
  claimed. The only new content is the application to this host and the identification
  of "is `K` stable?" as the cleanest open sub-question, with the growing-block
  heuristic and the membership wall of §3.
