---
rg: 2
id: fw-window-zero-shells-are-self-similar-actions
kind: claim
title: Window-zero shell actions are exactly self-similar actions of finite defect, and for FW inputs the window-zero and commuting-window shell routes exist only through them
distinct_from:
  fw-shell-inputs-at-window-zero-are-highly-transitive: that derives high transitivity and trivial centre from descending window zero at s; this identifies descending window zero at every shift power with an intrinsic object, the self-similar action of finite defect, and states the whole window-zero and commuting-window verdict for FW inputs through it.
  fw-inputs-pass-window-zero-only-via-proper-self-embeddings: that records index constraints and the self-similar shape as the surviving case; this proves the equivalence in both directions, for every shift power.
  fw-inputs-fail-commuting-shell-windows: that closes ascending commuting windows; this places commuting windows in both directions under the same criterion.
  genuine-action-shell-envelopes-generalize-the-regular-shell: that sets up genuine-action shells; this characterizes their window-zero case.
---

**ESTABLISHED** by `fw-window-zero-shells-are-self-similar-actions-proof`. It is a lane proof,
elementary, not independently reviewed. It assembles the other FW window nodes, which are cited
with their own review status, and claims no novelty for the ingredients.

## Definition

A **self-similar action of defect `m >= 1`** of a group `P` consists of:
- a `P`-set `(X, ρ)` on which every `ρ_g`, `g ≠ 1`, has infinite support;
- an injective endomorphism `ψ` of `P`;
- a subset `Y ⊆ X` with `|Y| = m`;
- a bijection `σ : X -> X − Y` with `σ ∘ ρ_g = ρ_(ψ(g)) ∘ σ` for all `g`, such that the
  rays `{σ^k(y) : k >= 0}`, `y ∈ Y`, cover `X` up to a finite set.

Then `Y` is `ψ(P)`-invariant. `X` looks like `m` copies of `N` on which `σ` is the shift, and
`P` acting through `ψ` on "`X` minus `Y`" is `P` acting on `X`. This is the permutation-group
form of `V ≅ V[cone]`, and of the corner self-embeddings of Leavitt-type groups.

## Statement

Let `s : n ↦ n+1`, and read shell relations in `NearSym(N)`.

1. **Every self-similar action is a descending window-zero shell action (any `P`).** A
   self-similar action of defect `m` becomes, under a suitable enumeration `X ≅ N`, a genuine
   action on `N` with infinite supports satisfying

       s^m ρ_g s^-m = ρ_(ψ(g))   for all g ∈ P.

   For `m = 1` this is window zero in the direction `ε = -1`. Then `R_ρ ≅ P *_ψ`, and if `P` is
   finitely presented the shell germ group `Q_ρ` is finitely presented
   (`fp-window-group-makes-shell-germ-group-fp`, with window group `ρ(P) ≅ P`).
2. **For FW inputs the converse holds.** Let `P` be finitely generated with property FW. Let a
   genuine action with infinite supports and an endomorphism `ψ` satisfy
   `s^m ρ_g s^-m = ρ_(ψ(g))` near. Then `ρ` restricts to a self-similar action of defect `m` on a
   cofinite `ρ(P)`-invariant subset of `N`.
3. **The ascending direction never occurs for infinite FW inputs,** at any shift power:
   `fw-inputs-admit-no-twisted-shell-normalization` for `s`, and
   `fw-inputs-admit-no-twisted-normalizing-genuine-shell-action` or
   `fw-inputs-fail-commuting-shell-windows`, Step 5, for `s^m`.
4. **Commuting windows reduce to window zero on `[P,P]`**
   (`fw-inputs-fail-commuting-shell-windows`).
   - An ascending commuting window of width `N` never occurs.
   - A descending one yields a self-similar action of `[P,P]` of defect `N+1`, by item 2.
5. **Property X: what a self-similar action of an infinite FW group forces.**
   - `Z(P)` has finite exponent, for every `m`
     (`fw-descending-shift-power-windows-force-torsion-centre`).
   - For `m = 1`, in addition:
     - `P` acts highly transitively on each orbit (`fw-shell-inputs-at-window-zero-are-highly-transitive`);
     - `ψ` has trivial core `⋂_j ψ^j(P)` and `[P : ψ(P)] = ∞`
       (`fw-window-zero-descending-sign-forces-trivial-core`, `fw-inputs-pass-window-zero-only-via-proper-self-embeddings`);
     - `C_P(ψ(P))` has finite exponent (`descending-shell-endomorphisms-have-finite-exponent-centralizers`).

## The verdict for Kazhdan inputs

For an infinite finitely generated Kazhdan (or FW) input `P`:
- the shell route through window zero, of any sign and any shift power, exists exactly when
  `P` has a self-similar action of finite defect;
- through commuting windows it needs one for `[P,P]`.

Item 5 lists what that action forces. So the fate of these routes is decided by one intrinsic
question: **does `P` admit a faithful self-similar action of finite defect?** Consequences:

- **Excluded at every defect, since they have a central subgroup of infinite exponent.**
  `St_N(R_L)` and `E_N(R_L)` (`N >= 4`), and Deligne's lattice.
- **Excluded at defect one, since they are co-Hopfian.** Every co-Hopfian FW input
  (`fw-window-zero-descending-sign-forces-trivial-core`, item 3).
  Higher defect for co-Hopfian inputs is not settled here.
- **Excluded.** The corner endomorphism of `EL_n(L_(F_2)(1,2))`.
- **Not decided here.** A simple Kazhdan group with a trivial-core endomorphism of infinite
  index and a highly transitive self-similar action. No example is known.
- **Outside this criterion.** Non-commuting windows `N >= 1`. It is open whether they reduce to
  it.

## Lesson for general BH

- *FW turns every near-equivariance into an exact one.* The graph of a near-equivariant map
  is a commensurated set, and FW transfixes it.
- So for Kazhdan inputs the shell's germ gate at window zero is not about enumerations but
  about an intrinsic self-similarity of the group: `X ≅ X − Y` twisted by an endomorphism.
- For a finitely presented input, a self-similar action of defect one is also sufficient for
  a finitely presented germ group. The remaining gap in the shell route is then the one-point
  stabilizer `A_1`.
