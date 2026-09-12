# Amenable envelopes are relative amenable hierarchies

Date: 2026-09-11. Written proof, not a Lean certificate. It answers the converse
question left by `amenable-envelope-magnus-piece-sofic-2026-09-11.md`, §5.

## 1. Definitions

Let `F <= B`. An **amenable envelope** of `(B, F)` is an injective
`iota: B -> B'`, where `B'` is obtained from `iota(F)` by moves of two kinds:
* `Y -> Y *_E X`, with `E` amenable and `X` sofic;
* HNN extensions of `Y` over amenable associated subgroups;

together with directed unions of such constructions. Directed unions change
nothing in the transport lemma (§2 of the envelope artifact): pushouts commute
with directed colimits, amalgam monotonicity keeps the embedding, and directed
unions of sofic groups are sofic.

A **relative amenable hierarchy** of `(B, F)` is a finite chain

    B = V_k >= V_(k-1) >= ... >= V_0 = F

such that for each `i >= 1`, `V_i` acts without inversions on a tree `T_i` in
which:
* edge stabilizers are amenable;
* `V_(i-1)` is the stabilizer of a vertex `v_i`;
* every vertex stabilizer outside the `V_i`-orbit of `v_i` is sofic.

## 2. Theorem

**Theorem.** `(B, F)` has an amenable envelope if and only if it has a relative
amenable hierarchy.

**Corollary (recursion).** If `B` is sofic, the soficity condition on side
vertex stabilizers holds automatically, since they are subgroups of `B`. So for
sofic `B`, an envelope exists exactly when `B` has a finite chain of tree
actions with amenable edge stabilizers, each step passing to the vertex
stabilizer containing `F` and the chain ending at `F`.

For a Magnus piece `B_0` of `G = <a,t | w>`, the relator `W_0` has fewer letters
than `w`. Under the inductive hypothesis "every one-relator group with a
shorter relator is sofic", `B_0` is sofic and envelopes reduce to pure
Bass--Serre data.
