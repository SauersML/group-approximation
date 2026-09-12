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

## 3. Proof

**Hierarchy gives envelope.** Fix `i >= 1`. By Bass--Serre theory `V_i` is the
fundamental group of the quotient graph of groups `V_i \ T_i`. The orbit of
`v_i` is one quotient vertex, with group `V_(i-1)`. Every other vertex group is
sofic and every edge group is amenable. Choose a maximal tree containing that
vertex and enumerate its vertices so that each is adjacent to an earlier one.
Adjoining a vertex group `X` along its tree edge is a move `Y *_E X`; the edge
group already lies in `Y` and is amenable. Each edge outside the tree is an HNN
move over amenable associated subgroups that already lie in the partial group.
Finite subgraphs give finitely many moves, and `V_i` is their directed union.
Composing the steps `i = 1, ..., k` builds `B` from `F`, so the identity is an
envelope.

**Envelope gives hierarchy.** Let `iota(F) = Y_0 <= Y_1 <= ... <= Y_r = B'` list the
moves, treating a directed union as its final stage; the argument below never
uses finiteness of `r`. Identify `B` with `iota(B)` and put `V_i = B ∩ Y_i`. Then
`V_0 = F` and `V_r = B`. Each `Y_i` acts on the Bass--Serre tree `T_i` of its
move:
* edge stabilizers are conjugates of the amenable edge groups;
* vertex stabilizers are conjugates of `Y_(i-1)` or of the sofic factor `X`;
* `Y_(i-1)` fixes a vertex `v_i`.

Restrict to `V_i`. Edge stabilizers are subgroups of amenable groups, so they
are amenable. `Stab_(V_i)(v_i) = V_i ∩ Y_(i-1) = V_(i-1)`. Every other vertex
stabilizer lies in a conjugate of `X`, which is sofic, or in a conjugate of
`Y_(i-1)`. The latter is sofic because it is built from the free group `iota(F)`
by moves, and the transport lemma with `S = iota(F)` makes it sofic. Subgroups of
sofic groups are sofic. ∎

**Remark.** The earlier necessary condition (envelope artifact, §5) is the top
nontrivial step of this hierarchy. The theorem shows that one splitting is not
enough: the vertex group containing `F` must again split, down to `F` itself.
