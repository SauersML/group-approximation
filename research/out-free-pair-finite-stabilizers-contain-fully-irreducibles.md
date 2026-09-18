---
rg: 2
id: out-free-pair-finite-stabilizers-contain-fully-irreducibles
kind: claim
title: In any action of Out(F_n), n at least three, with finitely many orbits of pairs and an infinite orbit, the stabilizers of that orbit contain fully irreducible elements and are never virtually reducible or commensurated
requires:
  - bounded-orbit-subgroups-have-infinitely-many-double-cosets
distinct_from:
  out-free-groups-satisfy-boone-higman: that is the open target; this is a necessary condition on the only direct route BFFHZ Remark 2.5 discusses, a type (A) action of Out(F_n) itself, and it does not decide the target.
  commensurator-rigid-groups-have-no-faithful-bs-members: that shows BLIW Theorem C never applies to Out(F_n) (n ≥ 4) because its vertex groups would be commensurated; this shows type (A) stabilizers are never commensurated, so commensurator rigidity says nothing against the type (A) route.
  aut-free-groups-satisfy-permutational-boone-higman: that is BFFHZ Theorem A, whose actor is Aut_G(G∗F_n), not Aut(F_n); nothing here constrains that actor.
---

**ESTABLISHED** (lane proof, elementary given the cited inputs; not reviewed; no
priority claimed). Inputs read only at abstract level this session: Handel–Mosher
arXiv:0908.1255 (subgroup alternative, for all subgroups), Horbez arXiv:1404.4626
(short proof), Kapovich–Lustig arXiv:0711.3806 and Bestvina–Feighn
arXiv:1107.3308 (the free factor complex `FF_n` is connected, hyperbolic and of
infinite diameter). That `FF_n` is among Kapovich–Lustig's infinite-diameter
complexes is recalled, not read.

**Statement.** Let `n ≥ 3` and let `Out(F_n)` act on a set `X` with finitely many
orbits of ordered pairs. Let `x ∈ X` have infinite orbit, and put `H = Stab(x)`.
Then:
1. **Unbounded.** `H` has unbounded orbits on `FF_n`.
2. **Not virtually reducible.** No finite-index subgroup of `H` fixes the
   conjugacy class of a proper nontrivial free factor. By Handel–Mosher, `H`
   therefore contains a fully irreducible element.
3. **No geometric stabilizers.** `H` is not virtually contained in the
   stabilizer of any of the following:
   - a proper free factor, a free factor system, or a free splitting (a vertex
     group of a one-edge free splitting is a proper free factor, and an index ≤ 2
     subgroup of its stabilizer fixes that factor's class);
   - the conjugacy class of a non-filling element;
   - a point, or bounded set, of Outer space (bounded orbits there are finite).
4. **Not commensurated.** `H` is not commensurated in `Out(F_n)`.

Since a faithful action of an infinite group with finitely many pair orbits has
an infinite orbit, every type (A) action of `Out(F_n)` in Zaremsky's sense has
such stabilizers.

**Proof.**
- **Items 1 and 4.** `X ⊇ Out(F_n)·x ≅ Out(F_n)/H` has finitely many pair
  orbits, so `H\Out(F_n)/H` is finite and `[Out(F_n) : H] = ∞`. `Out(F_n)` acts
  on the vertices of `FF_n` with finitely many orbits (one per rank). Infinite
  diameter then forces unbounded orbits: if `Out(F_n)·v` had radius `R` about
  `v`, every vertex `g·v_i` would lie within `R + max_i d(v, v_i)` of `v`. Apply
  item 1 and item 2 of `bounded-orbit-subgroups-have-infinitely-many-double-cosets`.
- **Item 2.** If `H' ≤ H` has finite index and fixes the vertex `[A]`, then
  `H·[A]` is finite, so bounded, contradicting item 1. Handel–Mosher's
  alternative holds for all subgroups (both abstracts), so `H` contains a fully
  irreducible element.
- **Item 3, non-filling classes.** Let `w` lie in a proper free factor. The
  intersection `A_w` of all free factors containing `w` is a free factor, since
  an intersection of two free factors is a free factor and ranks descend. If
  `φ` fixes `[w]`, choose a lift `Φ` with `Φ(w) = w`. Then `Φ(A_w)` is a free
  factor containing `w`, so `A_w ⊆ Φ(A_w)`. A free factor contained in a free
  factor of the same rank equals it, so `Φ(A_w) = A_w`. So `Stab([w])` fixes
  `[A_w]`, which is proper, and item 2 excludes it.

**What survives.** A direct type (A) actor built from `Out(F_n)` needs a finitely
generated, infinite-index subgroup `H` with finitely many double cosets. `H` must
contain fully irreducibles, act with unbounded orbits on `FF_n`, and fix no
proper free factor class even virtually. Candidates not excluded here:
- stabilizers of conjugacy classes of filling elements, such as the boundary word
  of a one-boundary surface, whose stabilizer contains geometric fully
  irreducibles;
- subgroups built by small cancellation (Hull–Osin) or from Tarski presentations
  (Garion–Glasner), which BFFHZ Remark 2.5 already doubts are finitely generated.

Whether `Stab([w_∂])` has finitely many double cosets is the next concrete test.
Recorded as Attempt 4 on `out-free-groups-satisfy-boone-higman`.

**Update.** The test case above is settled negatively for one-cusp orientable
surface words in even rank: `surface-word-stabilizers-have-infinitely-many-double-cosets`.
The `Aut`-orbit of the surface word grows exponentially in word length, while
each mapping-class-group orbit grows polynomially.
