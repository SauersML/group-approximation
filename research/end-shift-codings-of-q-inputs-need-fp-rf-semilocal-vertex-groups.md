---
rg: 2
id: end-shift-codings-of-q-inputs-need-fp-rf-semilocal-vertex-groups
kind: claim
title: The end shift of a cocompact locally finite tree with finitely generated vertex stabilizers is an SFT over the acting group; if that group is finitely presented, contains (Q,+) and acts topologically freely on the ends, some vertex stabilizer is a finitely presented residually finite group containing a semilocalization Z_(S) of Z
requires:
  - bounded-valence-trees-scale-only-primes-below-the-valence
  - decidable-fp-groups-have-effective-minimal-free-subshifts
  - steinberg-groups-of-r-l-are-quasisimple
distinct_from:
  free-group-boundary-shifts-are-quantum-rigid: that codes the end shift over a group whose Cayley graph is the tree (finite stabilizers); this codes it over any finitely generated group acting cocompactly on a locally finite tree with finitely generated vertex stabilizers, which is what an input containing (Q,+) needs, since its vertex stabilizers are necessarily infinite.
  z-localized-embeds-in-fp-rf-group: that is the OPEN question whether some Z_(l) lies in a finitely presented residually finite group, needed by three gq host routes; this shows the boundary route to (★′) for every input containing (Q,+) needs the weaker semilocal form, so a refutation of the semilocal form kills four routes.
  locally-finite-tree-end-shifts-are-quantum-rigid-sfts: that node (bh-star-a, f2bfa4b84, landed the same hour) proves part 1 here and also quantum rigidity; this adds the vertex-group consequences for inputs containing (Q,+), parts 2 and 5.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports Bux–Llosa Isenrich–Wu, whose Theorem A embeds every faithful cocompact locally-finite-tree group with finitely presented edge stabilizers in a finitely presented simple group; part 5 here shows every such host of an input containing (Q,+) needs (SL).
  gl-n-q-bh-via-track-a-over-st-10-times-free-group: that route gets minimality from (M2) for St_10(R_L) plus minimal product simulation; this is the boundary alternative, where the end shift is minimal and topologically free at once, and it shows St_10(R_L) can never be the acting group there.
---

**ESTABLISHED** (lane bh-gln-tracka, 2026-09-18; elementary Bass–Serre theory and symbolic dynamics, lane proof, not
reviewed; no priority claimed).

**Correction (same day, lane bh-gln-tracka).**
- Part 1 duplicates item 1 of `locally-finite-tree-end-shifts-are-quantum-rigid-sfts` (bh-star-a, f2bfa4b84), landed
  the same hour. That node also proves quantum rigidity of `X_T`.
- The "boundary alternative" below is subsumed by Bux–Llosa Isenrich–Wu. Their Theorem A
  (`thm:main-actions-on-trees`, read at source in `$GQ/src/bh-free-05/bliw-2408.05673v2.tex`) embeds every group
  acting faithfully and cocompactly on a locally finite tree with finitely presented edge stabilizers in a finitely
  presented simple group. Every `Λ` of part 2 is such a group. So wherever the end-shift route to (★′) applies, BH
  for its subgroups already follows directly, with no rigidity or E3′ step.
- The lasting content is therefore part 5, an obstruction to the whole BLIW method: every BLIW host of an input
  containing `(Q,+)` needs (SL). Parts 2–4 are its special cases.

## Setting

`Λ` is a finitely generated group acting without inversions on a locally finite tree `T`.
- There are finitely many orbits of vertices, with representatives `v_1, ..., v_r`, and every vertex stabilizer
  `Λ_v` is finitely generated.
- `E(v)` is the finite set of edges at `v`, and `d` is the maximal valence.
- For a finite set `S` of primes, `Z_(S)` is the ring of rationals whose denominators are prime to every `p ∈ S`.
  So `Z_({l}) = Z_(l)`, and `Z_(S) ⊆ Z_(l)` for every `l ∈ S`.

## Theorem

1. **The end shift is an SFT.** Put `A = E(v_1) × ... × E(v_r)`. For an end `ξ` let `out_ξ(w)` be the edge at `w`
   pointing to `ξ`, and let `x_ξ(g) = (g^(-1)·out_ξ(g v_i))_i ∈ A`. Then `ξ ↦ x_ξ` is a `Λ`-equivariant homeomorphism
   of `∂T` onto a subshift of finite type `X_T ⊆ A^Λ`. So `X_T` is minimal, or topologically free, exactly when the
   action on `∂T` is.
2. **Vertex groups.** Suppose in addition that:
   - `Λ` is finitely presented;
   - `Λ` acts topologically freely on `∂T`;
   - `Λ` contains a nonzero subgroup `A_0` of `(Q,+)` that is `ℓ`-divisible for every prime `ℓ > d`.

   Then some vertex stabilizer `Λ_v` is a finitely presented residually finite group containing a copy of `Z_(S)`,
   where `S` is the set of primes `≤ d`.
3. **Inputs.** Hypothesis 2 on `A_0` holds for every `Λ` containing `(Q,+)`, hence for every `Λ` containing
   `GL_n(Q)`, `SL_n(Q)`, `PGL_n(Q)` (`n >= 2`), `Aff(Q)` or `U_3(Q)`.
4. **Not `St_10(R_L)`.** No `Λ` as in 2 contains `St_10(R_L)`, or any infinite group with property (FA) and no
   nontrivial finite quotient.
5. **BLIW hosts.** Let `Λ` act faithfully and cocompactly on a locally finite tree with finitely presented edge
   stabilizers (the hypotheses of BLIW Theorem A), and let `Λ` contain `A_0` as in 2. Then some vertex stabilizer is
   a finitely presented residually finite group containing `Z_(S)`, `S` the primes `≤ d`. So the BLIW method applied
   to `GL_n(Q)`, `Aff(Q)`, `U_3(Q)` or `(Q,+)` presupposes (SL) below, whatever the tree.
6. **Splittings cannot create (SL).** Let `Λ = π_1(𝕐)` for a finite graph of groups with all edge groups of finite
   index in the adjacent vertex groups, and suppose `Λ` is residually finite and contains `Z_(S)` for a finite set
   `S`. Then some vertex group, which is residually finite and is finitely presented if `Λ` is and the edge groups
   are finitely generated, contains `Z_(S')` with `S' = S ∪ {primes ≤ d}`. So an (SL) witness built as such a
   graph of groups already has one among its vertex groups. Only splittings with edge groups of infinite index,
   where `Z_(S)` can be an ascending union of edge groups along a ray (`z-localized-fixes-a-vertex-or-end-of-every-tree`),
   can produce new divisibility.

## Proof

**1, the rules.** `X_T` is cut out by two finite families of rules.
- **(V)** For each `i` and each generator `k` of `Λ_(v_i)`: `x(gk)_i = k^(-1)·x(g)_i`.
- **(E)** For each `i` and each edge `e = [v_i, w] ∈ E(v_i)`, fix `c ∈ Λ` and `j` with `w = c v_j`, and let
  `e' = c^(-1)e ∈ E(v_j)`. Then exactly one of `x(g)_i = e` and `x(gc)_j = e'` holds.

Both families are finite: `Λ_(v_i)` is finitely generated, and `T` is locally finite with finitely many vertex
orbits.

**1, `x_ξ` satisfies the rules.** For `k ∈ Λ_(v_i)`,
`x_ξ(gk)_i = k^(-1) g^(-1) out_ξ(g v_i) = k^(-1)·x_ξ(g)_i`. Rule (E) says the edge `g e` is the out-edge at exactly one
of its endpoints `g v_i` and `g c v_j`, which holds for the orientation toward `ξ`.

**1, every solution comes from an end.** Let `x` satisfy (V) and (E).
- **An out-edge at each vertex.** Define `o(g v_i) = g·x(g)_i`. By (V), applied along a word in the generators (and
  to inverses, since `x(g) = x((gk^(-1))k)`), `x(gk)_i = k^(-1) x(g)_i` for every `k ∈ Λ_(v_i)`. So `o` is well
  defined on vertices.
- **Each edge oriented once.** By (E), every edge is the out-edge of exactly one of its endpoints.
- **A ray from each vertex.** Following out-edges from a vertex never reverses along an edge, so it traces a ray.
- **One end.** If `o(u) = [u, w]`, the ray from `u` is `u` followed by the ray from `w`. Adjacent vertices therefore
  have rays with the same end `ξ`, and since `T` is connected all rays converge to `ξ`.
- **So `x = x_ξ`.** Each edge is oriented toward `ξ`.

**1, homeomorphism.** `ξ ↦ x_ξ` is injective, since `x_ξ` gives the out-edge at every vertex, and hence `ξ`. It is
continuous, since `out_ξ(w)` is locally constant in `ξ`, and equivariant by the displayed computation:
`x_(hξ)(g) = (h^(-1)g)^(-1) out_ξ(h^(-1) g v_i) = x_ξ(h^(-1) g)`. `∂T` is compact, so this is a homeomorphism onto
its image, which is `X_T`.

**2, finite presentation.**
- `Λ` is the fundamental group of the quotient graph of groups (Bass–Serre), a finite graph.
- Each edge group `Λ_e ≤ Λ_v` has index at most `deg(v)`, since the `Λ_v`-orbit of `e` lies in `E(v)`. So the edge
  groups are finitely generated.
- For the fundamental group of a finite graph of groups with finitely generated edge groups, the whole group is
  finitely presented iff every vertex group is. This is standard (recalled; for example by building a presentation
  complex from the pieces).

So every `Λ_v` is finitely presented.

**2, residual finiteness.**
- If `γ ≠ 1` acted trivially on `T`, then `Fix(γ) = ∂T` would be open, contradicting topological freeness. So `Λ`
  acts faithfully on `T`.
- Hence `Λ_v` embeds in `Aut(T)_v`, which is profinite because `T` is locally finite: it is the inverse limit of its
  actions on the balls around `v`.
- So `Λ_v` is residually finite.

**2, `Z_(S)` in a vertex group.**
- By `bounded-valence-trees-scale-only-primes-below-the-valence`, part 4, some `(A_0)_v = A_0 ∩ Λ_v` is nonzero and
  `ℓ`-divisible for every prime `ℓ > d`.
- For `a ∈ (A_0)_v` nonzero and `n` a product of primes `> d`, dividing repeatedly gives `a/n ∈ (A_0)_v`.
- So `a·Z_(S) ⊆ Λ_v`, and `a·Z_(S) ≅ Z_(S)`.

**3.** `(Q,+)` is `ℓ`-divisible for every `ℓ`. The groups listed contain `(Q,+)` as a root group, as the
translations, or as the centre.

**5.** Faithfulness on `T` embeds each vertex stabilizer in the profinite group `Aut(T)_v`, so each is residually
finite. Each is a finite-index overgroup of a finitely presented edge stabilizer, hence finitely presented. The copy
of `Z_(S)` comes from `bounded-valence-trees-scale-only-primes-below-the-valence`, part 4, as in part 2.

**6.** The Bass–Serre tree has valence at most `d`. Apply that node, part 4, to `A_0 = Z_(S)`, which is `ℓ`-divisible
for every prime `ℓ ∉ S`, in particular for every `ℓ > d` outside `S`. Some `Z_(S) ∩ Λ_v` is nonzero and divisible by
every prime outside `S'`, so it contains a copy of `Z_(S')`. Vertex groups are subgroups of `Λ`, so they are
residually finite. Finite presentation is as in part 2.

**4.** `St_10(R_L)` is Kazhdan, hence has (FA), so it fixes a vertex `v` and lies in `Λ_v`. `Λ_v` is residually
finite by part 2, so `St_10(R_L)` would be residually finite. But `St_10(R_L)` is infinite with no nontrivial finite
quotient: it is generated by divisible root subgroups
(`decidable-fp-groups-have-effective-minimal-free-subshifts`, item 5). The same argument works for any infinite
(FA) group with no nontrivial finite quotient. ∎

## Reading for Boone–Higman and 5.3(5)

**The boundary alternative to (M2).**
- On the group route, (★′) needs a quantum-rigid, minimal, topologically free SFT over an fp `Λ ⊇ GL_n(Q)`
  (`master-route-needs-only-topological-freeness`).
- Part 1 supplies minimality and topological freeness at once, by an end shift, whenever the action on `∂T` is
  minimal and topologically free. So it bypasses (M2) and the
  minimal product-simulation premise of `gl-n-q-bh-via-track-a-over-st-10-times-free-group` altogether.
- The model is `PGL_2(Q)` on the `(p+1)`-regular tree (`gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings`).
  - Minimal: `PGL_2(Q)` is dense in `PGL_2(Q_p)`.
  - Topologically free: a nontrivial Möbius map fixes at most two points of `P^1(Q_p)`.
  - Vertex stabilizers `PGL_2(Z_(p))`, which contain `Z_(p)`.

**What the alternative costs** (parts 2 and 4).
- *An acting group.* An fp group `Λ` acting cocompactly on a locally finite tree with finitely generated vertex
  stabilizers and containing `PGL_2(Q)` or `GL_n(Q)`. It cannot contain `St_10(R_L)`, so it is not the explicit
  overgroup of Problem 2.7.
- *Its vertex groups.* They are fp residually finite groups containing `Z_(S)`. So the alternative implies the
  **semilocal form** of `z-localized-embeds-in-fp-rf-group`:

  > **(SL)** some finitely presented residually finite group contains `Z_(S)` for some finite set `S` of primes.

  `z-localized-embeds-in-fp-rf-group` (`S = {l}`) implies (SL), but not obviously conversely.
- *What is already excluded.* By `fg-linear-groups-have-roots-at-finitely-many-primes` and
  `fg-metabelian-groups-have-roots-at-finitely-many-primes`, the vertex groups are neither linear nor metabelian.
- *Rigidity, still open.* The end shift is rigid for Cayley trees (`free-group-boundary-shifts-are-quantum-rigid`).
  Rigidity of `X_T` with infinite finitely generated stabilizers is expected by the same monotone-chain argument:
  rules (V) identify frames at a vertex, and rules (E) are exactly the Cayley-tree edge rules. This is not checked
  here.

**Consequences, either way.**
- *If (SL) is false:* no locally finite tree boundary carries any input containing `(Q,+)`, which with
  `gl-n-q-fixes-a-vertex-in-free-splittings` leaves the (IE) emitter gate or programmable (gate 3) rigidity as the
  only sources of (★′) for 5.3(5).
- *If (SL) holds* with enough structure to contain `PGL_2(Z_(p))` compatibly with its action on the rooted tree:
  5.3(5) for `n = 2` reduces to rigidity of one tree end shift plus E3′.

## Lesson for general BH

A tree boundary is minimal and topologically free for free, and it is an SFT exactly when vertex stabilizers are
finitely generated. For inputs that fix points of trees (Kazhdan inputs) or divide by infinitely many primes
(divisible inputs), the boundary route therefore moves the whole input problem into the vertex groups. They must be
finitely presented and residually finite, and must carry the input's divisibility or its (FA) part. Residual
finiteness is forced by topological freeness on the boundary. So a boundary SFT turns BH for such an input into an
RF Higman-embedding problem for its vertex part:
- impossible for Kazhdan inputs without finite quotients (part 4);
- equal to (SL) for divisible inputs.

This is the precise sense in which compression codings "need an infinite emitter": finite valence plus finite
generation forces residually finite vertex groups.
