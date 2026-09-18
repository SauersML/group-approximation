---
rg: 2
id: free-rewritable-tape-layers-kill-finite-presentation
kind: claim
title: A freely rewritable full-shift layer kills finite presentation; over every infinite finitely generated group, no finitely presented subgroup of the V-times-Turing-machine full group contains the translations and the tape-conditioned 3-cycles
distinct_from:
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that is about the transformation groupoid Λ ⋉ X, whose full group can move the tape but never rewrite it; this adds every local rewrite of a full-shift layer (the homoclinic relation), which makes the groupoid minimal for free, and shows that finite presentation still fails.
  fp-alternating-full-groups-of-free-subshifts-force-sft: that forces finite type of a transformation groupoid's subshift; here the tape is a full shift, of finite type trivially, and the obstruction is the rewriting layer's lack of constraints.
  car-bernoulli-crossed-product-is-lamplighter-ring: that identifies the Λ = Z tensor-shift ring with the lamplighter crossed product; the ring remark below shows that ring (for every infinite Λ) is not finitely presented.
---

**ESTABLISHED** (lane proof, elementary; bh-invent-10, 2026-09-18; not independently reviewed). Route:
`free-rewritable-tape-layers-kill-finite-presentation-proof`. No priority claimed. Barbieri–Kari–Salo
(arXiv:1603.08715, arXiv:2303.17270, read at source) study the `Λ = Z^d` groups of reversible Turing
machines (finite generation, torsion problem) and do not discuss finite presentation. A bounded web
search found no statement of the theorem below.

## Setting

- `Λ` is an infinite group with finite symmetric generating set `S`, word metric `d`, and balls `B_D`.
- `Y ⊆ B^Λ` is an arbitrary subshift (a single point is allowed), `A` is an alphabet with `|A| >= 2`, and
  `X = Y × A^Λ ⊆ (B × A)^Λ` carries the diagonal shift `(g.ξ)(h) = ξ(g^(-1) h)`. The second layer is the *tape*.
- `ℋ` is the tape-homoclinic relation: `(ξ~, ξ) ∈ ℋ` iff the two points have the same `Y`-layer and their
  tapes differ at finitely many sites. With the inductive-limit topology of the relations
  `ℋ_F = {tapes agree off F}` (`F` finite, product topology on each), `ℋ` is an ample AF equivalence relation on `X`.
- The *Turing groupoid* is `𝒯 = Λ ⋉ ℋ`, with arrows `(λ, ξ~, ξ)` from `ξ` to `λ.ξ~`. Its bisections are
  finite-window rewrites of the tape followed by translations. The moving-tape reversible Turing machines of
  Barbieri–Kari–Salo are the full group of `𝒯 × (pair groupoid on the states)` for `Λ = Z^d` and `Y` a point.
- `G_V` is the groupoid of germs of Thompson's `V` on `C = {0,1}^N`, and `T' = G_V × 𝒯` on `C × X`.
- `t_s ∈ F(T')` is translation by `s ∈ S`. For `a ∈ A`, `e_a ∈ F(T')` applies the 3-cycle
  `h : 00w -> 01w -> 1w -> 00w` to the `C` coordinate when the tape letter at the origin is `a`, and is the
  identity otherwise.

## Theorem

No finitely presented subgroup `Γ ≤ F(T')` contains every `t_s` and every `e_a`. This holds for every infinite
finitely generated `Λ`, every subshift `Y`, every tape alphabet with at least two letters, and every choice of the
remaining generators of `Γ` (they may rewrite the tape arbitrarily).

**Corollary 1 (Turing–Thompson groups).** Take `Y` a point, so `X = A^Λ`.
- `T'` is minimal and effective, so `F(T') = A(T')` is simple. It contains `Λ` (the translations) and the
  lamplighter group `Sym(A) ≀ Λ` (translations and rewrites at the origin).
- `F(T')` is finitely generated (route, Section 4, a sketch through Nekrashevych's expansivity criterion).
- `F(T')` is not finitely presented.

So every infinite finitely generated group `Λ` lies in an explicit finitely generated simple group of reversible
Turing machines with `V`-controlled head states. None of these groups is finitely presented, whatever `Λ` is.

**Corollary 2 (a simple subgroup of 3V).** Let `c : G_V -> Z` be the length cocycle of prefix replacements.
Let `3V_□ ≤ 3V` be the group of elements of the Brin–Thompson group all of whose germs `(g_1, g_2, g_3)` satisfy
`c(g_2) + c(g_3) = 0`. Informally, these are the elements that preserve the area of the last two coordinates.
- `3V_□` is `F(T')` for `Λ = Z`, `A = {0,1}` and `Y` a point.
- It is simple, and finitely generated (sketch, as in Corollary 1). It contains the baker's map and `Z/2 ≀ Z`.
- It is not finitely presented.

(For comparison, `{g ∈ 2V : c(g_1) + c(g_2) = 0}` is Barbieri–Kari–Salo's `RTM(2,1)`, which they prove is not
finitely generated. The extra `V` coordinate is what restores finite generation.)

**Remark (ring analogue).** For every infinite finitely generated `Λ` and every field `k`, the tensor-shift ring
`(⊗_Λ M_A(k)) ⋊ Λ` is not a finitely presented `k`-algebra. For `Λ = Z` and `|A| = 2` this is the lamplighter
ring of `car-bernoulli-crossed-product-is-lamplighter-ring`. The route (Section 5) gives the same proof without
the `V` coordinate.

## Calibration

- **Without rewriting.** If every generator of `Γ` lies in `F(G_V × (Λ ⋉ X))`, the theorem is contained in
  `fp-v-times-subshift-full-groups-force-quantum-rigidity`, since `A^Λ` is not quantum rigid. The new content is
  that unlimited rewriting power does not rescue finite presentation.
- **Finite `Λ`.** Then `T'` is `G_V` times a finite pair groupoid, and `F(T')` is a Higman–Thompson group,
  which is finitely presented. The proof uses that `Λ` is infinite in exactly one place: two far sites must
  receive the same colour.
- **Scope.** Only *unconditioned* rewriting of an *unconstrained* layer is covered. Conditioned rewrites of a
  constrained layer, such as defects in a rigid SFT that surgery may create or remove, are not covered. There,
  slot families (below) must satisfy the layer's constraints, and in general they do not.

## Lesson for general BH

**No free layer.** Finite presentation fails at the level of a single site whenever a site is free.
- The necessity theorem's orbit representation only ever sees a ball. So any layer in which no constraint ties
  a site to its neighbours can be realized by a *slot family*:
  - properly colour the `2D`-neighbourhood graph of `Λ` with finitely many colours, one tensor slot per colour;
  - let far sites of the same colour share a slot, in rotated bases.
  The family commutes on every ball but not globally.
- Rewriting power (a Turing tape, homoclinic surgery) turns the site idempotents into matrix units. It changes
  nothing, because matrix units sit in a slot just as well as idempotents.

**For the master route.**
1. **E1 cannot be bypassed** by buying minimality from a free layer (Bernoulli noise, a scratch tape,
   surgery). The groupoid becomes minimal, but finite presentation is lost.
2. **In an fp host every symbol must be pinned by local constraints.** So the minimal free structure has to be
   carried by a constrained, hierarchical SFT, and that layer's rigidity is E2. Minimality and rigidity are paid
   for by the same constraints.
3. **Where freedom can live.** The only freedom an fp host can afford is freedom that is not local, such as the
   phases of a hierarchy, which no single site can change. That is exactly where E1's crux
   (`nonamenable-products-have-minimal-sft-extensions-of-free-inputs`, the phase field) sits.
