---
rg: 2
id: dynamically-v-separated-groups-satisfy-boone-higman
kind: claim
title: A finitely presented group with an injective endomorphism φ and a representation ρ in V whose φ-orbit separates points lies in a finitely presented full Cantor group, hence embeds in a finitely presented simple group
distinct_from:
  annular-hosts-with-free-zoom-germs-are-not-finitely-presented: that shows annular hosts with no cross-depth germ relations are never finitely presented; this is the positive counterpart, where the single cross-depth relation t^(-1) g t = φ(g) makes every SingFix group an iterated ascending HNN extension, so the host is finitely presented.
  orbit-preserving-germ-corollary-extensions-of-v-are-rational: that treats Belk--Hyde--Matucci Corollary 2.10, where the zoom germs are normal and hosts are rational; here the germ group is an ascending HNN extension, in which the zoom is not normal, and Theorem 2.1 is applied directly.
  rf-groups-have-free-product-germs-over-v: that realizes residually finite groups with germ group G * Z through unrelated finite quotients, which kills finite presentation; this realizes a group through iterates of one representation under one endomorphism.
  f-infinity-tail-ascending-hnns-satisfy-boone-higman: that uses the same mechanism, a one-orbit germ extension whose germ group is an ascending HNN extension, for last-section endomorphisms of subgroups of bounded automata groups over V_d S; this is the abstract version over V itself, for any finitely presented group with an injective endomorphism and a V-representation separating along its orbit, with no automaton.
artifacts:
  - research/artifacts/beyond-polynomial-germs/mapping-tori-and-compact-core.md
---

**ESTABLISHED** by `dynamically-v-separated-host-singfix-proof` (lane proof. It rests on
Belk--Hyde--Matucci Theorem 2.1 and on the `F_∞` stabilizers of `V`, both imported in
`germ-complex-and-bux-gonzalez-morse-inputs`, and on the type (A) criterion named above.
Not reviewed; no priority claimed).

The 2026-09-20 *Beyond polynomial germs* manuscript proposes the
stronger OPEN `observed-mapping-tori-have-simple-fk-hosts`: for an
automorphism with both forward and backward separating observations,
embed the entire mapping torus and its twisted `V` lamps in a simple
type `F_k` host. Its two-species realization and uniform compact-core
SingFix theorem are unverified new gates. The present one-sided
finite-presentation result retains its existing status and is not
silently upgraded to that bilateral or higher-finiteness statement.

The mechanism, ascending germ groups at one singular orbit certified by Theorem 2.1,
is the one of `f-infinity-tail-ascending-hnns-satisfy-boone-higman`. What is new is the
abstract input condition, with base `V` and no self-similar structure.

**Definition.** Let `G` be a group, `φ: G -> G` an injective endomorphism and
`ρ: G -> V` a homomorphism. `(G, φ, ρ)` is **dynamically V-separated** if for every
`g != 1` there are infinitely many `m` with `ρ(φ^m(g)) != 1`.

**Theorem.** Let `G` be finitely presented and dynamically V-separated. Then:
1. `G` embeds in a finitely presented group `Γ` of homeomorphisms of the Cantor set.
   `Γ` contains `V`, is full and clopen transitive, is a finite germ extension of `V`
   with one singular orbit, and has germ group `G *_φ` at the singular point.
2. Hence `G` lies in `B_A` and embeds in a finitely presented simple group.

**Construction.**
- Let `p = 0^∞`, `A_n = 0^n 1 C` and `α_n(w) = 0^n 1 w`.
- Replace `ρ` by `ι ∘ ρ`, with `ι: V -> V(1C)` the copy of `V` on the cone `1C`. This keeps
  the separation.
- Define `ĝ` to fix `p`, to be the identity on `A_0`, and to act on `A_n`, `n >= 1`, by
  `α_n ρ(φ^(n-1)(g)) α_n^(-1)`.
- `Γ` is the full closure of `<V, Ĝ>`.

**Example.** Let `G = Z^2 * Z = <a, b | [a,b]> * <c>`, `φ = (a, b, c ↦ a, ab, c)`, and
`ρ = (a, b, c ↦ α, 1, γ)` with `<α, γ>` free in `V`. Then `φ^m(a^i b^j) = a^(i+mj) b^j`, so
for large `m` every syllable of a reduced word survives and `G` is dynamically
V-separated. `Z^2 * Z` is not a subgroup of `V` (Bleak--Salazar-Díaz, cited, not read).
So the class is strictly larger than the subgroups of `V`.

**Consequences for Problem 5.3(12).**
- *Reduction.* Every finitely presented residually finite group that embeds in a finitely
  presented dynamically V-separated group satisfies Boone--Higman.
- *Torsion.* Unlike the self-similar route, this has no bounded-composition-factor
  obstruction: `V` contains every finite group.
- *Separation.* The separating family is the orbit of one representation under one
  endomorphism, which is the finite depth-transport rule demanded by
  `annular-free-product-germ-hosts-are-not-finitely-presented`.
- *Finite images excluded.* `ρ` must have infinite image for infinite `G`
  (`annular-free-factor-germ-extensions-fail-bhm-singfix`, item 2).

**Limits.**
- A dynamically V-separated `G` is residually a subgroup of `V`. In particular every
  simple subgroup of `G` embeds in `V`.
- So through its germs this host reaches only inputs that are residually `V`. General
  Boone--Higman inputs, such as simple groups with hard word problem, need other
  placements.
- Whether any finitely presented residually finite group with hard word problem embeds
  in a dynamically V-separated finitely presented group is open.

**Lesson for general BH.**
- *Two sides of one principle.* Local rigidity says a finitely presented host must fix
  every depth by finitely many relations. The ascending relation `t^(-1) ĝ t = φ(g)^` does
  exactly that: every SingFix group becomes an iterated ascending HNN extension of a
  finitely presented base.
- *Design rule.* Store the input as the orbit `ρ ∘ φ^m` of one representation under one
  endomorphism. A deterministic transition rule, possibly a machine step, and a fixed
  observation give finite presentation for free.
- *Where the difficulty moves.* It is now algebraic: find finitely presented overgroups
  whose endomorphism dynamics separates points through `V`. For a machine, that means
  an endomorphism acting as the step on configuration elements, with configurations
  not identified by relations. Reversible machines give automorphisms.
