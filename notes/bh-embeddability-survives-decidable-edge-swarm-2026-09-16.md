# Swarm lane: `bh-embeddability-survives-decidable-edge-hnn` (2026-09-16)

Agent label `swarm-bh-embeddability-survives-deci`. Hole locked with
`bin/cairn lock bh-embeddability-survives-decidable-edge-hnn --ttl 180m`, and
released at the end. Nothing committed.

**Outcome: partial progress.** One new ESTABLISHED-by-proof claim covers the
ascending case along automorphisms of `M * F_m` for a finitely presented simple
MIF group `M`. The general hole stays OPEN.

## 1. Setup

**Target.** `A` is finitely generated and embeds in a finitely presented simple
group. `C_1, C_2 <= A` are finitely generated with decidable membership, and
`phi : C_1 -> C_2` is an isomorphism. The claim is that `A*_phi` embeds in a
finitely presented simple group. It is a special case of Boone--Higman, and
decidability is necessary (`bh-embeddability-forces-decidable-edge-membership`).

**Orientation.** Attempts 1--6 on the node record the following:
- no action of `A*_phi` itself of the right kind is known;
- the envelope-first approach dies;
- finite-index edges are covered by Bux--Llosa Isenrich--Wu, except the mapping
  torus of an infinite finitely presented simple group (Attempt 4);
- the stable-permutation extension of an actor reduces the problem to three
  unsupplied clauses (Attempt 6).

Nodes read: `stable-permutation-hnn-of-type-a-actor-is-type-a` and its proof,
`relative-automorphism-of-fp-simple-mif-group-has-type-a-action`,
`pbh-class-closed-under-relative-holomorphs` and its proof,
`pbh-graph-product-closure-proof`, `type-a-action-gives-boone-higman-for-subgroups`,
`boone-higman-type-a-class-closed-under-finite-extensions`,
`fp-simple-highly-transitive-groups-satisfy-pbh`,
`power-map-free-mapping-tori-satisfy-permutational-boone-higman`,
`one-relator-groups-satisfy-boone-higman`, `fp-simple-kac-moody-lattices-are-mif`,
`binary-leavitt-unit-group-is-mif`.

**Convention.** `B_A` is the class of groups embedding in a group with a type
(A) action. Every group in `B_A` embeds in a finitely presented simple group
(Zaremsky, Corollary B).

**Tooling note.** `bin/cairn search` timed out at 120 s, so duplicate search was
done with ripgrep over `research/`. Searches for "automorphism ... M * F",
"mapping torus ... simple", "ascending HNN", "outer automorphism" and "MIF"
found no claim covering ascending HNN extensions along automorphisms of
`M * F_m` that move `M` by an outer automorphism.

## 2. Literature gate

WebSearch was unavailable (session quota exhausted), and the arXiv export API
returned HTTP 429 through both WebFetch and curl. So no keyword sweep of arXiv
2024--2026 could be run in this session. Pages fetched directly:

- **Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2** (HTML, fetched
  2026-09-16).
  - Theorem C, Theorem E and Corollary F, as already imported in the graph.
  - Remark 3.5, read verbatim this session. Finitely generated simple highly
    transitive groups are MIF (citing Hull--Osin, Theorem 5.9). Finitely presented
    simple groups of homeomorphisms of `{1..n}^N` containing `[V_n, V_n]` are
    highly transitive, among them `V` and the finitely presented commutator
    subgroups of Röver--Nekrashevych groups. Twisted Brin--Thompson groups are
    highly transitive. The finitely presented simple Burger--Mozes groups are
    highly transitive and MIF. Non-affine Kac--Moody groups over finite fields
    are the one source for which they say PBH remains open.
  - Remark 4.1 embeds `F_n ⋊_α Z` in `Aut(F_n)` when `α` has infinite outer
    order, through conjugation.
  - The Question 3.1 discussion says PBH is "not" preserved under amalgamated
    products "in general".
  - No statement about mapping tori of finitely presented simple MIF groups, or
    about HNN permanence, was found in the fetched text.
- **Bleak--Cameron--Maissel--Navas--Olukoya, arXiv:1605.09302** (abs page,
  fetched 2026-09-16). The abstract describes `Aut(G_(n,r))` for the
  Higman--Thompson groups through bi-synchronizing transducers. It does not say
  whether `Out(G_(n,r))` has elements of infinite order, and the body was not
  read. So this source was not used.
- **Earlier in this session**, consulted before a context compaction, with
  details not re-fetched now:
  - Zaremsky, arXiv:2405.18354 (Theorem A, Corollary B);
  - Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3 (Problem 5.3, item (9),
    quoted in `one-relator-groups-satisfy-boone-higman`);
  - Bux--Llosa Isenrich--Wu, arXiv:2408.05673;
  - arXiv:2512.10800v1 and arXiv:2609.01868.
  None of these proves the target, nor the ascending case of Section 3.
- **Kurosh subgroup theorem** and **malnormality of free factors**: standard
  (Lyndon--Schupp, Chapter IV; Serre, *Trees*). No theorem numbers are claimed.

**Unverified.** Whether any finitely presented simple MIF group has an
automorphism of infinite outer order was not settled from sources (see §6).

## 3. What was proven

**New claim** `mif-free-product-automorphism-ascending-hnn-is-pbh`, with route
`mif-free-product-ascending-hnn-pbh-proof`. The route requires
`relative-automorphism-of-fp-simple-mif-group-has-type-a-action` (BFFHZ Theorem E),
`stable-permutation-hnn-of-type-a-actor-is-type-a` and
`type-a-action-gives-boone-higman-for-subgroups`. Both files passed `check.sh`
with exit 0.

**Statement.** Let `M` be a finitely presented simple MIF group, `Q = M * F_m`,
`β ∈ Aut(Q)` arbitrary, and `J <= Q` with `β(J) ⊆ J`. Then `J *_β ∈ B_A`. When
`J` is finitely generated, `J *_β` embeds in a finitely presented simple group.

**Proof in five lines.**
1. `M` is freely indecomposable and not free, and free factors are malnormal.
   So by Kurosh `β(M) = gMg^-1`.
2. `β₀ = c_g^-1 ∘ β` gives an isomorphic mapping torus, and `β₀ = θ ∘ hat(α)`
   with `θ ∈ Aut_M(Q)` and `α = β₀|_M`.
3. In `P = Q * <x>`, right multiplication `ρ_q : x -> xq` embeds `Q` in
   `Ω = Aut_M(P)`. `hat(α)` normalizes `Ω`, and `Q ⋊_(β₀) Z` embeds in
   `Ω ⋊ <hat(α)>` by `s -> tilde(θ) hat(α)`.
4. On `X = Hom_M(P, M)` the permutation `f -> α ∘ f ∘ hat(α)^-1` normalizes the
   BFFHZ action and induces `hat(α)`. Case (c) of the stable-permutation claim
   puts `Ω ⋊ <hat(α)>` in `B_A`. When some power of the permutation lies in the
   image of `Ω`, it uses the infinite-order element `ρ_(z_1)`.
5. `J *_β` embeds in `Q ⋊_β Z` (normal form `t^-p j t^q`).

**Which instances of the hole this settles.**
- For an input `A = C_1 = J`, `C_2 = β(J)` and `phi = β|_J`, the conclusion
  holds with no decidability hypothesis. Decidability then follows, by
  `bh-embeddability-forces-decidable-edge-membership`.
- In particular it settles the mapping torus `A ⋊_phi Z` of an **infinite
  finitely presented simple MIF** group `A` along any automorphism. That is the
  case Attempt 4 isolates and Attempt 6 reduces to finding a normalizing
  permutation. The permutation is supplied here, on the actor `Ω`, not on `A`.
- The genuinely new instances are those where `phi|_M` has infinite order in
  `Out(M)`. Finite outer order already follows from (T) of
  `pbh-class-closed-under-relative-holomorphs` plus finite-index closure.
- **Not settled:**
  - mapping tori of finitely presented simple groups that are not known to be
    MIF;
  - every non-ascending edge;
  - every ascending edge whose endomorphism does not extend to an automorphism of
    some `M * F_m` with `M` finitely presented simple MIF.

**Suggested Attempt 7 text for the hole node** (the referee decides; I did not
edit the committed node):

> 7. **Mapping tori of MIF bases through a normalizing permutation of the BFFHZ
>    actor.** By `mif-free-product-automorphism-ascending-hnn-is-pbh`, for `M`
>    finitely presented simple MIF, every ascending HNN extension `J *_β` with
>    `J <= M * F_m` and `β ∈ Aut(M * F_m)` lies in `B_A`. This covers the
>    mapping-torus case of Attempt 4 when `A` is MIF, for automorphisms of every
>    outer order. It does not reach non-ascending edges: `<A, t>` inside
>    `(M * F_m) ⋊_β Z` is `A *_phi` only when the `β^i(A)` form a bi-infinite
>    tree product, and every edge map it reaches is, up to conjugation, the
>    restriction of an automorphism of `M`. *Partial.*

## 4. Two reduction lemmas (proved here, not made nodes)

These are short Britton arguments. I kept them out of `research/` because on
their own they settle no instance that is not already covered (see the
limitation below).

**Lemma 4.1 (conjugation realization).** Let `A <= X`, let `C_1, C_2 <= A`, and
let `phi : C_1 -> C_2` be an isomorphism. Suppose some `k ∈ X` satisfies
`k c k^-1 = phi(c)` for all `c ∈ C_1`. Let

```text
X *_(C_1) = < X, u | u c u^-1 = c  (c ∈ C_1) >
```

be the HNN extension of `X` along the identity of `C_1`. Then `A -> A`,
`t -> k u` defines an injective homomorphism `A *_phi -> X *_(C_1)`.

*Proof.*
- **Well defined.** `(ku) c (ku)^-1 = k c k^-1 = phi(c)`.
- **Setup.** Let `w = a_0 t^(e_1) a_1 ... t^(e_n) a_n` be Britton-reduced in
  `A *_phi`. That is, no `t a t^-1` with `a ∈ C_1`, and no `t^-1 a t` with
  `a ∈ C_2`. Substitute `t = k u` and `t^-1 = u^-1 k^-1`. The pinches of
  `X *_(C_1)` are `u x u^-1` and `u^-1 x u` with `x ∈ C_1`. Consider two
  consecutive letters `t^(e_i) a_i t^(e_(i+1))`.
- **`e_i = 1`, `e_(i+1) = -1`.** Between `u` and `u^-1` stands `a_i`, which is
  not in `C_1`. No pinch.
- **`e_i = -1`, `e_(i+1) = 1`.** Between `u^-1` and `u` stands `k^-1 a_i k`. It
  lies in `C_1` iff `a_i ∈ k C_1 k^-1`. Since `phi` is onto `C_2`,
  `k C_1 k^-1 = C_2`, and `a_i` is not in `C_2`. No pinch.
- **Equal signs.** These give no pinch in an HNN extension.
- **Conclusion.** So the image is reduced with `n` stable letters. If `n >= 1`
  it is nontrivial by Britton's lemma. If `n = 0`, `w = a_0 != 1` lies in `X`,
  which embeds in `X *_(C_1)`. ∎

**Corollary 4.2 (retract case).** In Lemma 4.1 suppose also `X ∈ B_A` and that
`C_1` is a retract of `X`. Then `A *_phi ∈ B_A`.

*Proof.* `X *_(C_1) ≅ X *_(C_1) (C_1 × <u>)`, compare the presentations. Part 1
of `pbh-graph-product-closure-proof` (Steps 0--5) gives
`X *_C (C × K) ∈ B_A` for `X, K ∈ B_A` and `C` a retract of `X`. Take `K = Z`,
which lies in `B_A` as a subgroup of the BFFHZ actor. ∎

**Limitation of 4.2.** Let `r : X -> C_1` be a retraction. Applying `r` to
`k c k^-1 = phi(c)` gives `r ∘ phi = c_(r(k))` on `C_1`, with `r(k) ∈ C_1`.
- **Abelian `C_1`.** This forces `r(phi(c)) = c`. For `BS(p, q)` (`A = <a>`,
  `C_1 = <a^p>`, `C_2 = <a^q>`) write `r(a) = a^(pn)`. From `r(a^p) = a^p` we get
  `pn = 1`, so `p = ±1`. Then `r(a^q) = a^q` must equal `a^p`, so `q = p`. Only
  `Z^2` survives.
- **Ascending, `C_1 = A`.** `r` is the identity on `A`, so `phi = c_(r(k))` is
  inner in `A`, and `C_2 = A`. Proper ascending extensions and outer
  automorphisms both die.

So 4.2 covers only near-trivial twisting. Lemma 4.1 is used again in §5.6.

## 5. Approaches and where each dies

### 5.1 Non-ascending edges inside a mapping torus

**Setup.** Let `β ∈ Aut(Q)`, `A <= Q`, `C_1 <= A` with `C_2 = β(C_1) <= A`, and
`phi = β|_(C_1)`. Then `A -> A`, `t -> t` defines `A *_phi -> Q ⋊_β Z` with
image `<A, t>`.

**Criterion (proved here).** This map is injective iff the natural map `T -> Q`
is injective. Here `T` is the bi-infinite tree product with vertex groups
`A_i = β^i(A)` (`i ∈ Z`) and edge groups `β^i(C_2) = β^(i+1)(C_1)`.

*Proof.*
- Both groups map onto `Z` by the `t`-exponent, compatibly. So injectivity is
  equivalent to injectivity on the kernels.
- The kernel `K` of `A *_phi -> Z` contains `A`. On the Bass--Serre tree it has
  quotient `K\L/A ≅ L/K = Z` on vertices, and likewise on edges. So `K` is the
  tree product of the `t^i A t^-i` over the `t^i C_2 t^-i` (Serre, *Trees*, §I.5).
- The kernel of `<A, t> -> Z` is generated by the `β^i(A)`, and the map on
  kernels is the natural map `T -> Q`. ∎

**Example where it fails.** Take `Q = M * <z>` and `β = c_z ∘ hat(α)`, so
`β(z) = z` and `β(M) = zMz^-1`. Let `A = M * zMz^-1`, let `1 != N < M` be
proper, and put `C_1 = N`, so that `C_2 = zα(N)z^-1 <= A`.
- **Collapse.** Replacing `M' = zMz^-1` by `t^-1 M' t` is a Tietze move. It
  turns the relations into `n = ι(α(n))`, with `ι` the isomorphism `M -> t^-1 M' t`.
  So `A *_phi ≅ (M *_(N = α(N)) M) * Z`.
- **Failure of the criterion.** `A_i ∩ A_(i+1)` contains `z^(i+1) M z^-(i+1)`,
  but the edge group is only `z^(i+1) α^(i+1)(N) z^-(i+1)`. For `y` in the
  difference, "y in `A_i`" times "y^-1 in `A_(i+1)`" is a reduced word of length
  2 in `T`, hence nontrivial, but it maps to `1` in `Q`.

**Dies.** It dies here, and more generally for free-factor examples. By the
Kurosh argument in "Where it stops" of the new claim, whenever `A` is freely
indecomposable and not infinite cyclic and `C_2 != 1`, every edge that can be
reached is, up to conjugation, an automorphism of `M` restricted to `C_1`. The
criterion then asks
for a tree product inside `M ⋊_α Z`, which is a subgroup question about the
input itself.

### 5.2 Hosts inside the BFFHZ actor Ω

- **Explicit conjugators.** For `θ ∈ Aut_M(Q)` and `tilde(θ)` (`θ` on `Q`,
  `x -> x`), `tilde(θ) ρ_q tilde(θ)^-1 = ρ_(θ(q))`. Check this on `x` and on `Q`.
  So conjugation by these elements realizes only restrictions of automorphisms
  of `Q` that fix `M` pointwise. For `A <= M` this is the identity. Only `hat(α)`
  twists `M`, and it lies outside `Ω`.
- **Point stabilizers as enlarged edges** (clause 2 of Attempt 6). For
  `f ∈ Hom_M(P, M)` we have `f ∘ ρ_q^-1 = f` iff `f(q) = 1`. Hence
  `Stab_Ω(f) ∩ ρ(Q) = ρ(ker f|_Q)`, a normal subgroup of `Q` meeting `M` trivially.
  - Point stabilizers have finitely many orbits, because pair orbits are finite.
  - But `A ∩ D_1 = C_1` with `D_1 = Stab_Ω(f)` forces `C_1` to be normal in `A`
    with `C_1 ∩ M = 1`. For `A <= M` it forces `C_1 = 1`.
  - `D_1 = Ω` gives only the mapping-torus case.

**Dies** for every partial isomorphism of subgroups of `M` that is not the
restriction of an automorphism of `M`.

### 5.3 Residually finite hosts

Suppose `A*_phi` embeds in an HNN extension `B *_psi` with finite-index edges
whose Bass--Serre action is faithful, as in
`finite-index-edge-hnn-embeds-in-fp-simple-group`. Then `B` is a vertex
stabilizer of a locally finite tree acting faithfully, so it embeds in a
profinite vertex stabilizer of `Aut(T)` and is residually finite. So `A <= B`
is residually finite. **Dies** for every non-residually-finite `A`, in
particular for every infinite finitely presented simple `A`. The in-subgroup
injectivity problem of Attempt 4 is a second obstruction.

### 5.4 A type (A) action of J *_β itself

By Attempt 5, a type (A) action of `J *_β` must have point stabilizers with
nonzero `t`-exponent. I did not look for one. The route avoids the question by
embedding `J *_β` in `E = Ω ⋊ <τ>` acting on `Hom_M(P, M)`.
- Consistency check: `π` fixes the homomorphism `f_0` that is the identity on
  `M` and kills `z_1, ..., z_m, x`. Indeed `α ∘ f_0 ∘ hat(α)^-1` is `m -> m` on
  `M` and `1` on the free letters.
- So `Stab_E(f_0)` contains `τ` and has nonzero exponent, as Attempt 5 requires.

### 5.5 Cyclic edges over a free base

Take `A = F_2 = <a, b>`, which embeds in `V`. Take `C_1 = <w>` and `C_2 = <v>`
with `w, v != 1`; cyclic subgroups of free groups have decidable membership.
These are inputs of the target, and `A*_phi = < a, b, t | t w t^-1 = v >` is a
one-relator group.

So the target implies Boone--Higman for every one-relator group of this shape.
Item (9) of Problem 5.3 in Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3,
as quoted in `one-relator-groups-satisfy-boone-higman`, asks for all
torsion-free one-relator groups, and that node is OPEN. I did not determine how
much of this subfamily is already covered, for instance by
`hyperbolic-groups-satisfy-boone-higman`.

The new claim reaches this family only through the tree-product criterion of
§5.1. For example, a free factor `F_2 <= M * F_m` preserved by `β` gives
`F_2 ⋊ Z`, a proper quotient of the HNN extension. `F_2` is freely decomposable,
so the Kurosh reduction of §5.1 does not apply. I found no `β` for which the
criterion holds with cyclic edges `<w> != F_2`, but I did not rule one out.
**This is not a dead end of a method; it is a lower bound on the difficulty of
the target.**

### 5.6 Splitting the target into realization and centralizing permanence

Lemma 4.1 gives an equivalence. Write "BH-embeddable" for "embeds in a finitely
presented simple group".

- **(R) Realization.** For every input `(A, C_1, C_2, phi)` of the target there
  are:
  - a finitely generated BH-embeddable group `X`, with `A <= X`;
  - decidable membership of `C_1` in `X`;
  - `k ∈ X` with `k c k^-1 = phi(c)` for all `c ∈ C_1`.
- **(Z) Centralizing permanence.** The target for `phi = id_(C_1)`, that is, for
  `X *_C (C × Z)` with `X` finitely generated and BH-embeddable and `C <= X`
  finitely generated with decidable membership.

**Claim: target ⟺ (R) and (Z).**
- **Target ⟹ (Z).** (Z) is a special case.
- **Target ⟹ (R).** Take `X = A*_phi` and `k = t`. `X` is BH-embeddable by the
  target.
  - Membership of `C_1` in `X` is decidable. `A` has solvable word problem, being
    a finitely generated subgroup of a finitely presented simple group
    (Kuznetsov).
  - `phi` and `phi^-1` are computable on edge elements: enumerate expressions in
    the edge generators, which terminates for elements of the edge.
  - So Britton reduction is effective. A reduced word with a stable letter is not
    in `A`. A word without one is tested for membership in `C_1` inside `A`.
- **(R) and (Z) ⟹ target.** `A*_phi <= X *_(C_1)` by Lemma 4.1. The latter is
  BH-embeddable by (Z), and a subgroup of a BH-embeddable group is BH-embeddable.

**Dies** in the sense that neither half is supplied in general. Both halves are
formally weaker than the target: (Z) is a special case and (R) is a consequence.
The hat trick of §3 supplies realization for automorphism edges of MIF bases, but
there the full conclusion is already proved. (Z) is known here only for retract
edges `C` of groups `X ∈ B_A`, by part 1 of `pbh-graph-product-closure-proof`
(Corollary 4.2). It contains the doubles
`X *_C X`: the subgroup `<X, uXu^-1>` of `X *_C (C × <u>)` is `X *_C uXu^-1`, by
Britton. So (Z) is at least amalgam permanence for doubles over decidable
edges. The necessity of decidability for (Z) is the example of Attempt 2
(`A = C_1 = C_2 = N`, `phi = id`). What this does give is a clean separation of
the twisting from the edge permanence. It was not made a node because both halves
are open and the equivalence is a short consequence of Lemma 4.1. A referee may
promote it.

## 6. What remains open

1. **An example of infinite outer order (main caveat on novelty).** The new
   content of `mif-free-product-automorphism-ascending-hnn-is-pbh` needs a
   finitely presented simple MIF group `M` with an automorphism of infinite order
   in `Out(M)`. I verified none. If every known such `M` has torsion `Out(M)`,
   the claim adds only a uniform proof of instances already covered by (T) plus
   finite-index closure. Candidates, all **unverified**:
   - **Twisted Brin--Thompson groups `SV_Γ`.** BFFHZ Remark 3.5 calls them highly
     transitive, citing BBMZa Proposition 5.4, and hence MIF when finitely
     generated and simple. A permutation `σ` of `S` normalizing `Γ` should permute
     coordinates of the Cantor space `C^S` and normalize `SV_Γ`. Two things would
     have to be checked:
     - that no power `σ^k`, `k >= 1`, induces an inner automorphism, by a
       Rubin-type uniqueness of the implementing homeomorphism;
     - that the chosen `SV_Γ` is finitely presented
       (`twisted-brin-thompson-finite-presentation-criterion`).
   - **Higman--Thompson groups.** The abstract of arXiv:1605.09302 describes
     `Aut(G_(n,r))` through transducers, but I did not read whether `Out` has
     elements of infinite order.
   - **Burger--Mozes groups, and the finitely presented commutator subgroups of
     Röver--Nekrashevych groups.** Not examined.
2. **Non-ascending edges** over a finitely presented simple MIF base, even when
   `phi` extends to an automorphism of `M`. By §5.1 this needs the `α^i(A)` to
   form a tree product inside `M`, which the construction does not supply.
3. **Mapping tori of finitely presented simple groups not known to be MIF,**
   along automorphisms of infinite outer order. A positive answer to
   `fp-simple-groups-embed-in-fp-simple-mif-groups` (BFFHZ Question 3.4) would not
   suffice by itself: the automorphism must extend to the MIF envelope. For a
   base in `B_A` and finite outer order, `G ⋊_(α) Z` has the index-`k` subgroup
   `G ⋊_(α^k) Z ≅ G × Z` (inner twist), so that case is covered.
4. **(R) and (Z) of §5.6.** In particular, centralizing permanence
   `X *_C (C × Z)` for decidable, non-retract `C`. It contains doubles
   `X *_C X`.
5. **Partial isomorphisms that extend to no automorphism of any finitely
   presented simple MIF overgroup.** Every edge the §3 construction reaches is of
   the extendable kind (Kurosh and malnormality). Deciding whether a given
   partial isomorphism extends to an automorphism of some BH-envelope is itself
   a realization problem of type (R).

**In-flight lanes not relied on.** The uncommitted artifact
`research/artifacts/outer-extensions-mif-pbh-2026-09-16.md` gives an independent
route to cases 1 and 2 of the new claim (see "What is new" in the claim). The
hole `decidable-groups-embed-in-outer-extensions-of-fp-simple-groups` was locked
by another agent during this session; I read only its statement.

**Validation.** `check.sh` exited 0 on
`research/mif-free-product-automorphism-ascending-hnn-is-pbh.md` and
`research/mif-free-product-ascending-hnn-pbh-proof.md`, against landed head
8e8413bb1 (2026-09-16, 04:24 UTC). It reported "established:
mif-free-product-automorphism-ascending-hnn-is-pbh" as unlocked by the change.
No scripts or experiments were run; every argument was done by hand.
