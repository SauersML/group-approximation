# Out(F_n) into Aut(F_m): splitting-compatible embeddings are virtual sections

Lane `bh-out-fn-into-aut-fm`, swarm 7, 2026-09-12.

**Target.** `out-free-groups-virtually-embed-in-aut-free-groups`: for `n ≥ 3`, some
finite-index `L ≤ Out(F_n)` embeds in some `Aut(F_m)`. With PBH for `Aut(F_m)`
(BFFHZ Theorem A) and closure of PBH under subgroups and commensurability, this
gives Boone--Higman for `Out(F_n)` (route `out-fn-bh-via-virtual-embedding-in-aut-fn`).

**Outcome.** Not settled. No embedding was found and no general obstruction was
proved. What is proved (Sections 2--4) is that every construction of the natural
shape, a homomorphism into `Aut(F_n ∗ C)` that preserves a free splitting with an
`F_n` factor carrying the given outer action, is a virtual section of
`Aut(F_n) → Out(F_n)` as soon as `L` has property FA. That holds for every
finite-index `L` when `n ≥ 4`. So passing to a larger rank `m > n` gains nothing
for such constructions: they reduce to the same-rank question already recorded
on the target.

## 1. Reformulation of the target inside Out(F_(m+1))

Write `F_(m+1) = F_m ∗ ⟨t⟩`. The map `β ↦ [β ∗ id_⟨t⟩]` from `Aut(F_m)` to
`Out(F_(m+1))` is injective:
- if `β ∗ id = ι_w`, then `w` centralizes `t`, so `w ∈ ⟨t⟩`;
- `ι_(t^k)` preserves `F_m` only for `k = 0`, so `β = id`.

Its image is the set of classes having a representative that preserves `F_m` and
fixes `t`. Such a representative is unique, because `ι_u` with `u ∈ F_m` fixes `t`
only when `u = 1`. So the target is equivalent to: some finite-index `L ≤ Out(F_n)`
embeds in some `Out(F_(m+1))` with image inside the stabilizer of the pair
(`[F_m]`, `t`). In particular the image fixes the conjugacy class of a primitive
element.

The covering representations `L → Out(Φ)` (Φ characteristic of finite index; item 2
of the target's Attempts) never land in such a stabilizer. If `L` fixed the
`Φ`-conjugacy class of `φ ≠ 1`, it would fix the `F_n`-conjugacy class of `φ`. But
every finite-index subgroup of `Out(F_n)`, `n ≥ 3`, contains a power of an atoroidal
element, and atoroidal elements have no periodic nontrivial conjugacy class
(Brinkmann, GAFA 2000; existence of atoroidal fully irreducible automorphisms for
`n ≥ 3`; not re-read from source). This is a remark, not a graph claim.

## 2. Splitting-compatible homomorphisms

**Setting.** `G = A ∗ C` with `A` free of rank `n ≥ 2` and `C ≠ 1` any group.
`T` is the Bass--Serre tree: vertices `G/A ⊔ G/C`, edges `G`, edge `g` joins `gA`
and `gC`. `L ≤ Out(A)` is any subgroup, and `ρ: L → Aut(G)` is a homomorphism
such that for every `γ ∈ L`:
- `ρ(γ)` maps `A` to a conjugate of `A` and `C` to a conjugate of `C`;
- the induced outer automorphism of `A` is `γ`.

**Induced class.** If `φ(A) = bAb^{-1}`, then `ι_b^{-1}∘φ|_A ∈ Aut(A)`. Its class in
`Out(A)` does not depend on `b`, which is determined up to right multiplication by
`N_G(A) = A`. It is also unchanged when `φ` is composed with an inner automorphism
of `G` on either side (computed in Section 3, step 2).

**Statement.**
- **(a)** `ρ(L)` acts on `T` by type-preserving automorphisms, so without
  inversions.
- **(b)** If `ρ(L)` fixes a vertex of `T`, there is a homomorphism `λ: L → Aut(A)`
  with `[λ(γ)] = γ`, so `Aut(A) → Out(A)` splits over `L`.
- **(c)** If `L` has property FA, the conclusion of (b) holds.
- **(d)** Without any condition on `C`, if each `ρ(γ)` maps `A` to a conjugate
  inducing `γ`, then `L` acts on `G/A`. Any finite orbit gives a splitting over a
  finite-index subgroup of `L`.

Injectivity of `ρ` is not assumed.

## 3. Proofs

**Step 1: the two images are adjacent.** Let `φ ∈ Aut(G)` with `φ(A) = aAa^{-1}`
and `φ(C) = cCc^{-1}`. Put `u = aA`, `v = cC`, so `G_u = φ(A)`, `G_v = φ(C)`, and
`G = G_u ∗ G_v`. Types differ, so `d(u,v)` is odd. Suppose `d(u,v) ≥ 3`, and let `w`
be a vertex of type `C` strictly inside `[u,v]`. Then `G_w ≠ 1`. We show
`⟨G_u, G_v⟩ ∩ G_w = 1`, which contradicts `⟨G_u, G_v⟩ = G`.
- **Half-trees.** Let `T_v` be the component of `T − u` containing `v`, and `T'_u`
  the component of `T − v` containing `u`. The vertex `w` lies in `T_v ∩ T'_u`.
- **Ping-pong.** Edge stabilizers are trivial, so a nontrivial `g ∈ G_u` fixes
  no edge at `u` and moves `T_v` to another component of `T − u`. Hence
  `g(T_v) ⊆ T'_u \ T_v`. Likewise a nontrivial `g' ∈ G_v` gives
  `g'(T'_u) ⊆ T_v \ T'_u`.
- **Conclusion.** A reduced word `h = g_1⋯g_k` with letters alternating from
  `G_u \ 1` and `G_v \ 1` sends `w` into `T'_u \ T_v` or into `T_v \ T'_u`.
  Neither meets `T_v ∩ T'_u`, so `hw ≠ w`.

So `d(u,v) = 1`. Let `e_φ ∈ G` be the unique edge joining `u` and `v`. Then
`φ(A) = e_φ A e_φ^{-1}` and `φ(C) = e_φ C e_φ^{-1}`.

**Step 2: the tree action.** Define `φ_T` by `gA ↦ φ(g)e_φA`, `gC ↦ φ(g)e_φC` and
`g ↦ φ(g)e_φ` on edges.
- **Well defined:** `φ(A) ⊆ e_φ A e_φ^{-1}`, and the same holds for `C`.
- **Graph automorphism:** the map is incident-preserving and type-preserving,
  and `(φ^{-1})_T` inverts it.
- **Homomorphism:** `φψ(A) = φ(e_ψ) e_φ A (⋯)^{-1}`, and the edge joining the two
  images is unique, so `e_(φψ) = φ(e_ψ) e_φ`. Then
  `(φψ)_T(g) = φ(ψ(g)e_ψ)e_φ = φ_T(ψ_T(g))`.

This proves (a).

**Normalization.** Replace `ρ` by `ρ' = ι_g^{-1} ρ ι_g` for `g ∈ G`. The hypotheses
persist, and a vertex fixed by `ρ` moves by `g^{-1}`. The induced classes are
unchanged: `ρ'(γ)(A) = b'Ab'^{-1}` with `b' = g^{-1}ρ(γ)(g)b`, and
`ι_(b')^{-1} ρ'(γ)|_A = ι_b^{-1} ρ(γ)|_A` by direct substitution.

**Step 3: proof of (b).**
- **A fixed `A`-vertex.** Normalize so that `1A` is fixed. Then `e_γ ∈ A`, so
  `ρ(γ)(A) = A`, and `λ(γ) = ρ(γ)|_A` is a homomorphism of class `γ`.
- **A fixed `C`-vertex.** Normalize so that `1C` is fixed.
  - Then `e_γ ∈ C`, `ρ(γ)(C) = C`, and `ρ(γ)(A) = e_γ A e_γ^{-1}`.
  - The neighbours of `1C` are the vertices `cA` with `c ∈ C`, all distinct, so
    `e_γ` is unique in `C`.
  - Step 2 gives the exact cocycle `e_(γδ) = ρ(γ)(e_δ) e_γ`, and all three factors
    lie in `C`.
  - Put `λ(γ) = ι_(e_γ)^{-1} ∘ ρ(γ)|_A`. Then
    `λ(γ)λ(δ) = ι_(e_γ)^{-1} ι_(ρ(γ)(e_δ))^{-1} ρ(γ)ρ(δ) = ι_(ρ(γ)(e_δ)e_γ)^{-1} ρ(γδ) = λ(γδ)`
    on `A`, and `[λ(γ)] = γ` by definition.

**(c).** Property FA means every action on a tree without inversions has a global
fixed vertex (Serre). Apply it to (a) and (b).

**(d).** Choose `a_γ` with `ρ(γ)(A) = a_γ A a_γ^{-1}`; the coset `a_γA` is canonical.
- **Action.** Define `γ·gA = ρ(γ)(g)a_γA`. It is well defined as in Step 2, and
  `a_(γδ)A = ρ(γ)(a_δ)a_γA` gives `(γδ)·x = γ·(δ·x)`.
- **Section from a finite orbit.** A finite orbit is fixed pointwise by a
  finite-index `L′`. Normalizing so that `A` is fixed gives `a_γ ∈ A` and
  `ρ(γ)(A) = A` on `L′`, and restriction is a section over `L′`.

## 4. Consequences for Out(F_n)

- **Property (T).** `Aut(F_n)` has (T) for `n ≥ 4`: Nitsche for `n = 4`
  (`aut-f4-has-property-t`), Kaluba--Nowak--Ozawa for `n = 5`, and
  Kaluba--Kielak--Nowak for `n ≥ 6` (the status artifact of `aut-f4-has-property-t`).
  `Out(F_n)` is a quotient, (T) passes to finite-index subgroups, and (T) implies
  FA for countable groups (Watatani).
- **So for `n ≥ 4`:** let `L ≤ Out(F_n)` have finite index, and let
  `ρ: L → Aut(F_(n+k))` preserve the conjugacy classes of both factors of some
  free splitting `F_(n+k) = A ∗ C` with `A ≅ F_n` inducing the given outer action.
  Then `ρ` gives a section of `Aut(F_n) → Out(F_n)` over `L`. Embeddings into a
  larger rank of this shape are no easier than the same-rank virtual-section
  question.
- **What an embedding must avoid.** An embedding `L ↪ Aut(F_m)` that would bypass
  the same-rank question must preserve no free splitting with an `F_n` factor
  carrying the outer action. If it preserves only the conjugacy class of such a
  factor, `L` must act on `G/A` without finite orbits, by (d).
- **Rank 3.** Finite-index subgroups of `Out(F_3)` need not have FA, so (c) says
  nothing there for non-FA subgroups.

## 5. Other constructions examined

- **Extension by the identity on a complement.** `α ↦ α ∗ id_C` in `Aut(F_n ∗ C)`
  sends inner automorphisms `ι_x` to non-inner partial conjugations. It is
  injective on `Aut(F_n)` and not defined on `Out(F_n)`. This is the phenomenon
  BFFHZ note after their Remark 4.1.
- **Involution complements.** In `G = F_n ∗ ⟨s | s²⟩`, the automorphisms
  preserving `F_n` and sending `s` to an `F_n`-conjugate form `F_n ⋊ Aut(F_n)`.
  Modulo `Inn(G)` this is `Aut(F_n)`, via `(α,u) ↦ ι_u^{-1}α`, not `Out(F_n)`.
- **Direct products.** `[α] ↦ [α × id]` embeds `Out(F_n)` in `Out(F_n × C)`, but
  that host is not free and is not a known Boone--Higman host.
- **Rigidity theorems.** Theorems on homomorphisms from the full groups `Aut(F_n)`
  and `Out(F_n)` (Bridson--Vogtmann; Kielak) use finite subgroups and do not
  constrain torsion-free finite-index subgroups. Their statements were not re-read
  in this pass.

## 6. Free factors with torsion

**Source.** M. Carette, *Virtually splitting the map from Aut(G) to Out(G)*,
arXiv:1301.4446. Read on 2026-09-12 from the author-hosted PDF
(`perso.uclouvain.be/mathieu.carette/papers/splitaut.pdf`, 172,936 bytes). The same
file downloads with curl on MSI.

> "Corollary 3.2. Let G = G_1 ∗ H where G is finitely generated and H ≠ {1} is
> freely indecomposable with Out(H) finite. Suppose moreover that one of the
> following holds
> • either G is residually finite and H has finite center
> • or H has trivial center.
> Then the map Aut(G) → Out(G) splits virtually."

The lift fixes `H` pointwise, because `H` is an AS subgroup (Proposition 2.1 and
Section 3.3). About free groups, page 2 says the strategy "relies in many instances
on the presence of suitable finite subgroups, but is hopeless for many torsion-free
groups like orientable surface groups (as Mess' result above shows) or free
groups." So the paper gives nothing about `Aut(F_n) → Out(F_n)`.

**Remark: `Out(F_k ∗ H)` satisfies PBH for finite `H ≠ 1` and `k ≥ 1`.** Put
`G = F_k ∗ H`.
- **Virtual lift.** `G` is virtually free, so residually finite, and `H` is finite.
  By Corollary 3.2 some finite-index `O ≤ Out(G)` embeds in `Aut(G)`.
- **A characteristic free subgroup.** Let `K` be the intersection of all subgroups
  of index at most `|H|`.
  - `K` is characteristic and of finite index.
  - `K` lies in the kernel of `G → H`, the map killing `F_k`. That kernel is
    torsion-free, because every finite subgroup of `G` is conjugate into `H`.
  - So `K ≅ F_m` for some `m ≥ 2`.
- **Restriction to `K` is injective.** If `φ|_K = id`, then `g^{-1}φ(g)`
  centralizes `K` for every `g`. `C_G(K)` is normal and meets `K` in
  `Z(K) = 1`, so it is finite. Edge stabilizers in the Bass--Serre tree are
  trivial, so a nontrivial finite normal subgroup would fix exactly one vertex, and
  `G` would fix that vertex. `G` fixes no vertex, so `C_G(K) = 1` and `φ = id`.
- **Conclusion.** `O ↪ Aut(G) ↪ Aut(F_m)`, so `O` satisfies PBH
  (`aut-free-groups-satisfy-permutational-boone-higman`). Then so does `Out(G)`,
  as a finite-index overgroup (`boone-higman-type-a-class-closed-under-finite-extensions`).

**Why this does not reach Out(F_n).** Put `G = F_n ∗ H`.
- **Quotient.** `⟨⟨H⟩⟩` is the normal closure of the torsion elements, so it is
  characteristic, and `G/⟨⟨H⟩⟩ = F_n`. This gives maps `Aut(G) → Aut(F_n)` and
  `Out(G) → Out(F_n)` that commute with the quotient maps.
- **Sections transfer down.** Take a section of `Out(G) → Out(F_n)` over `L`.
  Composing it with Carette's lift and `Aut(G) → Aut(F_n)` gives a section of
  `Aut(F_n) → Out(F_n)` over a finite-index subgroup of `L`.
- **In the language of Section 2.** The lift fixes `H` pointwise, so it fixes the
  vertex `1H`. So (b) applies without FA, in every rank including `n = 3`, whenever
  the embedding preserves `[F_n]` and induces the outer action.
- **What remains.** Torsion closes the gap between Aut and Out for `Out(F_k ∗ H)`
  itself. An embedding of `L ≤ Out(F_n)` into some `Out(F_k ∗ H)` gives something
  new only if it is not a section of `Out(F_k ∗ H) → Out(F_k)` with `k = n`.

## 7. Literature

- **arXiv access.** The API at `export.arxiv.org` is unreachable from the MSI login
  node: https gives curl code 000, and http gives only a 301 redirect. The first
  query therefore returned nothing. Downloads from `https://arxiv.org/pdf/` work.
- **Carette**, arXiv:1301.4446: Section 6.
- **Surfaces.**
  - `birman-exact-sequence-does-not-virtually-split` (Chen--Salter,
    arXiv:1804.11235, Theorem A, `g ≥ 4`) is the surface analogue of the
    same-rank question.
  - Carette (page 1) attributes the Torelli version to Mess [Mes90]. The
    Chen--Salter abstract says an error in Mess's preprint was found.
  - No free-group analogue turned up in these sources.
- **Embeddings in Out.**
  - Bogopolski--Puga, *On embeddings of Out(F_n) ... into the group Out(F_m) for
    m > n*, read from the PDF, page 1: "For each n ⩾ 1 the group Out(F_n) can be
    embedded into the group Out(F_m) where m = 1 + (n − 1)k^n, and k is an
    arbitrary natural number co-prime to n − 1."
  - Their proof splits `F_n/H → Aut(F_n)/H → Out(F_n)` for a characteristic abelian
    cover `H`, then maps into `Out(H)`.
  - Marchand, arXiv:2107.11230v3 (abstract and page 2), does the same for
    `Out(F_d ∗ G_(d+1) ∗ ⋯ ∗ G_n)` with finite abelian `G_i` of order coprime to
    `n − 1`. The paper cites Bridson--Vogtmann, Cor. A, for `Out(F_n) ↪ Out(F_m)` with
    `m = r^n(n − 1) + 1`.
  - These hosts are `Out`, not `Aut`. By Section 1, landing in `Aut(F_(m−1))`
    would need the image to fix a primitive conjugacy class, which images
    containing atoroidal powers do not.

## 8. Caveats

- Sections 2--3 and the remark in Section 6 are elementary given their citations.
  No novelty is claimed.
- The (T) citations for `n ≥ 5` and Brinkmann's atoroidal theorem were not re-read
  from source in this pass. The (T) citations are the ones recorded in the status
  artifact of `aut-f4-has-property-t`.
- Carette's Corollary 3.2 was read from the author-hosted PDF. The arXiv file is
  198,682 bytes and was not compared with it.
- Nothing here is reviewed or in Lean.
