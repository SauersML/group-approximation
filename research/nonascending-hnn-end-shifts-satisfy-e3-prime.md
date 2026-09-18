---
rg: 2
id: nonascending-hnn-end-shifts-satisfy-e3-prime
kind: claim
title: For a non-ascending multiple HNN extension Γ of a group H of type F_n in which no nontrivial element fixes a half-tree, the Bass–Serre end shift is a minimal, topologically free, quantum-rigid SFT over Γ, and F(G_V × (Γ ⋉ X_T)) is of type F_n; so E3′ holds with unit groups as complex as H
requires:
  - topologically-free-subshift-full-groups-force-quantum-rigidity
  - v-times-ample-full-groups-are-generated-by-transpositions
  - nekrashevych-symmetric-and-alternating-full-groups
  - fp-v-times-minimal-action-full-groups-have-type-a-actions
distinct_from:
  v-times-rigid-topologically-free-sft-full-groups-are-fp: that is the open gate E3′ for all rigid minimal topologically free SFTs over finitely presented groups; this proves its conclusion for the end shifts of non-ascending HNN extensions, the first family of instances whose unit groups are infinite.
  v-times-tree-boundary-full-groups-are-f-infinity: that is the case of Cayley trees (trivial vertex groups), where the Li coding has no units and the word problem is finite-state; here the vertex group H enters Li's theorem as the unit groups, so the host's word problem is that of H.
  free-sft-hosts-admit-no-finite-type-coding: that shows finite codings need contracting loops, hence isotropy; here the contracting loops are the hyperbolic elements of Γ and the isotropy sits at their attracting ends, as that node's recommendation asks.
  finite-type-e3-prime-hosts-carry-complexity-in-units: that is the general principle for finite Zappa–Szép k-graph codings (complexity equals that of the units, and the units are residually finite); this is its rank-one instance, proved in full.
  rank-one-cone-hosts-put-fw-groups-in-local-map-groups: that says FW inputs of rank-one hosts sit in local-map groups; here the local-map groups are the finite-index subgroups of H, so this family can never carry an infinite simple Kazhdan input.
---

**ESTABLISHED** (lane proof, bh-e3prime, 2026-09-18; not reviewed). The proof is in
`nonascending-hnn-end-shifts-satisfy-e3-prime-proof`. The finiteness input is X. Li, *Left regular
representations of Garside categories II*, arXiv:2110.04505v2, Example `ex:ZS` (II) with Theorem
`thm:ZS` and Remark `rem:ZS-Stab`, read at source in `$GQ/src/kep/li-garside-II-2110.04505v2.tex`.
No priority is claimed: at the C*-level, boundary crossed products of graphs of groups are
Exel–Pardo-type self-similar graph algebras (Brownlowe–Mundey–Pask–Spielberg–Thomas, 2017; recalled,
not re-read, and not used).

## Setting

- **The group.** `H` is a group of type `F_n` (`n >= 2`). `E` is a finite nonempty set of directed
  edge labels with a fixed-point-free involution `ε ↦ ε̄`. For each `ε`:
  - a subgroup `A_ε <= H` of finite index **at least 2** (non-ascending);
  - an isomorphism `θ_ε : A_ε -> A_ε̄` with `θ_ε̄ = θ_ε^(-1)`.

  `Γ = ⟨H, t_ε (ε ∈ E) | t_ε̄ = t_ε^(-1), t_ε^(-1) a t_ε = θ_ε(a) (a ∈ A_ε)⟩`, the multiple HNN
  extension. `Γ` is finitely presented.
- **The tree.** `T` is the Bass–Serre tree, with vertices `Γ/H`, base vertex `v_0 = H`, and standard
  edges `f_ε = [v_0, t_ε v_0]`, so `Stab(f_ε) = A_ε`. The edges at `v_0` are the `h f_ε` with `h`
  running over a transversal `T_ε ∋ 1` of `H/A_ε`. `T` is locally finite, and each vertex has degree
  `Σ_ε [H : A_ε] >= 2|E| >= 2`.
- **The end shift.** `A` is the finite set of edges at `v_0`. For an end `ξ` and `γ ∈ Γ`, `x_ξ(γ)` is
  the first edge of the ray from `v_0` to `γ^(-1)ξ`. Then `X_T ⊆ A^Γ` is the set of configurations
  satisfying, for all `γ`:
  - **(R1)** `x(γh) = h^(-1)·x(γ)` for `h` in a finite generating set of `H`;
  - **(R2)** `x(γ t_ε) = t_ε^(-1)·f_ε` holds exactly when `x(γ) ≠ f_ε`, for each `ε ∈ E`. Here
    `t_ε^(-1) f_ε = [t_ε^(-1)v_0, v_0]` is the edge `f_ε̄`, read backwards.

  Γ acts by the left shift, `(η·x)(γ) = x(η^(-1)γ)`.
- **(TF), the half-tree condition.** No nontrivial element of `Γ` fixes pointwise a half-tree of `T`
  (one component of `T` minus an open edge).
- **V.** `C = {0,1}^N`, and `G_V` is the groupoid of germs of prefix replacements on `C`.

## Statement

1. **SFT.** `ξ ↦ x_ξ` is a `Γ`-equivariant homeomorphism `∂T -> X_T`. So `X_T` is a subshift of
   finite type over the finitely presented group `Γ`, conjugate to `Γ ↷ ∂T`.
2. **Dynamics.** `Γ ↷ X_T` is minimal, and it is topologically free if and only if (TF) holds.
   (TF) is equivalent to a recursive condition on the unit groups (proof, Step 3). Under (TF),
   `H` is residually finite.
3. **Coding.** Let `E_T` be the finite graph with vertex set `E` and, for `ε, ε' ∈ E` and
   `h ∈ T_ε'` with `(ε', h) ≠ (ε̄, 1)`, one edge `ε -> ε'`. Let `𝔊` be the group bundle over `E`
   with fibre `A_ε̄` at `ε`, acting on `E_T` by `g·(ε', h) = (ε', h')` and
   `φ(g, (ε', h)) = θ_ε'(a)` where `g h = h' a` with `h' ∈ T_ε'`, `a ∈ A_ε'`. Then:
   - this is a pseudo-free self-similar action, so `D = C_(E_T) ⋈ 𝔊` is right cancellative;
   - under (TF), `(Γ ⋉ ∂T)|_Y` is isomorphic to Li's groupoid `(I_l(D) ⋉ ∂Ω_D)` reduced to
     `⊔_ε ∂Ω(ε)`, where `Y ⊆ ∂T` is the union of the half-tree boundaries beyond the standard edges
     `f_ε`;
   - `G_V × (Γ ⋉ ∂T)|_Y` is the same for the 2-graph `(C_2 × C_(E_T)) ⋈ 𝔊`, with `C_2` the free
     monoid on two letters.
4. **Finiteness (E3′ for X_T).** Under (TF), `F(G_V × (Γ ⋉ X_T))` is of type `F_n`, and of type
   `F_∞` if `H` is. The unit groups in Li's theorem are the finite-index subgroups `A_ε̄` of `H`.
5. **Host and rigidity.** Under (TF), `F(G_V × (Γ ⋉ X_T)) = A(G_V × (Γ ⋉ X_T))` is simple, contains
   `Γ`, and acts with type (A) on the proper nonempty clopen subsets of `C × X_T`. By the necessity
   theorem, `X_T` is quantum rigid.
6. **Complexity.** Fix finite generating sets and write `T_K(ℓ)` for the time to solve the word problem
   of `K` on words of length `ℓ`. There are constants `c, M` such that
   `T_H(ℓ) <= T_F(cℓ) + cℓ` and `T_F(ℓ) <= 2^(cℓ) (1 + T_H(M^(cℓ)))`, where `F` is the host of item 4.
   So the host's word problem is that of `H`, up to an exponential change of variables. The
   finite-state cap on earlier E3′ instances is a property of their trivial units, not of finite type.
7. **Limits.**
   - Every FA subgroup of `Γ` fixes a vertex, so it lies in a conjugate of `H`. Under (TF), `H` acts
     faithfully on the locally finite rooted tree `(T, v_0)`, so it is residually finite. So `Γ`
     contains no infinite simple Kazhdan group, and this family is not a Boone–Higman route for the
     reduced inputs.
   - Edge groups of infinite index would make `T` locally infinite, with infinite emitters, and Li's
     local finiteness would fail. That regime is gate (IE) of the master route.

## Calibration: Baumslag–Solitar groups

`H = Z`, `E = {e, ē}`, `A_e = mZ`, `A_ē = kZ`, `θ_e(mj) = kj`, with `|m|, |k| >= 2`. So `Γ = BS(m, k)`.
- (TF) holds if and only if `|m| ≠ |k|` (proof, Step 9).
- So for `|m| ≠ |k|`, `F(G_V × (BS(m,k) ⋉ ∂T))` is of type `F_∞`, simple and of type (A), and the
  end shift of `BS(m,k)` is a quantum-rigid, minimal, topologically free SFT.
- For `|m| = |k|`, `⟨a^m⟩` is normal in `Γ` (as `t^(-1) a^m t = a^(±m)`) and lies in every edge
  stabilizer, so it acts trivially on `T`, and the action is not even faithful.

The word problem here is easy, so this is a calibration, not a complexity gain. A gain needs an `H`
whose word problem exceeds every finite-state bound and which admits the structure above. That is gate
(SS-hard) of `finite-type-e3-prime-hosts-carry-complexity-in-units`; no such `H` is known to this lane.

## Lesson for general BH

**Infinite units lift the finite-state cap; finite index keeps them residually finite.** The only
finite-type instances of E3′ on main had trivial or finite units, which is why their word problem
was capped. With the vertex group `H` as unit group, Li's Zappa–Szép theorem proves E3′ for every
non-ascending HNN end shift. The host's complexity is then exactly that of `H`, so finite type is no
obstacle to complexity.

But finite-index edge groups make the tree locally finite, and the units act through the profinite
completion of that tree. So units carry only residually finite complexity, and FA inputs are pushed
out of them.

The split between finite-index and infinite-index edge groups is the same as the split between E3′
in finite type and the emitter gate (IE). A hard simple input either rides in rank at least 2, or sits
at an infinite emitter.
