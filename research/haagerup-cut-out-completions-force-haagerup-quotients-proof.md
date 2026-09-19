---
rg: 2
id: haagerup-cut-out-completions-force-haagerup-quotients-proof
kind: route
title: "Proof: M = closure of rho(N) is compact open normal in the closure of rho(F), with quotient F/N; a compact M fixes a point of any affine isometric Hilbert action, so a proper cocycle descends; a compact-by-(T) closed subgroup of a Haagerup group is compact; Neretin groups act properly on a CAT(0) cube complex; the discrete case is a finite-index normal core, where Browder applies"
target: haagerup-cut-out-completions-force-haagerup-quotients
requires:
  - commensurated-cat0-witnesses-force-finite-rational-cd
  - type-f-weyl-groups-have-bounded-elementary-abelian-ranks
---

Verification tier: proposed-established. Standard inputs:
- Bekka–de la Harpe–Valette, *Kazhdan's property (T)* (BdlHV): 1.7.6 (if
  `M ⊴ D` is closed and `M` and `D/M` have (T), so does `D`; compact groups
  have (T)); 2.12.4 and 2.4 (a σ-compact group with (T) has bounded orbits
  in every affine isometric action on Hilbert space).
- Cherix–Cowling–Jolissaint–Julg–Valette, *Groups with the Haagerup
  property* (CCJJV): Haagerup means a proper continuous affine isometric
  action on a Hilbert space (for σ-compact locally compact groups); it passes
  to closed subgroups.
- Cherix–Martin–Valette (ETDS 2004) and Niblo–Reeves: a locally compact group
  acting continuously and properly on a CAT(0) cube complex (any dimension)
  is Haagerup, via the wall (`ℓ^1`) metric.
- Genevois–Lonjou–Urech, *Cremona groups over finite fields, Neretin groups,
  and non-positively curved cube complexes*, IMRN 2024 (arXiv:2110.14605):
  explicit locally compact CAT(0) cube complexes on which Neretin groups act
  properly; plane Cremona groups over finite fields are dense in Neretin
  groups.
- Izeki–Karlsson, arXiv:2404.19273 (2024): a finitely generated torsion
  group of subexponential growth acting by isometries on a
  finite-dimensional complete CAT(0) space has a fixed point.
  Norin–Osajda–Przytycki, Duke Math. J. 171 (2022): the same for
  2-dimensional CAT(0) complexes, any finitely generated torsion group.
- A `p`-group of order `p^s` has an abelian normal subgroup of order `p^a`
  with `s ≤ a(a+1)/2` (a maximal normal abelian subgroup is
  self-centralizing; Huppert, *Endliche Gruppen I*, III.7.3).

Notation: `π : F -> P = F/N`, a cut-out `(H, K, ρ)`, `F̂ = cl ρ(F)`,
`M = F̂ ∩ K`.

## Step 1: the transfer lemma

- **`ρ(F) ∩ K = ρ(N)`.** For `f ∈ F`, `ρ(f) ∈ K` iff `f ∈ N`.
- **`M = cl ρ(N)`.** `K` is compact, so closed, and `cl ρ(N) ⊆ M`.
  Conversely `M` is open in `F̂`, and `ρ(F)` is dense in `F̂`. So every open
  neighbourhood of a point of `M` inside `M` meets `ρ(F) ∩ K = ρ(N)`.
- **Normality.** `ρ(N) ⊴ ρ(F)`, so `ρ(F)` lies in
  `{g ∈ F̂ : gMg^{-1} ⊆ M}`. This set is closed because `M` is closed, so it
  is all of `F̂`. The same holds with `g^{-1}`, so `M ⊴ F̂`. `M` is compact,
  being closed in `K`, and open in `F̂`.
- **The quotient.** `F̂/M` is discrete, and the image of `ρ(F)` is dense, so
  `F -> F̂/M` is onto. Its kernel is `{f : ρ(f) ∈ M}`. This contains `N`
  and is contained in `{f : ρ(f) ∈ K} = N`. So `P ≅ F̂/M`.
- **σ-compactness.** `F̂ = ρ(F) M` (since `M` is open and `ρ(F)` dense),
  a countable union of compact sets. ∎

## Step 2: the analytic kill

**Haagerup.** Suppose `H` is Haagerup. Then `F̂` is too (closed subgroup).
Let `α` be a proper continuous affine isometric action of `F̂` on a Hilbert
space `ℋ`.
- `M` is compact, so its orbits are bounded and it has a fixed point
  (circumcentre).
- `ℋ^M = {ξ : α(m)ξ = ξ for all m ∈ M}` is a nonempty closed affine subspace.
  It is `F̂`-invariant because `M ⊴ F̂`.
- `F̂/M` acts on `ℋ^M`. For `ξ ∈ ℋ^M`, the function `g -> ‖α(g)ξ - ξ‖` is
  proper on `F̂` and constant on `M`-cosets. So it is proper on `F̂/M`.
So `P ≅ F̂/M` is Haagerup, and so is every subgroup of `P`.

**Amenability.** Closed subgroups and quotients of amenable locally compact
groups are amenable.

**Kazhdan subgroups.** Assume every closed subgroup of `H` with (T) is
compact. Let `Γ ≤ P` have (T), and `D ≤ F̂` its preimage. `D` is open in
`F̂`, hence closed in `H`. `D/M ≅ Γ` and `M` is compact, so `D` has (T)
(BdlHV 1.7.6). So `D` is compact, and `Γ = D/M` is compact and discrete,
hence finite.
- If `H` is Haagerup, a closed σ-compact subgroup `D` with (T) acts
  properly with bounded orbits, so it is compact. So the hypothesis holds.

**`U`.** `U` contains every finitely presented group, in particular
`SL_3(Z)`, which is infinite with (T) (Kazhdan). So `U` is `F/N` for no
cut-out in such an `H`. ∎

**Witnesses give cut-outs.** For a commensurated witness, let
`C = ⟨F, Σ⟩`, `G` the closure of the image of `C` in `Sym(C/Σ)` (pointwise
topology), and `K = Stab_G(Σ)`. `K` is compact open because the
`Σ`-orbits on `C/Σ` are finite. For `f ∈ F`, `ρ(f) ∈ K` iff `fΣ = Σ` iff
`f ∈ F ∩ Σ = N`. So `(G, K, ρ)` is a cut-out. For a host action
`Λ -> H` and `Σ = Λ ∩ ρ^{-1}(K)`, restrict to `F`.

## Step 3: Neretin groups and cube complexes

- Let `X` be the locally compact CAT(0) cube complex of Genevois–Lonjou–
  Urech, with its proper continuous `N_{d,k}`-action. The wall metric gives
  a conditionally negative definite function `g -> d_{ℓ^1}(x_0, g x_0)`
  (Niblo–Reeves; Cherix–Martin–Valette for locally compact groups). It is
  proper because the action is proper. So `N_{d,k}` is Haagerup, and so is
  every closed subgroup.
- A homomorphism `ρ : F -> N_{d,k}` and any compact open `K` give a
  Haagerup cut-out, and Step 2 applies. Typical `K`: the group of
  automorphisms of the rooted forest `T_{d,k}` (the "tree vertex
  stabilizer"), or any of its open subgroups.
- **Thompson-like hosts.** `V_{d,k}`, `T`, `F`, Röver's group `⟨V, G_0⟩`,
  and plane Cremona groups over finite fields all embed in Neretin groups.
  If a host `Λ` maps to `N_{d,k}` and `Σ = Λ ∩ ρ^{-1}(K)`, then
  `F ∩ Σ = F ∩ ρ^{-1}(K)`. So `F/N` is Haagerup, and it is never `U`.
- The same argument applies verbatim to any locally compact group acting
  continuously and properly on a CAT(0) cube complex. This includes
  `Aut(T)` for a locally finite tree `T`, and automorphism groups of
  locally finite right-angled buildings, whose Davis realizations are cube
  complexes.

**Why no rank or section bound is available here.** Let `O` be the compact
open group of rooted-forest automorphisms. `V_{d,k} ∩ O` is the group of
finitary automorphisms. The finite subgroups of `V_{d,k} ≤ N_{d,k}` include
every finite group (`V` contains `Sym(n)` for all `n`). So the compact
subgroups of `N_{d,k}` realize every finite group. The finite quotients
`L/(L ∩ K)` of Step 4 of the linear-kill proof are therefore unrestricted.
The bounded simple sections of `O` itself (iterated wreath products of
`Sym(d)` and `Sym(k)`) say nothing about them. Property (T) is the invariant
that survives. ∎

## Step 4: discrete completions

Assume `Λ` is torsion-free, `Σ` is of type `F`, and `G` from Step 2 is
discrete.
- `K` is compact open in a discrete group, so finite. The image of `Σ` lies
  in `K`, so the kernel `Σ_0` of `Σ -> Sym(C/Σ)` has finite index. That
  kernel is `core_C(Σ)`, which is normal in `C ⊇ F`.
- `Σ_0` is of type `F` (finite index), torsion-free, with finitely generated
  homology. `N_0 = F ∩ Σ_0 ⊴ F`, and `[N : N_0] ≤ m = [Σ : Σ_0]`.
- `F/N_0 ≅ FΣ_0/Σ_0 ≤ N_Λ(Σ_0)/Σ_0`. By Corollary 1 of
  `type-f-weyl-groups-have-bounded-elementary-abelian-ranks`, every
  elementary abelian `p`-subgroup of `F/N_0` has rank `≤ b = 2 cd Σ + c_p(Σ_0)`.
- Suppose `(Z/p)^r ≤ P = (F/N_0)/(N/N_0)`. Let `S` be a Sylow `p`-subgroup
  of its (finite) preimage in `F/N_0`. `S` maps onto `(Z/p)^r`, so
  `|S| = p^s` with `s ≥ r`. For `x ∈ S`, `x^p` lies in the kernel, a subgroup of
  `N/N_0` of order `m' = [N : N_0] ≤ m`. So `x^{pm'} = 1` and `exp S ≤ p^e`,
  where `p^e` is the `p`-part of `pm'`.
- `S` has an abelian subgroup of order `p^a` with `a(a+1)/2 ≥ s`. Its
  exponent is at most `p^e`, so it has rank at least `a/e`, hence an
  elementary abelian subgroup of rank `≥ a/e`. So
  `a/e ≤ b`, which gives `r ≤ s ≤ be(be+1)/2`.
So finite subgroups of `P` have bounded `p`-rank, and `U`, `V`, `Z/2 ≀ Z`
and `G_0` (which contains `(Z/2)^r` for all `r`) are excluded. With Step 2,
a witness for `N_U` has a non-discrete, non-Haagerup completion `G`. The
preimage `D ≤ F̂` of `SL_3(Z)` is a closed, non-compact subgroup of `G` with
(T). ∎

## Step 5: the two leftover groups

**Grigorchuk's group.** Let `(G, K, ρ)` be a cut-out through a group `G`
acting on a locally finite CAT(0) complex `X` of dimension `d` with finitely
many shapes and compact open cell stabilizers. By Steps 0–2 of
`commensurated-cat0-witnesses-force-finite-rational-cd-proof`:
- `Z = Fix(ρ(N))` is a nonempty closed convex subcomplex of the barycentric
  subdivision `X'`. So it is a complete CAT(0) space of geometric dimension
  `≤ d`, and its telescopic dimension is at most that (Caprace–Lytchak).
- `P` acts on `Z` by isometries, without inversions, with finite vertex
  stabilizers.

Suppose `P = G_0`, which is finitely generated, torsion and of intermediate
growth. By Izeki–Karlsson, `P` fixes a point `z ∈ Z`. It stabilizes the open
simplex of `X'` containing `z`, hence fixes one of its vertices. So `P` is
contained in a finite vertex stabilizer, a contradiction since `G_0` is
infinite. For `d = 2`, Norin–Osajda–Przytycki give the same conclusion for
every finitely generated infinite torsion group. The same argument applies to
every infinite finitely generated torsion group of subexponential growth
(e.g. the torsion Grigorchuk groups `G_ω`).

**`Z/2 ≀ Z`.** Put `k_0 = F_2((t))`, `k_∞ = F_2((t^{-1}))`, and
`H = Aff(k_0) × Aff(k_∞)`, with `Aff(k) = k ⋊ k^×`, a closed subgroup of
`PGL_2(k)` (the Borel subgroup modulo the centre).
- `Γ = F_2[t^{±1}] ⋊ t^Z`, embedded diagonally, is `Z/2 ≀ Z`.
- It is discrete. `F_2[t^{±1}]` is the ring of `{0, ∞}`-integers, a lattice
  in `k_0 × k_∞`. And `t^n` lies in `O_0^× × O_∞^×` only for `n = 0`.
- For a compact open `K_1 ≤ H`, `Γ ∩ K_1` is finite. Shrinking `K_1` inside
  a basis of compact open subgroups removes each of its nonidentity
  elements, giving `K` with `Γ ∩ K = 1`.
- For `ρ : F -> Γ` onto, `F ∩ ρ^{-1}(K) = ker ρ = N`.
`H` acts on `T_3 × T_3` with compact open stabilizers, and it is amenable
(solvable). So `Z/2 ≀ Z` is a cut-out in a 2-dimensional CAT(0) completion,
in characteristic-2 linear groups and in an amenable group. It satisfies
`cd_Q(Z/2 ≀ Z) ≤ 2`, the Haagerup property and amenability. No completion
invariant of the kind used by the linear, tree, CAT(0) or analytic kills can
exclude it. An obstruction must use the type `F` hypothesis on `Λ` and `Σ`.
Item 4 does this only for discrete completions. ∎

## Step 6: what is not proved

- `V` is Haagerup (Farley, 2003), so Step 2 does not exclude it. Whether some
  closed subgroup of a Neretin group has a compact open normal subgroup with
  quotient `V` is not decided.
- **Branch (b).** Q-core homology growth gives nothing. In the amalgam
  family (`commensurated-witnesses-browder-survives-linear-kill-proof`,
  Step 3), `Σ_Q = M_r` has `rk H_1 = 1 + p^r(r-1)`. A lower bound of the form
  "`H_*(Σ_Q)` carries a faithful enough `(Z/p)^r`-action" asks only for rank
  linear in `r`. A type `F` host puts no upper bound on `[Σ : Σ_Q]`, so no
  contradiction comes from growth.
- The root claim is untouched.
