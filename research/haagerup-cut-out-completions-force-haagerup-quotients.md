---
rg: 2
id: haagerup-cut-out-completions-force-haagerup-quotients
kind: claim
title: "A cut-out witness makes F/N the quotient of a closed subgroup of the completion by a compact open normal subgroup, so F/N inherits the Haagerup property, amenability and the absence of infinite Kazhdan subgroups; Neretin groups act properly on CAT(0) cube complexes, so no Neretin-type (Thompson-like) completion witnesses N_U; Grigorchuk's group has no finite-dimensional CAT(0) cut-out, while Z/2 wr Z is a cut-out and passes every such test"
distinct_from:
  commensurated-cat0-witnesses-force-finite-rational-cd: That bounds cd_Q(F/N) by the dimension of a locally finite CAT(0) complex and says nothing in infinite dimension; this transfers analytic properties (Haagerup, amenability, no infinite (T) subgroup) and needs no dimension, so it reaches Neretin groups, whose cube complexes are infinite-dimensional.
  commensurated-witnesses-survive-browder-but-die-when-linear: That bounds finite-subgroup ranks for p-adic and tree cut-outs; Neretin groups contain every finite group as a compact subgroup, so no rank or section bound can hold there, and the kill here is by property (T).
  type-f-weyl-groups-have-bounded-elementary-abelian-ranks: That is the normalized (Browder) kill; item 4 here shows the discrete-completion case of a commensurated witness reduces to it.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Setting as in
`commensurated-cat0-witnesses-force-finite-rational-cd`: `F` free, `N ⊴ F`,
`P = F/N`. A **cut-out** of `N` is a triple `(H, K, ρ)`: a locally compact
group `H`, a compact open subgroup `K ≤ H`, and a homomorphism `ρ : F -> H`
with `N = F ∩ ρ^{-1}(K)`. Every commensurated witness `Σ ≤ Λ` gives one: `H`
is the relative Schlichting completion `G` of `⟨F, Σ⟩` in `Sym(⟨F,Σ⟩/Σ)`,
and `K = Stab_G(Σ)`. So does every `Σ = Λ ∩ ρ^{-1}(K)` for a continuous
action of the host.

1. **Transfer lemma.** For every cut-out, let `F̂` be the closure of `ρ(F)`
   and `M = F̂ ∩ K`. Then `M` is a compact open normal subgroup of `F̂`, and
   `ρ` induces an isomorphism `P ≅ F̂/M`. Hence `P` inherits from `H` every
   property of locally compact groups that passes to closed subgroups and to
   quotients by compact normal subgroups.
2. **Analytic kill.**
   - If `H` has the Haagerup property, so does `P`.
   - If `H` is amenable, so is `P`.
   - If every closed subgroup of `H` with property (T) is compact (true when
     `H` is Haagerup), then every subgroup of `P` with property (T) is
     finite.
   Higman's `U` contains `SL_3(Z)`, an infinite group with (T). So `N_U` has
   no cut-out in any such `H`, whatever the finiteness type of `Λ` or `Σ`,
   and with or without torsion.
3. **Neretin-type completions are dead for `N_U`.**
   - Genevois–Lonjou–Urech (IMRN 2024) construct a locally compact CAT(0)
     cube complex on which each Neretin group `N_{d,k}` acts properly and
     continuously. So `N_{d,k}` and all its closed subgroups are Haagerup.
   - So item 2 applies to every homomorphism `ρ : F -> N_{d,k}` and every
     compact open `K`. This covers hosts `Λ` built from `V_{d,k}`, `T`,
     Thompson's `F`, Röver-type groups, or plane Cremona groups over finite
     fields (which are dense in Neretin groups, by the same paper), with `Σ`
     the preimage of a tree automorphism group `Aut(T_{d,k})` or any other
     compact open subgroup.
   - The same holds for every locally compact group acting continuously and
     properly on a CAT(0) cube complex of any dimension (including infinite
     dimension), for `Aut(T)` of any locally finite tree, and for all amenable
     completions.
   - This is the class that the rank kills and the `cd_Q` kill cannot
     reach. Neretin groups contain `V_{d,k}`, hence every finite group, as
     compact subgroups, and their cube complexes are infinite-dimensional.
4. **Discrete completions reduce to Browder.** Let `Λ` be torsion-free and
   `Σ` of type `F`. If the relative Schlichting completion of a
   commensurated witness is discrete, then `Σ_0 = core_{⟨F,Σ⟩}(Σ)` has finite
   index in `Σ`. The group `F/(F ∩ Σ_0)` then lies in a type `F` Weyl group,
   and `P` is its quotient by a finite normal subgroup. So the finite
   subgroups of `P` have bounded `p`-rank for every `p`, and `U`, `V`,
   `Z/2 ≀ Z` and Grigorchuk's group are excluded.
   Together with item 2: a witness for `N_U` has a **non-discrete,
   non-Haagerup** completion `G`. `G` contains a closed non-compact subgroup
   `D` with (T): the preimage in `F̂` of `SL_3(Z) ≤ U`, which is
   compact-by-`SL_3(Z)`.
5. **The two leftover groups.**
   - **Grigorchuk's group `G_0`** has no cut-out through any locally finite
     CAT(0) complex of finite dimension `d` with finitely many shapes (the
     setting of the cited `cd_Q` claim). `P = G_0` would act there on the
     fixed set of `ρ(N)` with finite cell stabilizers. But a finitely
     generated torsion group of subexponential growth acting by isometries on
     a finite-dimensional complete CAT(0) space has a fixed point
     (Izeki–Karlsson, arXiv:2404.19273, 2024; for `d = 2` also
     Norin–Osajda–Przytycki, Duke 2022). So `G_0` would be finite. This
     input is an external theorem, taken as stated.
   - **`Z/2 ≀ Z` cannot be decided by any completion test of this kind.** It
     is a cut-out in `H = Aff(F_2((t))) × Aff(F_2((t^{-1})))`, a closed
     subgroup of a product of `GL_2` over local fields of characteristic 2,
     acting properly on `T_3 × T_3`. It is amenable, so it passes every test
     in item 2. Any obstruction to a type `F` witness for `Z/2 ≀ Z` must use
     the finiteness type of `Λ` or `Σ` (as Browder does), not the geometry
     of the completion.
6. **Not claimed.**
   - `V` is Haagerup (Farley), so item 2 does not exclude `V`. Whether `V` is
     `F̂/M` for a closed subgroup `F̂` of a Neretin group is open.
   - Branch (b), growth of the homology of Q-cores, gives no obstruction.
     The amalgam family of
     `commensurated-witnesses-survive-browder-but-die-when-linear` (item 3)
     already realizes `(Z/p)^r` with `rk H_1(Σ_Q)` of order `p^r r`. A type
     `F` host gives no upper bound on `[Σ : Σ_Q]`.
   - The root is untouched.

**Surviving shape for `N_U`.** The completion `G` must be non-discrete. It
must contain a closed subgroup with a compact open normal subgroup and
quotient `U`. It is not Haagerup, not amenable, and not linear over a
characteristic-0 local field. It has no proper action on a finite-dimensional
locally finite CAT(0) complex, and no proper action on a CAT(0) cube complex
of any dimension. The next candidates are totally disconnected groups with
non-compact Kazhdan subgroups that are neither linear nor finite-dimensional,
for example almost-automorphism groups modelled on higher-rank or Kazhdan
structures, not on trees.

Proof: route `haagerup-cut-out-completions-force-haagerup-quotients-proof`.
