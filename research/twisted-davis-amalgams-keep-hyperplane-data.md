---
rg: 2
id: twisted-davis-amalgams-keep-hyperplane-data
kind: claim
title: Twisting one factor of a split Davis amalgam by a carrier-fixing commensurator keeps the Burger–Mozes hyperplane sub-amalgam (so non-residual finiteness and cd 3), wall twists give explicit such commensurators, and faithfulness on the tree is automatic once the X-projection is dense; density is the only X-side gate left
requires:
  - hyperplane-extensions-into-davis-lattices-are-split
---

**ESTABLISHED** (lane proof, elementary, not reviewed) for items 1–4. Item 5 states the remaining gate.

## Setting

We use the notation of `hyperplane-extensions-into-davis-lattices-are-split`:
- `X = X_{O_d}`, the hyperplane `H_0` of type `D`, its carrier `C`, and the Coxeter retraction `r`;
- the section `E` and the Davis lattices `W_F = K_0 ⋊ E(F)`;
- `U = U(Alt_{2d-1})`, whose subgroup `U^+` is simple and has trivial centralizer;
- `Γ = F_a *_{F_e} F_b`, a torsion-free edge-transitive lattice on `T' × T_d` with `pr_{T_d}` injective.

## Statement

1. **Faithfulness from density.** Let `W_1, W_2` be Davis lattices with `A = W_1 ∩ W_2` of finite
   index in both, and put `Λ = W_1 *_A W_2`.
   - If the closure `G` of `⟨W_1, W_2⟩` in `Aut(X)` contains `U^+`, then `Λ` acts faithfully on its tree.
   - The same holds whenever `G` has no nontrivial discrete normal subgroup.
   - So condition (IRR) of the split node (a core-free `A`) follows from density. It is not a
     separate gate.
2. **Twist lemma.** Let `φ ∈ Aut(X)` satisfy three conditions:
   - (i) `φ` fixes `C` pointwise;
   - (ii) `φ` commensurates `W_{F_b}`;
   - (iii) `φ` commutes with `E(F_e)`.

   Put `W_1 = W_{F_a}` and `W_2 = φ W_{F_b} φ^{-1}`. Then:
   - `A = W_1 ∩ W_2` has finite index in both;
   - `Stab_{W_1}(H_0)`, `Stab_{W_2}(H_0)` and `Stab_A(H_0)` restrict to `F_a`, `F_b` and `F_e`;
   - `Λ_φ = W_1 *_A W_2` contains `Γ`, is torsion-free and finitely presented, and has cd 3. So it is
     non-residually finite if `Γ` is.

   Every nontrivial `φ` satisfying (i) lies outside the fibred group `G_r = K ⋊ E(Aut C)`, because
   `G_r ∩ Fix(C) = 1`. Condition (iii) is also necessary for `E(F_e) ⊆ W_2`.
3. **Wall twists (explicit `φ`).** Assume `F_e ≤ W_{lk(D)}`, i.e. `F_e` acts type-preservingly on `H_0`.
   Choose types `E_1, …, E_m ∉ st(D)` that pairwise meet as sets, so that their walls never cross and
   the regions of their union of walls form a tree `T_*`. Choose also:
   - a finite-index `W'' ⊴ W_L`;
   - a function `ε` on regions with `ε(R_0) = 1`, where `R_0 ⊇ C`.

   Require that each wall of type `E_i` changes `ε` by an element of `Sym(E_i)`, the group that fixes
   `[2d-1] ∖ E_i` pointwise. Require also that `ε` is invariant under `W''` (or its `F_e`-stable
   finite-index subgroup) and under `F_e`.
   - Then the field `σ_x := ε(region of x)` defines `φ_ε` with (i)–(iii), relative to `W_L` and hence
     to every lattice commensurable with it.
4. **A necessary condition for density.** Suppose every value of `σ_φ` preserves the set `D`, as for
   twists by `Sym(D ∩ E)`. Then every element of `⟨W_1, W_2⟩` has all its local actions in
   `Stab_{Sym(2d-1)}(D)`.
   - So `⟨W_1, W_2⟩ ⊆ U(Stab(D))`, which is closed and proper, and is never dense.
   - Density therefore needs twist values that move `D`. Wall twists with `E_1 ∪ … ∪ E_m ⊇ D` supply
     them: together with the `Sym(D^c)` local actions of `E(F)`, the groups `Sym(D^c), Sym(E_1), …`
     generate `Sym(2d-1)`.
   - With even values and even `τ` they generate `Alt(2d-1)`. For example `m = 2` works for `d >= 4`.
5. **Remaining gate (DENS + N2).** Choose `ε` so that:
   - `⟨W_{F_a}, φ_ε W_{F_b} φ_ε^{-1}⟩` is dense in `U`, which gives (N1);
   - the local action of `W_1` on `W_1/A` gives a boundary-2-transitive tree closure, which is (N2).

   Then `Λ_φ` is virtually simple, and `Λ_φ^(∞)` answers Kourovka 21.46.
   - AL's local-to-global theorem needs a vertex-transitive group. Here no `W_i` is vertex-transitive,
     although `⟨W_1, W_2⟩` may be.
   - So either prove that `⟨W_1, W_2⟩` is vertex-transitive, or prove a finitely-many-orbits version
     of AL's theorem.
   - Item 3 also needs a non-residually-finite `Γ` whose edge group `F_e` is colour-preserving on `T_d`
     (`F_e ≤ W_{lk(D)}`). We have not checked that one exists. Without it, the wall twist must be made
     `E(F_e)`-equivariant in the twisted sense.

## Proof

1. **Faithfulness.** Let `N` be the kernel of `Λ` on its tree. Then `N ⊆ A ⊆ W_1`, and `pr_X` is
   injective on `W_1`, so `N' = pr_X(N)` is discrete.
   - `N'` is normalized by `⟨W_1, W_2⟩`, hence by the closure `G`, since normalizers of closed
     subgroups are closed.
   - If `G ⊇ U^+`: `N' ∩ U^+` is a closed normal subgroup of the topologically simple, non-discrete
     group `U^+`, so it is trivial. Then `[N', U^+] = 1`, and `U^+` has trivial centralizer, so `N' = 1`.
2. **Twist lemma.**
   - **Finite index.** `W_{F_a}` and `W_{F_b}` share `K_0 ⋊ E(F_e)` with finite index, and `φ`
     commensurates `W_{F_b}`. So `W_1` and `W_2` are commensurable.
   - **Stabilizers.** `Stab_{W_2}(C) = φ E(F_b) φ^{-1}`, because `φ` preserves `C`, and it restricts to
     `F_b`. An element of `E(F_a) ∩ φ E(F_b) φ^{-1}` restricts to some `f ∈ F_a ∩ F_b = F_e` and equals
     `E(f) = φ E(f) φ^{-1}` by (iii). So `Stab_A(C) = E(F_e)`.
   - **The rest.** The sub-amalgam lemma (reduction node, item 3) gives `Γ ≤ Λ_φ`. Item 2 of that node
     gives torsion-freeness, finite presentation and cd 3.
   - **Outside `G_r`.** If `k E(h)` fixes `C` pointwise, then `h = id`, and `k ∈ K` fixes `C`, so `k = 1`.
   - **Necessity of (iii).** `E(f) ∈ W_2` forces `φ^{-1} E(f) φ ∈ E(F_b)` with restriction `f`, i.e.
     `= E(f)`.
3. **Wall twists.**
   - **Compatibility.** Inside a region the field is constant. Only type-`E_i` edges cross a type-`E_i`
     wall, and across such a wall `ε(R)^{-1} ε(R') ∈ Sym(E_i) = Fix_{Aut L}(st(E_i))` pointwise.
     Indeed, fixing every `(d-1)`-subset of `E_i^c` fixes `E_i^c` pointwise.
   - **Tree of regions.** Walls of pairwise meeting types never cross, since crossing requires
     adjacent types. So the regions form a tree, and any choice of jumps is consistent.
   - **(i).** The base point `1 ∈ C ⊆ R_0` and `ε(R_0) = 1`.
   - **(ii).** The field is `W''`-periodic, so the commensurator criterion of the split node applies,
     giving `φ_ε ∈ Comm(W_L)`. With `F_e ≤ W_{lk(D)}`, the lattices `W_L`, `W_{F_a}` and `W_{F_b}` are
     commensurable, since they share `K_0 ⋊ F_e` up to finite index.
   - **(iii).** For `f ∈ F_e`, `φ f φ^{-1}` has field `ε(f R) ε(R)^{-1} = 1`, so it is type-preserving.
     It sends `1 ↦ f`, hence equals `f`.
4. **Necessary condition.** The local actions of `W_{F_a}` are `1` (on `K_0`) and `(id_D, τ)`. Those of
   `W_2` are `σ_φ(gx) σ_g(x) σ_φ(x)^{-1}`. All of them lie in `Stab(D)` when `σ_φ` does, and the cocycle
   keeps them there.
   - For the generation claim: the supports `D^c, E_1, E_2` overlap in a connected pattern, since
     `E_i ⊄ D` and `E_1 ∩ E_2 ≠ ∅`, and they cover `[2d-1]`.

## Lesson for general BH

- **Density buys faithfulness.** Once the projection of a two-factor amalgam of lattices is dense in a
  simple group with trivial centralizer, the common-normal-subgroup obstruction disappears by itself.
- **Twist what is invisible to the embedding.** The embedded input `Γ` lives on one hyperplane. So twist
  one factor by an automorphism that fixes that hyperplane's carrier and commutes with the edge group:
  - the input survives;
  - the split structure is destroyed, because no nontrivial carrier-fixing automorphism lies in the
    fibred group.
- **What a twist must do.** For density it must move the type of the carrier hyperplane. Twists that
  keep it produce a proper universal subgroup `U(Stab(D))`.
- **General principle.** Non-residual finiteness enters through a hyperplane; density and simplicity come
  from twists supported away from it. The two are independent, and each can be designed separately.
