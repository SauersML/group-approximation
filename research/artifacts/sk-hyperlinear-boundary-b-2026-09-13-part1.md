# sk-hyperlinear-boundary-b: the von Neumann side of S_∂ hyperlinearity (2026-09-13)

This is lane `sk-hyperlinear-boundary-b`, start (b) of `sk/ROSTER-D.md`. Written proofs, unreviewed.
- The peer lane `sk-hyperlinear-boundary-a` landed the reduction `boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el`
  (71964c981e). It shows that `S_∂(d,k)` is hyperlinear iff `EL_3(L_(F_p)(1,2))` is, where `p = char k`. That
  reduction is not repeated here.

## 0. Summary

**The question.** For a finite field `k`, `d >= 2` and `N >= 3`, is
`S_∂ = EL_N(LC(∂F_d,k) ⋊ F_d)/Z` hyperlinear? Equivalently, is `L(S_∂) ⊂ R^ω`? `S_∂` is infinite, simple, Kazhdan
and nonsofic, so a yes would give a hyperlinear nonsofic group.

**Status.** OPEN. By the peer reduction it is the binary Leavitt question in each characteristic. For `p = 2`,
`GL = EL` (`leavitt-gl-equals-el-and-perfect-unit-group`) makes it `binary-leavitt-unit-group-hyperlinear`.

**What this lane adds.**
1. A second, elementary route into `boundary-crossed-product-embeds-unitally-in-binary-leavitt`:
   `boundary-crossed-product-in-binary-leavitt-prefix-code-proof`.
   - It uses prefix codes, and the free group acts by explicit Thompson `V` units.
   - It needs no Leavitt path algebra identification and no Brownlowe–Sørensen import (§1).
2. Four firewalls for von Neumann-side routes (§2):
   - (V1) genuine tracial representations cannot obstruct;
   - (V2) the boundary ring has no tracial shadow in characteristic 0;
   - (V3) the boundary dynamics supports no tracial crossed product;
   - (V4) closure operations cannot certify hyperlinearity, because `S_∂(2,F_2)` contains a finitely presented,
     infinite, simple Kazhdan group.
3. No change to the note (§4).

## 1. The prefix-code embedding in detail

The route body has the general proof. This section gives the `d = 2` instance, as a concrete check of the covariance
step.

**Codes.**
- Letters: `a, A = a^(-1), b, B = b^(-1)`.
- Leaves: `μ_a = 11`, `μ_A = 10`, `μ_b = 01`, `μ_B = 00`.
- For each letter `x`, the three allowed successors `y ≠ x^(-1)`, in the order `a, A, b, B` with `x^(-1)` removed,
  get `ν_(x,·) = 1, 01, 00`. For example `ν_(a,a) = 1`, `ν_(a,b) = 01`, `ν_(a,B) = 00`.

**Coding.** `h(ξ) = μ_(x_1)ν_(x_1,x_2)ν_(x_2,x_3)⋯`. For instance `h(aab⋯) = 11 · 1 · 01 ⋯`, and `h(Bb⋯)` is not
defined because `Bb` is not reduced.

**The unit for `c = a`.**
- Domain code `D_a = {μ_a, μ_b, μ_B} ∪ {μ_A ν_(A,y) : y ∈ {A, b, B}} = {11, 01, 00, 101, 1001, 1000}`.
  It is complete, being `{1, 0}` refined.
- Range code `E_a = {μ_aν_(a,x) : x ∈ {a, b, B}} ∪ {μ_y : y ∈ {A, b, B}} = {111, 1101, 1100, 10, 01, 00}`.
  It is complete as well.
- `φ_a : 11 ↦ 111`, `01 ↦ 1101`, `00 ↦ 1100`, `101 ↦ 10`, `1001 ↦ 01`, `1000 ↦ 00`.
- Spot checks:
  - `ξ = b a ⋯`: `h(ξ) = 01 · ν_(b,a) ⋯`, and `φ_a` gives `1101 · ν_(b,a) ⋯ = μ_a ν_(a,b) ν_(b,a) ⋯ = h(aba⋯)`. ✓
  - `ξ = A b ⋯`: `h(ξ) = 10 · ν_(A,b) ⋯ = 10 · 01 ⋯ = 1001 ⋯`, and `φ_a` gives `01 ⋯ = h(b⋯)`. ✓ Also
    `a · Ab⋯ = b⋯`.
- `U_a = s_111 t_11 + s_1101 t_01 + s_1100 t_00 + s_10 t_101 + s_01 t_1001 + s_00 t_1000`.
  It is a permutation unit in `V ⊂ L_k(1,2)^x`.

**Consistency with K-theory.** A unital ring homomorphism `R_∂ -> L_k(1,2)` induces
`K_0(R_∂) -> K_0(L_k(1,2)) = 0`, which imposes nothing. By contrast the reverse unital map `L_k(1,2) -> R_∂` exists
exactly when `[1] = 2[1]` in `V(R_∂)`. That holds for `d = 2` (`boundary-crossed-product-carries-leavitt-family`).
For `d >= 3` only the `d`-ary family is recorded.

**What the explicit form adds.** `c_i ↦ U_(c_i)` is the classical embedding `F_d ↪ V` whose action on Cantor space is
conjugate to the boundary action. So `S_∂(d,k) ⊆ EL_N(L_k(1,2))` contains the image of
`EL_N(LC({1,2}^N,k) ⋊ F_d)` for this particular `F_d ≤ V`. All the boundary groups sit inside one ring built from
`V` and the diagonal.

## 2. Von Neumann-side firewalls

### (V1) Genuine tracial representations cannot obstruct

Let `G` be an infinite simple group. The left regular representation `λ : G -> U(L(G))` is an injective homomorphism
into a II_1 factor, with trace `δ_e`.
- Any argument of the form "every homomorphism `G -> U(M)` into a finite von Neumann algebra with faithful trace has
  property X" therefore holds for `λ`, and must be compatible with a faithful `δ_e` trace.
- So a non-hyperlinearity proof must use approximate representations. Examples: counting in finite models, stability
  or rounding of almost-homomorphisms, normalizer structure in `prod_ω M_n` that is not a genuine representation.
- **Calibration.** In `λ`, the Kazhdan projection of any infinite (T) subgroup is `0`. So the order lemma
  `U^*PU <= P` of the non-MF paper's transport argument is empty in `L(S_∂)`, which matches the failure recorded on
  the open node (Attempts, first bullet).

### (V2) No tracial shadow of the ring in characteristic 0

Let `A` be a unital ring with a Leavitt family `t_i s_j = δ_ij`, `Σ_(i≤d) s_i t_i = 1`, `d >= 2`. Let `B` be a unital
complex algebra with a linear functional `τ` satisfying `τ(xy) = τ(yx)` and `τ(1) = 1`. Then no unital ring
homomorphism `A -> B` exists.

**Proof.** `1 = τ(1) = Σ_i τ(s_i t_i) = Σ_i τ(t_i s_i) = d`.

**Consequences.**
- `LC(∂F_d, Q) ⋊ F_d` and its C*-completion `C(∂F_d) ⋊ F_d` (a purely infinite Cuntz–Krieger algebra) have no
  tracial states.
- So MF traces, quasidiagonal traces, and embeddings of the ring into `prod_ω M_n` cannot be the source of tracial
  models for the characteristic-0 boundary groups.
- Over a finite field the group `S_∂` consists of matrices over a characteristic-`p` ring, and its unitary models
  induce no ring map at all.
- Either way, a hyperlinear model of `S_∂` exists, if at all, only at the group level. There it has to live with the
  paradox `[1] = d[1]`, which is invisible to traces.

### (V3) The boundary dynamics supports no tracial crossed product

`∂F_d` carries no `F_d`-invariant Borel probability measure, for `d >= 2`.

**Proof.**
- For a letter `x`, `x · (∂F_d \ C(x^(-1))) = C(x)`. So an invariant `μ` has `μ(C(x)) + μ(C(x^(-1))) = 1`.
- Summing over the `d` pairs `{x, x^(-1)}` gives `Σ_(x ∈ Σ) μ(C(x)) = d`.
- But the `2d` cylinders partition `∂F_d`, so the sum is `1`. This contradicts `d >= 2`.

**Consequences.**
- A tracial state on `C(∂F_d) ⋊_r F_d`, or on any crossed product containing `C(∂F_d)` covariantly, restricts to an
  invariant probability measure. So there is none.
- The measure-side mechanism of the note (invariant measure ⇒ periodic towers ⇒ LEF) has no analogue.
- Any II_1 factor naturally attached to the boundary dynamics, such as a crossed product by a quasi-invariant measure
  with finite trace, would need such a measure.
- So no "Connes-embeddable crossed-product factor" argument can start from the dynamics.
- The type of the Patterson–Sullivan crossed products (type III) is recalled only and not used.

### (V4) Closure operations cannot certify it

Put `H = L_(F_2)(1,2)^x`. It is:
- infinite and simple (`binary-leavitt-unit-group-is-simple`);
- finitely presented (`leavitt-unit-group-finitely-presented`, Khanh, unreviewed import);
- Kazhdan: `H ≅ GL_3(L) = EL_3(L)` by `leavitt-gl-equals-el-and-perfect-unit-group`, and EJZ applies because `L` is
  finitely generated.

By the peer reduction (and `glAll_eq_elementary`), `H` embeds in `S_∂(2,F_2)`.

**Lemma.** Let `H` be infinite, simple, finitely presented and Kazhdan, and let `H ≤ G`. If `G` is obtained from
groups `G_i` by one of the operations below, then `H` embeds in some `G_i`.
- **(i) Extensions.** For `1 -> A -> G -> Q -> 1`, `H ∩ A` is normal in `H`. So `H ≤ A`, or `H` maps injectively
  to `Q`.
- **(ii) Amalgamated free products, HNN extensions, finite graph products.** `G` acts on a tree without inversions,
  with vertex stabilizers conjugate to the factors. (T) implies Serre's property FA (Watatani), so `H` fixes a vertex
  and lies in a conjugate of a factor. Finite graph products are iterated amalgams.
- **(iii) Directed unions.** `H` is finitely generated, so it lies in one stage.
- **(iv) Marked limits `G_i -> G`.** Write the generators of `H` as words in the marking of `G`. The subgroups of
  `G_i` generated by the same words converge to `H` as marked groups.
  - `H` is isolated (`fp-simple-groups-are-isolated`), so for large `i` they are quotients of `H`.
  - They are nontrivial because `H ≠ 1`, so they are isomorphic to `H`.

**Consequence.** Permanence of hyperlinearity under hyperlinear-by-amenable extensions, amalgams over amenable
subgroups (Brown–Dykema–Jung), directed unions or marked limits cannot produce a hyperlinear `S_∂(2,F_2)`, unless
some input group already contains `H`.
- This extends `fp-simple-groups-escape-soft-hyperlinear-permanence` (marked limits, residual amenability) by (i)
  and (ii), which use simplicity and (T).
- A certificate must be a genuine approximation of a group containing `H`, i.e. the binary Leavitt question itself.
- The existing criteria apply unchanged: `binary-leavitt-hyperlinear-iff-24k-feasible`,
  `leavitt-hyperlinearity-eighteen-relator-unitary-test`, `leavitt-unit-hs-stable-iff-nonhyperlinear`, and the
  necessary condition `thompson-v-hyperlinear`.

**Model test.** The lemma must allow real permanence examples. `G_X` (the note's group) is infinite, simple and
Kazhdan but not finitely presented, and it is a limit of the finite groups `SL_(3N)(F_2)` in the marking of its
models. (iv) fails for it exactly because the finite presentation is missing. ✓

## 3. Where start (b) stands

- **Positive side.**
  - Every von Neumann-side certificate reduces to an explicit approximation problem for `H` (for `p = 2`).
  - (V2) and (V3) remove the ring-level and dynamics-level shortcuts. (V4) removes the closure-level shortcuts.
  - There is no new route beyond the existing Leavitt criteria.
- **Negative side.**
  - An obstruction needs approximate-representation tools, by (V1).
  - The HS shadow of the one-sided compression mechanism is the open win-win
    `hyperlinear-groups-kill-rigid-compression-defects`.
  - Compression models are dead (`kazhdan-representations-have-no-hs-compression-models`, peer).
- **Sharpest next target.** The same as the binary Leavitt root. A new family of lanes on `S_∂` hyperlinearity is not
  recommended: the boundary group adds no new hyperlinearity problem in characteristic 2, and starts (a) and (b) both
  end at the Leavitt question.

## 4. Manuscript proposal

No change. The note concerns `G_X`, and `S_∂` does not appear in it. The paradox/measure contrast was already
declined by main (rev2 decisions, items 15 and 18).
