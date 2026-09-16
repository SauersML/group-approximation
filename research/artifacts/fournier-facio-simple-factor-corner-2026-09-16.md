# The Fournier--Facio simple factor: a crossed-product corner and a copy of Thompson's F

Lane `swarm-fournier-facio-simple-factor-n`, 2026-09-16. Handwritten proofs, nothing run.
Supports:

- `torsion-free-lattice-embeds-in-complement-crossed-product` (Theorem 1);
- `tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce` (Theorem 4);
- `hyde-lodha-fp-simple-groups-contain-thompson-f` (Theorem 5);
- the route `fournier-facio-simple-factor-via-thompson-f` (Section 6).

Status of the new results: proved here, not independently reviewed. No novelty is
claimed for Theorem 1 or the finite-index lemmas. They are the von Neumann shadow
of the standard measure-equivalence coupling of two lattices. The point is only
that they need no freeness and no permanence theorem for sofic actions.

## 0. Sources and the ambiguity in the target

**Read from full text this session.**

- **F. Fournier-Facio**, *A torsion-free non-sofic group*, arXiv:2608.02025v2 (PDF text,
  dated August 17, 2026), Section 2, list of input groups, verbatim: "A finitely
  presented simple torsion-free group S, e.g. a Burger–Mozes [BM97] or Hyde–Lodha group
  [HL25]". The only later use of `S` is "By universality, P contains a subgroup of the
  form P_1 × P_2 × S ≤ P", where `P` contains a universal finitely presented torsion-free
  group. So **any** finitely presented simple torsion-free group is admissible.
- **J. Hyde and Y. Lodha**, *Finitely presented simple left-orderable groups in the
  landscape of Richard Thompson's groups*, arXiv:2302.04805 (Ann. Sci. ÉNS 58 (2025)
  419–432, reference [HL25] of Fournier-Facio). PDF text read in full. Used verbatim:
  - Definition 1.2 (`Γ_n ≤ Homeo+(R)`: piecewise linear with breakpoints in
    `Z[1/(n(n+1))]`, preserving that ring, commuting with `t ↦ t+1`, plus a slope
    condition (3));
  - Theorem 1.3: "For each n ≥ 2, the group Q_n = [Γ_n, Γ_n] is a finitely presented
    (and type F∞) simple group of orientation-preserving homeomorphisms of R";
  - Proposition 1.4(2): "The stabilizer of 0 in Γ_n is isomorphic to the
    Higman-Thompson group F_{η_n}", with `η_n = n(n+1)`;
  - the definition following Proposition 1.4: "F_n is the group of
    orientation-preserving piecewise linear homeomorphisms f : [0,1] → [0,1] whose
    slopes lie in {n^m | m ∈ Z} and breakpoints lie in Z[1/n]. Denote this as the
    standard action of F_n on [0,1]."
- **M. G. Brin**, Theorem 1 of arXiv:math/9705205, as imported verbatim in the
  established node `brin-plo-i-one-sided-approach-gives-a-copy-of-f`.

**The ambiguity.** The target `fournier-facio-simple-factor-not-hyperlinear` says `S` is
"a Burger--Mozes or Hyde--Lodha group". These are different problems:

- For a Burger--Mozes group (a torsion-free cocompact lattice in `Aut(T_a) × Aut(T_b)`),
  Section 3 shows that the target implies a pmp action of `F_2 × F_2` with a
  non-Connes-embeddable crossed product.
- For a Hyde--Lodha group `Q_n`, Section 4 shows `F ≤ Q_n`. So the target follows from
  `thompson-f-is-not-hyperlinear`, and any refutation would prove Thompson's `F`
  hyperlinear.

Since the construction accepts either group, Section 6 instantiates it with `S = Q_n`.

## 1. The corner embedding lemma

**Setting (CL0).**

- `H` is a locally compact second countable group.
- `K ≤ H` is a compact open subgroup.
- `Λ ≤ H` is a subgroup with `H = ΛK` and `Λ ∩ K = {1}`. Then `H = ⊔_{λ∈Λ} λK` is a
  partition into open sets. So `Λ` is countable and discrete, and every `h ∈ H` has a
  unique factorization `h = λ(h) κ(h)` with `λ(h) ∈ Λ` and `κ(h) ∈ K`. The map `h ↦ λ(h)`
  is locally constant and `h ↦ κ(h)` is continuous.
- `S ≤ H` is a lattice with `S ∩ K = {1}`. This holds automatically if `S` is
  torsion-free: `S ∩ K` is discrete and compact, hence finite, hence trivial.
- `X = H/S` carries its unique `H`-invariant Borel probability measure `μ`.
- `Λ` acts on `X` by left multiplication. Put `M = L^∞(X, μ) ⋊ Λ`, with canonical unitaries
  `v_λ` satisfying `v_λ 1_B v_λ^* = 1_{λB}`, conditional expectation
  `E(Σ a_λ v_λ) = a_1` and trace `τ = ∫ E(·) dμ`. **No freeness is assumed.**

**Theorem 1 (CL1).** Let `A = KS/S ⊂ X` and `p = 1_A ∈ M`. Then `p ≠ 0`, and there is a
unitary representation `w : S → U(pMp)` with

```text
τ(w_s) = δ_{s,1} τ(p)      for all s ∈ S.                              (CL1)
```

Hence `L(S)` embeds trace-preservingly into `pMp` with its normalized trace.

**Corollary (CL2).** If `M` is Connes-embeddable, then `S` is hyperlinear.
Contrapositively, a non-hyperlinear torsion-free lattice `S` in `H` makes the crossed
product of the complementary lattice `Λ` acting on `H/S` non-Connes-embeddable.

### 1.1 Proof of Theorem 1

**Step 1: the corner.**

- The map `K → X`, `k ↦ kS`, is injective, because `kS = k'S` gives `k^{-1}k' ∈ K ∩ S = {1}`.
  It is continuous, and `K` is compact, so it is a homeomorphism onto `A`.
- `A` is open because `K` is open, and compact, hence clopen.
- `μ` has full support: `X` is covered by countably many translates of any nonempty open
  set. So `τ(p) = μ(A) > 0`.

**Step 2: the cocycle.** For `k ∈ K` and `s ∈ S`, write `ks = λ(k,s) κ(k,s)` with
`λ(k,s) ∈ Λ` and `κ(k,s) ∈ K`. From `kst = λ(k,s) κ(k,s) t` and uniqueness of the
factorization:

```text
λ(k, st) = λ(k,s) λ(κ(k,s), t),     κ(k, st) = κ(κ(k,s), t).            (CL3)
```

In particular `k ↦ κ(k,s)` is a bijection of `K` with inverse `k' ↦ κ(k', s^{-1})`, and
`λ(κ(k,s), s^{-1}) = λ(k,s)^{-1}`.

**Step 3: the pieces.** For `s ∈ S` and `λ ∈ Λ` put

```text
A_{s,λ} = { kS : k ∈ K, λ(k,s) = λ } = image of K ∩ λ K s^{-1}.
```

- Each `A_{s,λ}` is clopen in `A`, because `λ(·, s)` is locally constant.
- For fixed `s` the `A_{s,λ}` partition `A`. They are disjoint open sets covering the
  compact set `A`, so only finitely many are nonempty.
- For `kS ∈ A_{s,λ}` one has `λ^{-1} kS = λ^{-1} ks S = κ(k,s) S ∈ A`. So
  `λ^{-1} A_{s,λ} ⊂ A`, that is `A_{s,λ} ⊂ λA`.
- By Step 2, `λ^{-1} A_{s,λ} = A_{s^{-1}, λ^{-1}}`.

**Step 4: the unitaries.** Define the finite sum

```text
u_s = Σ_λ v_{λ^{-1}} 1_{A_{s,λ}}  ∈  M.
```

- `u_s p = u_s`, because `A_{s,λ} ⊂ A`.
- `v_{λ^{-1}} 1_{A_{s,λ}} = 1_{λ^{-1} A_{s,λ}} v_{λ^{-1}}`. So `p u_s = u_s` by Step 3, and
  `u_s ∈ pMp`.
- `u_1 = v_1 1_A = p`, because `λ(k,1) = 1`.

**Step 5: multiplication.** For Borel sets `B, C` and `λ, ν ∈ Λ`,

```text
(v_{ν^{-1}} 1_C)(v_{λ^{-1}} 1_B) = v_{ν^{-1}} v_{λ^{-1}} (v_λ 1_C v_λ^*) 1_B
                                = v_{(λν)^{-1}} 1_{B ∩ λC}.
```

Hence

```text
u_s u_t = Σ_{λ,ν} v_{(λν)^{-1}} 1_{A_{t,λ} ∩ λ A_{s,ν}}.
```

- For `kS ∈ A_{t,λ}` one has `λ^{-1} kS = κ(k,t) S`. So
  `A_{t,λ} ∩ λ A_{s,ν} = { kS : λ(k,t) = λ and λ(κ(k,t), s) = ν }`.
- By (CL3), on this set `λ(k, ts) = λν`.
- For fixed `μ_0 ∈ Λ`, the sets with `λν = μ_0` partition `A_{ts, μ_0}`.

Therefore

```text
u_s u_t = u_{ts}      for all s, t ∈ S.                                  (CL4)
```

**Step 6: adjoints.** By Step 3,

```text
u_s^* = Σ_λ 1_{A_{s,λ}} v_λ = Σ_λ v_λ 1_{λ^{-1} A_{s,λ}} = Σ_λ v_λ 1_{A_{s^{-1}, λ^{-1}}} = u_{s^{-1}}.
```

With (CL4) this gives `u_s^* u_s = u_{s^{-1}} u_s = u_{s s^{-1}} = p = u_s u_s^*`. So `u_s` is
a unitary of `pMp`, and `w_s := u_{s^{-1}}` satisfies
`w_s w_t = u_{s^{-1}} u_{t^{-1}} = u_{t^{-1}s^{-1}} = w_{st}`.

**Step 7: the trace.** `E(v_g a) = E((g·a) v_g) = δ_{g,1} a` for `a ∈ L^∞(X)`, so
`τ(u_s) = μ(A_{s,1})`. Now `A_{s,1} = { kS : k ∈ K, ks ∈ K }`. If `k, ks ∈ K`, then
`s = k^{-1}(ks) ∈ K ∩ S = {1}`. So `A_{s,1} = ∅` for `s ≠ 1`, and `τ(u_1) = τ(p)`.
This is (CL1).

**Step 8: the group factor.** By (CL1) the linear map `C[S] → pMp`, `s ↦ w_s`, is a
unital *-homomorphism carrying the canonical trace of `C[S]` to the normalized trace
`τ(p)^{-1} τ`. A trace-preserving *-homomorphism of a group algebra into a tracial von
Neumann algebra extends to a normal trace-preserving embedding of `L(S)`: the GNS spaces
coincide. So `L(S) ↪ pMp`. ∎

**Proof of (CL2).** If `M` is Connes-embeddable, so is its corner `pMp` (fact CE3 below),
hence so is the subalgebra `L(S)` (CE1). By
`hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower`, `S` is hyperlinear. ∎

### 1.2 Remarks

- **Relation to measure equivalence.** `H` with Haar measure and the action
  `(λ, s)·h = λ h s^{-1}` is the standard coupling of the lattices `Λ` and `S`. The
  unitaries `u_s` implement the right action of `S` on `Λ\H ≅ K`, which is `k ↦ κ(k,s)`.
  When both actions are essentially free, `pMp` is the crossed product
  `L^∞(Λ\H) ⋊ S`, which is Furman's stable isomorphism. Theorem 1 keeps only the
  inclusion `L(S) ⊂ pMp`, and that needs no freeness.
- **Where the hypotheses enter.** `Λ ∩ K = 1` gives uniqueness of the factorization, used
  in (CL3). `S ∩ K = 1` gives both the injectivity of `K → X` and the vanishing of
  `τ(u_s)`.

## 2. Finite-index lemmas and Connes-embeddability facts

A tracial von Neumann algebra `(N, τ)` with separable predual is Connes-embeddable (CE) if
it admits a trace-preserving normal embedding into `R^ω`. The following standard facts are
used without proof. The graph already uses (CE3) in the same form, for example in
`sp4-finite-index-scalar-data-hyperlinear-covers-proof`.

- **(CE1)** A trace-preserving von Neumann subalgebra of a CE algebra is CE.
- **(CE2)** If `N` is CE, so is `M_n(N)` with the trace `tr_n ⊗ τ`.
- **(CE3)** If `N` is CE and `q ∈ N` is a nonzero projection, `qNq` with the trace
  `τ(q)^{-1} τ` is CE.
- **(CE4)** A countable group is hyperlinear iff `L(G)` is CE
  (`hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower`).

**Lemma 2 (restriction, FI1).** Let `Γ ↷ (X, μ)` be pmp and `Γ_0 ≤ Γ` of index `n`. Put
`M = L^∞(X) ⋊ Γ` and `M_0 = L^∞(X) ⋊ Γ_0 ⊂ M`. Then there is a unital, normal,
trace-preserving *-embedding `π : M → M_n(M_0)`. Hence if `M_0` is CE, so is `M`.

*Proof.*

- Choose `g_1, ..., g_n` with `Γ = ⊔_i Γ_0 g_i`, so that `Γ = ⊔_i g_i^{-1} Γ_0`.
- Let `E_0 : M → M_0` be the trace-preserving conditional expectation,
  `E_0(Σ_γ a_γ v_γ) = Σ_{γ ∈ Γ_0} a_γ v_γ`.
- **Basis identity.** For `z ∈ M`,

  ```text
  z = Σ_j v_{g_j}^* E_0(v_{g_j} z) = Σ_j E_0(z v_{g_j}^*) v_{g_j}.       (FI2)
  ```

  For `z = a v_γ` one has `v_{g_j} a v_γ = (g_j·a) v_{g_j γ}`, and this lies in `M_0` iff
  `γ ∈ g_j^{-1} Γ_0`. That holds for exactly one `j`, and then
  `v_{g_j}^* (g_j·a) v_{g_j γ} = a v_γ`.
  - Both sides of the first identity are normal and linear in `z`, so it holds on all of `M`.
  - The second identity is the adjoint of the first, applied to `z^*`.
- **Definition.** Put `π(x)_{ij} = E_0(v_{g_i} x v_{g_j}^*)`.
- **Unital.** `π(1)_{ij} = E_0(v_{g_i g_j^{-1}}) = δ_{ij}`, because `g_i g_j^{-1} ∈ Γ_0` iff
  `Γ_0 g_i = Γ_0 g_j`.
- **Adjoints.** `π(x^*)_{ij} = (π(x)_{ji})^*`.
- **Multiplicative.** By the `M_0`-bimodule property of `E_0` and (FI2),

  ```text
  Σ_j E_0(v_{g_i} x v_{g_j}^*) E_0(v_{g_j} y v_{g_k}^*)
     = E_0( Σ_j E_0(v_{g_i} x v_{g_j}^*) v_{g_j} · y v_{g_k}^* )
     = E_0(v_{g_i} x y v_{g_k}^*).
  ```

- **Trace.** `(tr_n ⊗ τ)(π(x)) = n^{-1} Σ_i τ(v_{g_i} x v_{g_i}^*) = τ(x)`.
- **Conclusion.** A trace-preserving *-homomorphism with a faithful trace is injective,
  and `π` is normal because `E_0` is. The CE consequence is (CE2) followed by (CE1). ∎

**Lemma 3 (induction, FI3).** Let `Γ_0 ≤ Γ` have index `m`, and let `Γ_0 ↷ (X, μ)` be pmp.
Let `Y = Γ ×_{Γ_0} X` be the induced pmp action. So `Y = (Γ × X)/Γ_0` with
`(γ, x)·h = (γh, h^{-1}x)`, `Γ` acts by `γ'·[γ, x] = [γ'γ, x]`, and `ν` is normalized
counting measure on `Γ/Γ_0` times `μ`. Put `N = L^∞(Y) ⋊ Γ` and `q = 1_{[e,X]}`, with
`τ(q) = 1/m`. Then `L^∞(X) ⋊ Γ_0` embeds trace-preservingly into `qNq`. Hence if `N` is CE,
so is `L^∞(X) ⋊ Γ_0`.

*Proof.*

- For `h ∈ Γ_0` and `x ∈ X`, `h·[e, x] = [h, x] = [e, hx]`. So `[e,X]` is `Γ_0`-invariant
  and `x ↦ [e,x]` intertwines the two `Γ_0`-actions.
- For `γ ∉ Γ_0`, the set `γ[e,X] = [γ,X]` is disjoint from `[e,X]`.
- For `a ∈ L^∞(X)` let `ã ∈ L^∞(Y)` be `a` transported to `[e,X]` and `0` elsewhere.
- **The map.** Define `Φ(a v_h) = ã v_h q` for `h ∈ Γ_0`. Here `v_h q = q v_h`, and
  `v_h ã v_h^* = (h·a)~`. So `Φ` is a unital *-homomorphism from the algebraic crossed
  product into `qNq`.
- **Trace.** `τ(q)^{-1} τ(ã v_h q) = m δ_{h,e} ν(ã) = δ_{h,e} ∫ a dμ`, which is the trace
  of `a v_h`.
- **Conclusion.** `Φ` is trace-preserving, so it extends to a normal trace-preserving
  embedding of `L^∞(X) ⋊ Γ_0`. The CE consequence is (CE3) followed by (CE1). ∎

**Freeness upgrade (FI4).** If a pmp action `Γ ↷ (Y, ν)` of a countably infinite group has
a non-CE crossed product, so does the free diagonal action on `Y × {0,1}^Γ` (Bernoulli
shift). The inclusion `L^∞(Y) ⋊ Γ ⊂ L^∞(Y × {0,1}^Γ) ⋊ Γ` is trace-preserving, and the
Bernoulli factor makes the action essentially free.

## 3. Lattices in products of two trees

**Theorem 4 (PT1).** Let `a, b ≥ 3`, `H = Aut(T_a) × Aut(T_b)`, and let `S ≤ H` be a
torsion-free lattice (cocompact or not). If `L^∞(Y) ⋊ (F_2 × F_2)` is CE for every pmp
action `F_2 × F_2 ↷ (Y, ν)`, then `S` is hyperlinear.

**Contrapositive (PT2).** If some torsion-free lattice in some `Aut(T_a) × Aut(T_b)` is not
hyperlinear, then some **essentially free** pmp action of `F_2 × F_2` has a
non-Connes-embeddable crossed product.

*Proof.*

1. **The complementary lattice.** Let `W_a = C_2 * ... * C_2` (`a` factors), generated by
   involutions `s_1, ..., s_a`. Its Cayley graph for these generators is the `a`-regular
   tree. Fix identifications `T_a = Cay(W_a)` and `T_b = Cay(W_b)`, so that
   `Λ = W_a × W_b ≤ H` acts simply transitively on vertices of `T_a × T_b`. This is step 1
   of `product-tree-lattices-paunescu-class-proof`.
2. **(CL0) holds.** Let `K = Stab(v_0) × Stab(w_0)` for a base vertex pair. It is compact
   open.
   - `H = ΛK`: for `h ∈ H` pick `λ ∈ Λ` with `λ(v_0, w_0) = h(v_0, w_0)`; then
     `λ^{-1}h ∈ K`.
   - `Λ ∩ K = {1}` because `Λ` acts freely on vertices.
   - `S ∩ K = {1}` because `S` is torsion-free.
3. **Corner.** By Theorem 1, `L(S) ↪ p (L^∞(H/S) ⋊ Λ) p`.
4. **Finite index in `Λ`.** Let `K_a = ker(W_a → (C_2)^a, s_i ↦ e_i)`. By step 2 of
   `product-tree-lattices-paunescu-class-proof`, `K_a` is free of some finite rank
   `r_a ≥ 2`, of index `2^a`. Put `Λ_0 = K_a × K_b`, of index `2^{a+b}` in `Λ`. By Lemma 2,
   `L^∞(H/S) ⋊ Λ` is CE if `L^∞(H/S) ⋊ Λ_0` is.
5. **Into `F_2 × F_2`.** `F_r` is isomorphic to a subgroup of index `r − 1` of `F_2`. So
   `Λ_0 ≅ F_{r_a} × F_{r_b}` is isomorphic to a finite-index subgroup `Γ_0` of
   `Γ = F_2 × F_2`. Transport the `Λ_0`-action on `H/S` to `Γ_0` and induce to `Γ`. By
   Lemma 3, `L^∞(H/S) ⋊ Λ_0` is CE if the induced crossed product `L^∞(Y) ⋊ Γ` is CE.
6. **Chain.** Under the hypothesis, `L^∞(Y) ⋊ Γ` is CE. By steps 5 and 4, so is
   `M = L^∞(H/S) ⋊ Λ`. By (CL2), `S` is hyperlinear.
7. **(PT2).** Apply (FI4) to the induced action. ∎

**Remarks.**

- **Comparison with the sofic statement.** `product-tree-lattices-in-paunescu-class-iff-f2xf2`
  proves: every action of `F_2 × F_2` is sofic iff every action of `S` is sofic. That
  argument uses measure-equivalence invariance of Păunescu's class. Theorem 4 is the
  Connes-embedding analogue of its "if" direction. It is proved by an explicit corner,
  with no invariance theorem for a class of actions.
- **The hypothesis is the only obstruction.** Theorem 4 uses the tree structure only to
  produce `Λ`, and the free-group structure only through Lemmas 2 and 3.
- **The same argument in other groups.** Let `H` be any lcsc group with a compact open
  `K` and a vertex-simply-transitive `Λ`. Then every torsion-free lattice of `H` is
  hyperlinear as soon as all crossed products of `Λ` (or of a commensurable group) are CE.
- **What the hypothesis costs.** The hypothesis of Theorem 4 does not follow from
  hyperlinearity of `F_2 × F_2`. There is no known permanence theorem for crossed products
  of a non-amenable group that is not a free product. The Brown--Dykema--Jung
  amalgamation theorem covers `F_r`, because `L^∞(Y) ⋊ F_r` is an amalgamated free product
  of amenable algebras over `L^∞(Y)`. It does not cover `F_2 × F_2`, whose splittings
  are over non-amenable subgroups such as `F_2 × 1`. This remark is standard, is not proved
  here, and is not used.

## 4. Thompson's F inside the Hyde--Lodha groups

**Theorem 5 (HF1).** For every `n ≥ 2`, the finitely presented simple group
`Q_n = [Γ_n, Γ_n]` of Hyde--Lodha contains a subgroup isomorphic to Thompson's group `F`.

**Corollary (HF2).** If `F` is not hyperlinear (respectively not sofic), then no `Q_n` is
hyperlinear (respectively sofic). Hyperlinearity and soficity pass to subgroups.

The proof builds two explicit commutators in the Higman--Thompson group `F_η` and applies
Brin's Theorem 1 to the subgroup they generate.

### 4.1 Notation

- Fix `n ≥ 2` and `η = η_n = n(n+1) ≥ 6`.
- `F_η` is the group of orientation-preserving piecewise linear homeomorphisms of `[0,1]`
  with finitely many breakpoints, all in `Z[1/η]`, and all slopes in `η^Z` (the HL
  definition quoted in Section 0).
- Maps compose on the left, `(g ∘ h)(x) = g(h(x))`, and `[g, h] = g^{-1} h^{-1} g h`.
- `supp g = {x : g(x) ≠ x}` is open, and `supp(g h g^{-1}) = g(supp h)`. Brin writes maps on
  the right. Theorem 1 of Brin does not depend on the convention: the two conventions give
  anti-isomorphic groups on the same set of maps, and a group is anti-isomorphic to itself
  via `g ↦ g^{-1}`.

### 4.2 The elements

**The basic bump.** Let `f : [0,1] → [0,1]` be the piecewise linear map with nodes
`(0,0)`, `(η^{-2}, η^{-1})`, `(1 − η^{-1}, 1 − η^{-2})`, `(1,1)`:

```text
f(x) = η x                          on [0, η^{-2}],
f(x) = x + η^{-1} − η^{-2}          on [η^{-2}, 1 − η^{-1}],
f(x) = 1 − η^{-1}(1 − x)            on [1 − η^{-1}, 1].                   (HF3)
```

- The slopes are `η, 1, η^{-1}` and the breakpoints lie in `Z[1/η]`, so `f ∈ F_η`.
- `f(x) > x` on `(0,1)`. On the three pieces, `f(x) − x` equals `(η − 1)x`,
  `η^{-1} − η^{-2}` and `(1 − η^{-1})(1 − x)`.
- So `supp f = (0,1)`.
- The inverse is

  ```text
  f^{-1}(y) = y/η                     on [0, η^{-1}],
  f^{-1}(y) = y − η^{-1} + η^{-2}     on [η^{-1}, 1 − η^{-2}],
  f^{-1}(y) = 1 − η(1 − y)            on [1 − η^{-2}, 1].
  ```

**Rescaled bumps.** For `p ∈ Z[1/η]` and `m ≥ 0` with `p + η^{-m} ≤ 1`, let `β_{p,m}` equal
`x ↦ p + η^{-m} f(η^m (x − p))` on `[p, p + η^{-m}]` and the identity elsewhere.

- Conjugating by an affine map of slope `η^m` keeps the slopes in `η^Z`.
- The breakpoints are `p`, `p + η^{-m-2}`, `p + η^{-m} − η^{-m-1}` and `p + η^{-m}`. All lie
  in `Z[1/η]`.
- So `β_{p,m} ∈ F_η` and `supp β_{p,m} = (p, p + η^{-m})`.

**The four elements.** Put

```text
u   = f ∘ f,
v_1 = β_{η^{-1}, 1},            supp v_1 = (η^{-1}, 2η^{-1}),
v_2 = β_{2η^{-1} − η^{-2}, 2},  supp v_2 = (2η^{-1} − η^{-2}, 2η^{-1}).         (HF4)
```

Since `η^{-2} < η^{-1}`, `supp v_2 ⊂ supp v_1`. Now define

```text
k_i = u^{-1} ∘ v_i ∘ u ∘ v_i^{-1} = [u, v_i^{-1}]  ∈ [F_η, F_η],      i = 1, 2,
Q   = ⟨k_1, k_2⟩ ≤ [F_η, F_η].                                          (HF5)
```

### 4.3 Supports

**Three values of `u^{-1}`.** The inverse formula gives:

- `f^{-1}(η^{-1}) = η^{-2}` and `f^{-1}(η^{-2}) = η^{-3}`, so `u^{-1}(η^{-1}) = η^{-3}`.
- `2η^{-1} ∈ [η^{-1}, 1 − η^{-2}]` because `η ≥ 6`. So `f^{-1}(2η^{-1}) = η^{-1} + η^{-2}`, which
  lies in the same piece, and `f^{-1}(η^{-1} + η^{-2}) = 2η^{-2}`. So `u^{-1}(2η^{-1}) = 2η^{-2}`.
- `f^{-1}(2η^{-1} − η^{-2}) = η^{-1}`, so `u^{-1}(2η^{-1} − η^{-2}) = f^{-1}(η^{-1}) = η^{-2}`.

**The commutators.** `u^{-1}` is an increasing homeomorphism, so by these values:

- `supp(u^{-1} v_1 u) = u^{-1}(supp v_1) = (η^{-3}, 2η^{-2})`;
- `supp(u^{-1} v_2 u) = u^{-1}(supp v_2) = (η^{-2}, 2η^{-2})`.

Both lie below `2η^{-2} < η^{-1}`. So `u^{-1} v_i u` and `v_i^{-1}` have disjoint supports. They
commute, and the support of their product is the union:

```text
supp k_1 = (η^{-3}, 2η^{-2}) ⊔ (η^{-1}, 2η^{-1}),
supp k_2 = (η^{-2}, 2η^{-2}) ⊔ (2η^{-1} − η^{-2}, 2η^{-1}).                   (HF6)
```

- **Components.** Each displayed interval is one component. It is the support of a
  conjugate of a rescaled bump, and a rescaled bump moves every point of its open support.
- **Orbitals of `Q`.** A point is fixed by `Q` iff it is fixed by `k_1` and `k_2`. So
  `supp Q = supp k_1 ∪ supp k_2 = (η^{-3}, 2η^{-2}) ⊔ (η^{-1}, 2η^{-1})`. The two intervals
  are separated because `2η^{-2} < η^{-1}`. By Brin §1 (quoted in
  `brin-plo-i-one-sided-approach-gives-a-copy-of-f`), the orbitals of `Q` are the components
  of its support. So `A = (η^{-1}, 2η^{-1})` is an orbital of `Q`.

### 4.4 Proof of Theorem 5

- **Brin's hypothesis.** By (HF6) the orbitals of `⟨k_2⟩` are `B_1 = (η^{-2}, 2η^{-2})` and
  `B_2 = (2η^{-1} − η^{-2}, 2η^{-1})`.
  - `B_2` lies in `A` and has the endpoint `2η^{-1}`. So `k_2` approaches `2η^{-1}` in `A`.
  - `B_1` does not lie in `A`, and `B_2` has left endpoint `2η^{-1} − η^{-2} > η^{-1}`. So no
    orbital of `k_2` in `A` has `η^{-1}` as an endpoint, and `k_2` does not approach `η^{-1}`
    in `A`.
- **Brin's theorem.** `Q ≤ F_η ≤ PL_o(I)`. By Brin's Theorem 1, `Q` contains a subgroup
  isomorphic to `F`.
- **Into `Q_n`.** By HL Proposition 1.4(2) there is an isomorphism
  `φ : F_η → Stab_{Γ_n}(0)`. It is the 1-periodic action: HL §3.1 says "the stabilizer of 0
  in Γ n emerges as the 1-periodic action of Fη n on R". An isomorphism maps commutators to
  commutators, so

  ```text
  φ(Q) ≤ [Stab_{Γ_n}(0), Stab_{Γ_n}(0)] ≤ [Γ_n, Γ_n] = Q_n.
  ```

- **Conclusion.** `φ(Q) ≅ Q` contains a copy of `F`. ∎

**Machine check.** `experiments/fournier-facio-simple-factor-corner-2026-09-16/check_thompson_f_commutators.py`
verifies (HF3)–(HF6) in exact rational arithmetic for `n = 2, ..., 6`: slopes, breakpoints,
the three values of `u^{-1}`, both supports, and the orbital structure used in 4.4. Its
output is saved next to it in `run-output.txt`. Brin's theorem itself is not checked.

**Remarks.**

- **The whole group.** `F ≤ F_η ≅ Stab_{Γ_n}(0) ≤ Γ_n` is immediate from Brin's theorem
  applied to any element of `F_η` supported in `(0, 1/2)`. The commutator construction is
  needed only to land inside the simple subgroup `Q_n`.
- **Relation to the finitely generated examples.** For the finitely generated groups `G_ρ`
  of arXiv:1807.06478, `hyde-lodha-groups-contain-thompson-commutator-subgroup` already
  gives `F' ≤ G_ρ`, hence `F ≤ G_ρ`. Those groups are not finitely presented. Theorem 5 is
  the statement for the finitely presented groups `Q_n`, which that node lists as unchecked.
- **Left orders.** `Q_n ≤ Homeo+(R)` is left-orderable and hence torsion-free. It is a
  legitimate input `S` for Fournier--Facio: "a finitely presented simple torsion-free group".

## 5. What this does to the target

### 5.1 Two inequivalent problems

| choice of `S` | the target implies | refuting the target implies | what the target follows from |
|---|---|---|---|
| Burger--Mozes lattice in `Aut(T_a) × Aut(T_b)` | an essentially free pmp `F_2 × F_2`-action with non-CE crossed product (PT2) | nothing new recorded | no implication recorded |
| Hyde--Lodha `Q_n` | nothing new recorded | `F` is hyperlinear (HF2) | `thompson-f-is-not-hyperlinear` (Section 6) |

- **Hyde--Lodha.** For `S = Q_n`, disproving the target is at least as hard as proving
  `thompson-f-is-hyperlinear`. Proving the target is at most as hard as
  `thompson-f-is-not-hyperlinear`, and it would itself exhibit a first non-hyperlinear
  group.
- **Burger--Mozes.** Section 4 does not transfer to this choice. `F` contains `Z ≀ Z`, which is
  solvable and not virtually abelian. A group acting properly and cocompactly on a CAT(0)
  space has only virtually abelian solvable subgroups. This is the Bridson--Haefliger
  solvable subgroup theorem, standard and not re-read this session. So `F` is not a subgroup
  of any cocompact lattice in `Aut(T_a) × Aut(T_b)`.

### 5.2 Where the natural approaches die

1. **Rigidity and compression.**
   - A lattice in `Aut(T_a) × Aut(T_b)` acts properly on a product of trees, so it has the
     Haagerup property. By `a-t-menable-groups-have-no-rigid-compression-defect`, it carries
     no rigid-pair compression defect in any ambient group. This is the mechanism behind the
     nonsoficity of the whole Fournier--Facio group, and it is absent inside `S`.
   - For `Q_n`, HL Proposition 1.4(4) says that `Q_n` does not have property (T). An infinite
     Kazhdan subgroup of `Q_n` would be an infinite left-orderable Kazhdan group. That is
     Navas's Question 3, the open root `infinite-left-orderable-kazhdan-group`.
2. **Finite and amenable approximations (positive side).**
   - `S` is infinite, simple and non-amenable. For `Q_n`, HL Proposition 1.4(4) gives
     non-abelian free subgroups. For Burger--Mozes, a lattice in the non-amenable group
     `Aut(T_a) × Aut(T_b)` is non-amenable.
   - A simple group that is residually finite or residually amenable is finite or amenable.
   - A finitely presented LEF group is residually finite.
   - So `S` is not LEF, not residually finite and not residually amenable. No quotient tower
     and no local-embedding argument gives matrix models. A proof that `S` is hyperlinear
     needs genuinely non-residual models. For `Q_n` it needs such models for `F`.
3. **The Hecke transfer runs through the wrong algebra.**
   - By (HC5) of `hecke-corner-uniform-lattice-transfers-embeddability`, every Hecke algebra
     of `Aut(T_a) × Aut(T_b)` is CE, because `W_a × W_b` is a hyperlinear uniform lattice.
     So the Hecke algebras cannot certify the target for Burger--Mozes.
   - Theorem 1 uses the same lattice `Λ = W_a × W_b` differently. It gives the algebra
     `L^∞(H/S) ⋊ Λ`, which is **not** automatically CE, and whose CE property controls `S`.
   - This is the algebra where a nonhyperlinearity certificate for a Burger--Mozes `S` must
     live: (CL2) makes it non-CE whenever `S` is nonhyperlinear.
   - The converse, whether hyperlinearity of `S` makes `L^∞(H/S) ⋊ Λ` CE, is a
     crossed-product permanence question. It is not claimed.
4. **Crossed products by free groups are not the obstacle.**
   - The graph's literature audit
     (`research/artifacts/nonhyperlinear-literature-delta-parallel-2026-08-31.md`, section
     "Manzoor's IRS is not a point mass") records that Manzoor, arXiv:2502.06697v2,
     constructs a non-CE *equivalence-relation* von Neumann algebra from a non-co-hyperlinear
     IRS on a free group.
   - The *crossed product* of a free group action is an amalgamated free product of
     hyperfinite algebras over `L^∞(Y)`, which is CE by Brown--Dykema--Jung. That is standard
     and was not re-read this session.
   - So Theorem 4 with `F_2` in place of `F_2 × F_2` would prove the hypothesis. The whole
     difficulty sits in the product `F_2 × F_2`.
   - Theorem 1 deliberately uses the crossed product, not the orbit equivalence relation,
     for exactly this reason. It needs no freeness.
5. **Whole-group attacks do not descend.** The live negative attacks on the Fournier--Facio
   group use the compression letter, commuting copies and singular near representations.
   None of these lives inside `S`, as the target's own Attempts section already records.

### 5.3 Holes this suggests, not created

- **(C1) Crossed-product embeddability for `F_2 × F_2`.** "Every pmp action of `F_2 × F_2`
  has a CE crossed product". By Theorem 4 it would make every torsion-free lattice in every
  `Aut(T_a) × Aut(T_b)` hyperlinear. With a Burger--Mozes choice of `S`, that refutes the
  target. It is the Connes-embedding sibling of `f2xf2-in-paunescu-class`.
- **Why it is not recorded.** No attack on (C1) was made in this lane, and every new hole
  needs an Attempts section. It is recorded in the lane note only.

## 6. The route through Thompson's F

**Route statement.** Instantiate the simple input of the Fournier--Facio construction as
`S = Q_2`, the Hyde--Lodha group for `n = 2`. Any `Q_n` works. If Thompson's group `F` is
not hyperlinear, then `S` is not hyperlinear. That is the target
`fournier-facio-simple-factor-not-hyperlinear` for this choice of `S`.

### 6.1 The instantiation is admissible

1. **Fournier--Facio.** Section 2 of arXiv:2608.02025v2 asks only for "a finitely
   presented simple torsion-free group S", and names Hyde--Lodha groups [HL25] as an
   example. The only later use of `S` is universality: `P` contains `P_1 × P_2 × S` (Section 0).
2. **`Q_n` qualifies.** By HL Theorem 1.3, `Q_n` is finitely presented and simple. It is
   infinite: it contains `F`, by Theorem 5. It is torsion-free, since a group of
   orientation-preserving homeomorphisms of `R` is torsion-free: a nontrivial finite-order
   increasing homeomorphism is impossible, because `g(x) > x` forces `g^k(x) > x` for all `k ≥ 1`.
3. **The skeleton node.** `fournier-facio-torsion-free-skeleton` records `S` as
   "Burger--Mozes or Hyde--Lodha". The target restates this. So `Q_n` fits the target's
   wording literally.
4. **The consumers.**
   - Grep of the two routes that require the target (`fournier-facio-nonhyperlinear-via-simple-factor`,
     `fournier-facio-gamma-not-hyperlinear-via-simple-factor`) and of the nodes they cite
     (`fournier-facio-nontrivial-quotients-contain-simple-wreath`,
     `fournier-facio-group-contains-simple-wreath-shift`,
     `fournier-facio-hyperlinear-iff-singular-near`) finds no use of Burger--Mozes structure.
     The grep searched for "Burger", "BM97", "Aut(T" and "tree".
   - They use only `π|_S` injective, the wreath heredity (W8), and heredity of hyperlinearity
     to subgroups. All three hold for any admissible `S`.

### 6.2 Proof

- Suppose `F` is not hyperlinear.
- By Theorem 5, `F ≤ Q_n`.
- Every subgroup of a hyperlinear group is hyperlinear: restrict the embedding into the
  tracial matrix ultraproduct.
- Hence `Q_n` is not hyperlinear. With `S = Q_n`, this is the target. ∎

### 6.3 Remarks

- **Scope of the route.** The route closes the target only for a Hyde--Lodha choice of `S`.
  With a Burger--Mozes choice, the relevant reduction is Theorem 4 instead, and it runs in
  the opposite logical direction: it is a consequence of the target, not a proof of it.
- **Contrapositive form.** A refutation of the target for `S = Q_n` would prove
  `thompson-f-is-hyperlinear`. This is the same implication, read backwards. No reverse
  implication is known: a hyperlinear `F` would not make `Q_n` hyperlinear.
- **Other choices of `S`.** A proof that the simple factor can be hyperlinear should pick a
  Burger--Mozes `S` and attack (C1).
- **Soficity.** The same argument gives that `Q_n` is not sofic if `F` is not sofic.
  So a Hyde--Lodha choice makes the simple factor's approximation properties dominate those
  of `F` in both metrics.
