# Coset-local decoders force domination of gated codes on every group (2026-09-17)

Worker: swarm-0917-w4-pull-gs-2. Target cone: `bernoulli-rokhlin-entropy-maximal-for-every-group`.

## 0. Summary

`gated-diagonal-linear-deficits-force-kaplansky-failure` (Theorem 3 of
`research/artifacts/pointer-gated-linear-witness-direct-finiteness-2026-09-17.md`) bounds gated
monomial-diagonal codes when the whole ring `F_q[<E ∪ F>]` is directly finite. On a host whose group
ring is not directly finite, such as the binary Leavitt unit group, it gives only a recipe condition
(its Section 7). Its Corollary 4 then asks for a one-sided pair `a T_i = 1 != T_i a`.

This note shows that the needed directly finite ring can be *local*: the ring of a subgroup containing
one decoder, up to a coset. So the bound holds on **every** group, including non-directly-finite
hosts, for every coordinate that has one decoder of this local kind.

1. **Lemma 1 (coset projection).** Let `H <= G` be a subgroup with `F_q[H]` directly finite, and let
   `T ∈ F_q[G]`. Suppose either
   - (a) some left inverse `a` of `T` satisfies `supp a ⊆ cH` for some `c ∈ G`; or
   - (b) `T` has a left inverse and `supp T ⊆ dH` for some `d ∈ G`.

   Then `T` is a unit of `F_q[G]`, and its inverse is its unique left inverse in `F_q[G]`.
2. **Theorem 2 (unit coordinates are dominated on every group).** Let `psi` be gated
   monomial-diagonal over an arbitrary group `G`. If `T_i` is a unit of `F_q[G]`, then
   `P(d_i = 1) <= P(i ∈ I_{J_1})`. This holds in particular when some realization of the pointers
   gives a recovering combination for coordinate `i` supported in a coset of a subgroup with directly
   finite group algebra.
3. **Corollary 3 (class kill, all hosts).** A gated monomial-diagonal code with an abelian homomorphic
   pointer has `gap(psi) <= 0` on every group whenever every active coordinate satisfies Lemma 1's
   hypotheses. The class includes every group realization of the shared-pointer parity gadget whose
   decoders run inside one gadget, so the "large `K` with unit `sigma`" lead of firewall Section 8 is
   dead on every group.
4. **Corollary 4 (sharpened recipe on non-directly-finite hosts).** Suppose a witness in the class has
   `gap(psi) > gap(J)`. Then some coordinate `i` has a non-unit `T_i` with a left inverse. Moreover:
   - `F_q[<d^{-1} supp T_i>]` is not directly finite, for any `d ∈ supp T_i`;
   - for every recovering combination `a`, `F_q[<c^{-1} supp a>]` is not directly finite for any
     `c ∈ supp a`;
   - no recovering combination lives inside one shared-pointer gadget, meaning inside one coset of a
     finite stabilizer.

Setup, notation, `gap`, `d_i`, `r`, `I_j`, `T_i`, `h_{i,j}` and Lemma 2 (recovery criterion) are those
of Sections 1-3 of `research/artifacts/pointer-gated-linear-witness-direct-finiteness-2026-09-17.md`.
Theorem 1 (exact split) and Lemma 2 there hold on every incidence pattern of every group. Proposition 5
(abelian homomorphic pointers give `gap(J) <= 0`) is pattern-level.

## 1. Lemma 1: coset projection

**Lemma 1.** Let `H <= G` with `F_q[H]` directly finite, and let `T ∈ F_q[G]` have a left inverse.
If (a) some left inverse `a` has `supp a ⊆ cH`, or (b) `supp T ⊆ dH`, then `T` is a unit of `F_q[G]`
and every left inverse of `T` equals `T^{-1}`.

*Proof of (a).*
1. Write `a = c σ` with `σ ∈ F_q[H]`. From `c σ T = 1` we get `σ (T c) = 1`.
2. `F_q[G]` is a free left `F_q[H]`-module: `F_q[G] = ⊕_{t ∈ R} F_q[H] t`, where `R` is a set of
   representatives of the right cosets `Ht`, with `1 ∈ R`. Write `T c = Σ_t b_t t` with
   `b_t ∈ F_q[H]`.
3. Then `σ (T c) = Σ_t (σ b_t) t`, with `σ b_t ∈ F_q[H]`. The decomposition is unique, and `1` lies in
   the component `t = 1`. So `σ b_1 = 1` in `F_q[H]`.
4. Direct finiteness of `F_q[H]` gives `b_1 σ = 1`, so `σ` is a unit of `F_q[H] ⊆ F_q[G]`.
5. So `T c = σ^{-1} σ (T c) = σ^{-1}`, hence `T = σ^{-1} c^{-1}` and `T a = σ^{-1} c^{-1} c σ = 1`.
6. For any left inverse `a'`: `a' = a' (T a) = (a' T) a = a`. QED

*Proof of (b).*
1. Write `T = d τ` with `τ ∈ F_q[H]`, and let `a T = 1`. Then `(a d) τ = 1`.
2. Use the free right module `F_q[G] = ⊕_{t ∈ R'} t F_q[H]` over left cosets `tH`, with `1 ∈ R'`. Write
   `a d = Σ_t t b_t`. Then `(a d) τ = Σ_t t (b_t τ)`, and the component at `t = 1` gives `b_1 τ = 1`.
3. Direct finiteness gives `τ b_1 = 1`, so `τ` is a unit and `a d = τ^{-1}`.
4. So `a = τ^{-1} d^{-1}` and `T a = d τ τ^{-1} d^{-1} = 1`. Uniqueness follows as in (a), step 6.
   QED

**Hosts for `H`.**
- Every finite `H`: `F_q[H]` is finite-dimensional. If `σ b = 1`, then `x ↦ σ x` is surjective, hence
  injective. Since `σ (b σ - 1) = 0`, we get `b σ = 1`.
- Every `H` linear sofic over `F_q`, by `linear-sofic-group-algebra-is-stably-finite`.

**Remark (what is standard).** For `T ∈ F_q[H]`, a left inverse in `F_q[G]` projects to one in
`F_q[H]`. This is the usual reason direct finiteness is a local property. Lemma 1 is the coset form
of that projection, with `T` and the decoder allowed to lie in *different* cosets. That freedom is
what applies to gadget decoders, whose support sits in a coset while `T` does not.

## 2. Theorem 2: unit coordinates are dominated on every group

**Theorem 2.** Let `psi` be gated monomial-diagonal over an arbitrary countable group `G`, and let
`T_i` be a unit of `F_q[G]`. Then `P(d_i = 1) <= P(i ∈ I_{J_1})`.

*Proof.* This is Steps 1-3 of Theorem 3 of the gated-diagonal artifact, with direct finiteness of
`F_q[<E ∪ F>]` replaced by the unit hypothesis only where it is used, in Step 1.
1. By Lemma 2, `d_i = 1` iff some `a ∈ span{f h_{i,J_f} : (f, J_f) ∈ S_i}` has `a T_i = 1`.
2. Since `T_i` is a unit, `a = a T_i T_i^{-1} = T_i^{-1}`, the same fixed nonzero element for every
   pointer realization.
3. Fix `g_0 ∈ supp T_i^{-1}`. If `d_i = 1`, then `g_0 = f h_{i,j}` for some `f ∈ F` with `J_f = j` and
   `i ∈ I_j`.
4. The union bound over `j` and stationarity of `J_g` give
   `P(d_i = 1) <= Σ_{j: i ∈ I_j} P(J_1 = j) = P(i ∈ I_{J_1})`. QED

**Addendum (one local decoder suffices).** Suppose that for *some* pointer realization, coordinate
`i` has a recovering combination `a` with `supp a` in a left coset of a subgroup whose `F_q`-group
algebra is directly finite. Then Lemma 1(a) makes `T_i` a unit, and Theorem 2 bounds `P(d_i = 1)`
over all realizations, including recoveries that are not local.

## 3. Corollary 3: the class kill on every host

**Corollary 3.** Let `psi` be gated monomial-diagonal over any countable group `G`, with a pointer code
`J` that is a homomorphism for some finite abelian group structure on the pointer alphabet
(Proposition 5 of the gated-diagonal artifact). Suppose every coordinate `i` whose `T_i` is
left-invertible in `F_q[G]` satisfies hypothesis (a) or (b) of Lemma 1 for some subgroup with directly
finite `F_q`-group algebra. Then `gap(psi) <= 0`, that is `Phi >= log q`.

*Proof.*
- Coordinates with no left inverse have `d_i = 0`, by Lemma 2.
- The others are units by Lemma 1, so Theorem 2 applies to them. Summing gives `E d <= E r`.
- Theorem 1 gives `gap(psi) = gap(J) + log q (E d - E r) <= gap(J)`, and Proposition 5 gives
  `gap(J) <= 0`. QED

**Shared-pointer gadgets in groups (the firewall's Section 8 lead).**
1. **Pointer sharing gives a finite coset.** Let `P_E ⊆ E` be the pointer positions, and suppose
   codewords `f, f'` read the same pointer cells, `f P_E = f' P_E`.
   - Then `f'^{-1} f` lies in `K = {g : g P_E = P_E}`.
   - Left multiplication is free, so `K` acts freely on the finite set `P_E`. Hence `|K| <= |P_E|`,
     and every gadget of codewords sharing one pointer set lies in one left coset `cK`.
2. **Gadget decoders lie in a coset.** In the split gadgets (pointer and value coordinates disjoint,
   as in Section 5 of the gated-diagonal artifact), take a decoder `a` for coordinate `i` that uses
   only codewords of one gadget, with a constant shift `h_{i,J_f} = h` on that gadget. This covers the
   parity gadget, where `I_j = {j}` and `h = 1`, or any `J` constant on the gadget.
   - Then `supp a ⊆ cKh = (ch)(h^{-1} K h)`, a left coset of a finite subgroup.
3. **Conclusion.** By Lemma 1(a), `T_i` is a unit and every decoder of coordinate `i`, from any
   gadget, equals `T_i^{-1}`.
   - Theorem A's amplification uses `R` gadgets with *different* decoders for the same site, and it
     is exactly what disappears.
   - The value functional `T_i` is arbitrary here: full XOR, partial XOR, or a large `K` with a unit
     `sigma`. So the Section 8 lead dies on every group, whether or not `F_q[G]` is directly finite.
   - This includes the binary Leavitt unit group, which has non-directly-finite candidates but whose
     finite subgroups still have finite-dimensional algebras.

**Invariant and step.**
- **Invariant:** unit-ness of the value functional `T_i` in `F_q[G]`.
- **Step where every member dies:** Lemma 1, step 3. The coset projection onto `F_q[H]` turns one
  local decoder into a two-sided inverse, and then every decoder is the same element.

## 4. Corollary 4: what a surviving witness in the class must look like

Contrapositive of Corollary 3, on any host. Suppose `gap(psi) > gap(J)` for a gated monomial-diagonal
code. Then some coordinate `i` has `T_i` left-invertible but not a unit, and:

1. `F_q[<d^{-1} supp T_i>]` is not directly finite for every `d ∈ supp T_i`, by Lemma 1(b) with
   `H = <d^{-1} supp T_i>`. The normalized `T_i` is supported in `E`, so
   `<d^{-1} supp T_i> <= <E^{-1} E>`.
2. Every recovering combination `a` has `F_q[<c^{-1} supp a>]` not directly finite for `c ∈ supp a`, by
   Lemma 1(a). In particular `<c^{-1} supp a>` is infinite and not linear sofic over `F_q`.
3. No recovering combination uses codewords of only one shared-pointer gadget with a constant shift.
   So a survivor must decode by mixing codewords with *different* pointer sets.
4. Recoveries must be non-unique, because `T_i` is not a unit. So some pointer realizations recover
   through left inverses `a + b(1 - T_i a)` with different supports. The coupon-collector
   amplification must run across the affine space of left inverses of a one-sided unit, not across
   gadgets.

Compared with Corollary 4 of the gated-diagonal artifact:
- that result puts a one-sided pair somewhere in `F_q[F E E^{-1}]`;
- this one says both the functional and each decoder generate, after translation, subgroups whose
  algebras are not directly finite;
- it also says no decoder is local to a gadget.

## 5. Where it stops

- **Mixed-coordinate gated codes.** Arbitrary matrices `L_j`, the OPEN
  `pointer-gated-linear-codes-are-rank-dominated`, are not covered. Lemma 1 applies to one ring
  element, and a matrix version needs `M_n(F_q[H])` directly finite, where column inverses are still
  not unique.
- **Unsplit gadgets.** Codes whose pointer and value bits share coordinates are not pointer-linear,
  so Theorem 1 does not apply. The firewall's Theorem C still kills its specific pattern.
- **Nonlinear value parts.** Not touched.
- **Gottschalk.** No new implication: a surviving witness already needs a one-sided unit, which
  refutes Kaplansky and Gottschalk on the host by Seward's Corollary 4.1.
