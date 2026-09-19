# Affine decoders admit no proper cover pairs under direct finiteness (2026-09-19)

Agent: swarm-0917-w18-w18-gs-pull (stability-approximation / transplanter).
Target cone: `constant-point-sft-domains-admit-no-post-surjective-covers`.

## Setting

- `G` is any group, and `R` is a finite commutative ring. Put `V = R^k` with standard basis `e_1, ..., e_k`, and
  shift `(g.x)(h) = x(g^{-1}h)` on `V^G`. `V[G] ⊆ V^G` is the set of finitely supported configurations.
- An **R-linear automaton** is a continuous, shift-commuting, R-linear map `V^G → V^G`. An **affine automaton**
  is `F = L + b`, with `L` an R-linear automaton and `b` a fixed configuration. Since `F` commutes with the shift,
  `b = F(0)` is shift invariant, hence constant.
- For `p ∈ V^G`, `Fin_p(Y) = {y ∈ Y : y ~ p}`, where `~` means that two configurations differ in finitely many
  cells.
- `End_R` denotes the ring of R-linear automata under composition. The ring is **directly finite (DF)** when
  `ST = id` implies `TS = id`.

**Lemma 0 (matrix form).** Every R-linear automaton has the form `x ↦ xM`, where `M` is a `k × k` matrix over
`R[G]` and `(xM)_j(g) = Σ_{i,h} x_i(g h^{-1}) M_{ij}(h)`. Composition reverses the product:
`(xM)N = x(MN)`. So `End_R ≅ M_k(R[G])^op`, and `End_R` is DF iff `M_k(R[G])` is DF.

*Proof.* The rule at `e` is an R-linear map `V^S → V` for the finite memory set `S`. Such a map is given by
`k × k` matrices over `R`, one for each `s ∈ S`. Collect them into `M`. The composition law is the same
computation as `linear-proper-domain-duality-is-stable-finiteness-proof` Step 0, with `F_q` replaced by `R`.
Nothing there uses that `R` is a field. ∎

## Theorem A (one lifted point forces the full shift)

Let `X ⊆ V^G` be **any closed set**. It need not be shift invariant, linear or of finite type. Let `F = L + b` be
an affine automaton and `p ∈ X` a point with

```text
F(Fin_p(X)) ⊇ Fin_{F(p)}(V^G)          (weak post-surjectivity at the single point p; no lift constant)
```

If `End_R` is DF, then `X = V^G`, `L` is bijective and `F` is an affine automorphism.

*Proof.*
1. For `u ∈ V[G]`, `F(p + u) = F(p) + L(u)`. So the hypothesis says: for every `δ ∈ V[G]` there is `u ∈ V[G]`
   with `p + u ∈ X` and `L(u) = δ`.
2. Pick `u_i ∈ V[G]` with `L(u_i) = e_i δ_e` for `i = 1..k`, where `δ_e` is the indicator of the identity.
   Define `T(x)(h) = Σ_i Σ_g x_i(g) u_i(g^{-1}h)`, i.e. `T(x) = Σ_{g,i} x_i(g) g.u_i`.
   - For fixed `h`, only `g ∈ h·(supp u_i)^{-1}` contribute, and that set is finite. So `T` has finite memory, is
     continuous, and is R-linear.
   - `T(a.x) = a.T(x)`: substitute `g = a g'`.
   - So `T` is an R-linear automaton.
   - This is the one step that uses the module structure: `V[G]` is a **free** `R[G]`-module on the `k`
     elements `e_i δ_e`, so the `k` chosen lifts extend to a local equivariant right inverse.
3. `L T (e_i δ_g) = L(g.u_i) = g.(e_i δ_e) = e_i δ_g`. By linearity `LT = id` on `V[G]`. Both maps are
   continuous and `V[G]` is dense, so `LT = id` on `V^G`.
4. DF gives `TL = id`. So `L` is bijective with inverse `T`, and both preserve `V[G]`. Hence
   `T(V[G]) = V[G]`.
5. By injectivity of `L`, the lift in step 1 is unique: `u = T(δ)`. So `p + V[G] = p + T(V[G]) ⊆ X`.
6. `p + V[G]` is dense in `V^G` and `X` is closed, so `X = V^G`.
7. `F^{-1}(y) = T(y − b)` is an affine automaton. ∎

## Where direct finiteness comes from

**Corollary A1 (surjunctive groups).** If `G` is surjunctive, then `End_R` is DF for every finite commutative `R`
and every `k`.
- If `LT = id`, then `T` is an injective automaton over the finite alphabet `V`.
- By surjunctivity `T` is bijective, so `L = T^{-1}` and `TL = id`. ∎

**Corollary A2 (modular stable finiteness).** If `F_p[G]` is stably finite for every prime `p` dividing `|R|`,
then `End_R` is DF.
1. Write `R = Π_j R_j` with each `R_j` local (finite Artinian). Then `M_k(R[G]) = Π_j M_k(R_j[G])`, and a product
   is DF iff each factor is.
2. Fix a local `R_j` with maximal ideal `m`, `m^N = 0`, and residue field `F_q`, `q = p^r`. The ideal
   `J = M_k(m[G])` satisfies `J^N = 0`.
3. Choose an `F_p`-basis of `F_q`. Then `F_q[G]^k` is a free right `F_p[G]`-module of rank `kr`, and left
   multiplication gives a unital ring embedding `M_k(F_q[G]) → M_{kr}(F_p[G])`. A unital subring of a DF ring is
   DF, so `M_k(F_q[G])` is DF.
4. Suppose `ab = 1` in `M_k(R_j[G])`. Reduction mod `J` and step 3 give `ba ∈ 1 + J`, so `u = ba` is invertible.
   Also `u^2 = b(ab)a = u`, hence `u = 1`. ∎

By `linear-sofic-group-algebra-is-stably-finite`, A2 applies in particular to every group that is linear sofic
over every `F_p`.

## Converse: Theorem A is sharp

Suppose `ST = id ≠ TS` in `End_R`.
- `E = TS` is idempotent (`E^2 = T(ST)S = E`), and `X := T(V^G) = ker(id − E)` because `ET = T`.
- `X` is a closed, shift-invariant linear SFT containing `0`. It is cut out by the local rule `x = Ex`, and it is
  proper because `E ≠ id`.
- `(X, S|_X)` is a linear constant-point SFT cover pair. For `x ∈ X` and `z ~ S(x)`, put
  `x' = x + T(z − S(x)) ∈ X`. Then `S(x') = z`, and `x'` differs from `x` only inside `Δ(S(x), z)·Φ`, where `Φ`
  is the inverse of the memory set of `T`.

This is the ring version of the construction in `linear-proper-domain-duality-is-stable-finiteness`.

**Equivalence.** For every group `G`, finite commutative ring `R` and `k ≥ 1`, the following are equivalent.
1. `M_k(R[G])` is DF.
2. No closed `X ⊊ (R^k)^G` carries an affine automaton that is weakly post-surjective at one point of `X`.
3. No proper constant-point SFT cover pair over `(R^k)^G` has an R-linear decoder.

Theorem A gives 1 ⇒ 2. The implication 2 ⇒ 3 is immediate. The converse above gives 3 ⇒ 1.

## Class kill for the cover-pair program

**Corollary K.** Let `A` be a finite alphabet, `X ⊆ A^G` closed, and `F : X → A^G` weakly post-surjective at
some point `p ∈ X`. Every proper cover pair qualifies, constant-point or not, SFT or not. Suppose there are
bijections `π, σ : A → R^k`, with `R` a finite commutative ring, such that `σ ∘ F ∘ π^{-1}` is the restriction of
an affine automaton. If `G` is surjunctive, or `F_p[G]` is stably finite for every `p` dividing `|R|`, then
`X = A^G`.

*Proof.* Cellwise bijections preserve closedness and finite differences. So `π^G(X)` is closed, and the
conjugated map is weakly post-surjective at `π^G(p)`. Apply Theorem A with A1 or A2. ∎

- **The class.** Proper cover pairs whose decoder is affine for some independent recodings of source and target as
  a free module over a finite commutative ring. Examples are linear domains with linear decoders (already dead by
  `linear-proper-domain-duality-is-stable-finiteness`), and also every **nonlinear** domain (arrow-type,
  bounded-defect, sofic-constant) carrying a linear or affine decoder.
- **The invariant.** Affine-ness of the decoder. Nothing about the domain is used beyond closedness, and nothing
  about the lifts beyond their existence at a single point.
- **Where every member dies.** At step 2 of Theorem A: the lifts of the `k` generators `e_i δ_e` of the free
  `R[G]`-module `V[G]` assemble into a finite-memory right inverse `T`. Surjunctivity or direct finiteness then
  makes `T` onto, so the domain contains `p + V[G]`, which is dense.
- **Consequence for `constant-point-sft-domains-admit-no-post-surjective-covers`.** A counterexample to CP, or to
  CP_col, at a surjunctive group has a decoder that is non-affine under every such recoding. This applies to
  every sofic group and to the nonsofic Kun–Thom wreaths of `kun-thom-nonsofic-wreaths-are-surjunctive`, where
  CP_col is open.
- **The linear shadow of CP.** It is exactly stable finiteness of the modular group algebras (Equivalence plus A2
  and the prime-field case). So the linear shadow cannot separate CP from Kaplansky's problem.

## Where the method breaks for nonaffine decoders

Step 2 is the only step that is not formal.
- For a nonaffine `F`, the lift set over `Fin_{F(p)}(V^G)` carries no module structure. Lifts of generators
  therefore do not determine lifts of sums.
- A right inverse must be a local choice of lifts, coherent under the shift. That is exactly a section, i.e. a
  pointed pruning (open need 36774ad3 on the target node).
- Non-local choices of lifts always exist (by choice), but nothing makes them finite-memory.
- So the affine argument is the special case of PRUNE in which a free finite generating set of the lift module
  supplies the local section for free.
- Two boundary alphabets are not covered by Corollary K.
  - Non-free abelian group structures, e.g. `Z/2 × Z/4` with a decoder that is a homomorphism: lifts of
    order-2 generators need not be order-2, so step 2 fails.
  - Nonabelian group alphabets with homomorphic decoders: translated lifts need not commute.

  Both remain open, although `homomorphic-group-alphabet-ca-reduce-to-stable-finiteness` handles the analogous
  full-shift injectivity question by a socle filtration.