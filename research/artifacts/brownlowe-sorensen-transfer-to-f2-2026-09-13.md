# Brownlowe--Sørensen 2016 and Khanh 2026, read against Ara--Cortiñas Question 5.7 over F_2

Lane `ex3-ara-cortinas-q57`, 2026-09-13. Target: `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`.
Nothing here is reviewed.

## 0. Sources, read from PDF text
- N. Brownlowe and A. P. W. Sørensen, *L_{2,Z} ⊗ L_{2,Z} does not embed in L_{2,Z}*, arXiv:1603.03618v1
  (11 Mar 2016); J. Algebra 456 (2016) 1--22, doi:10.1016/j.jalgebra.2016.01.040. They write `a, b` for `s_0, s_1`,
  `U_V` for the image of Thompson's group `V` in the unitary group, and `U_1` for unitaries written without
  coefficients.
- H. V. Khanh, *Group algebras that do not embed into L_K(1,2)*, Res. Math. Sci. 13 (2026), Paper 72,
  doi:10.1007/s40687-026-00656-5 (published 2026-08-18). Springer PDF fetched on MSI.
- PDFs and text: `/scratch.global/sauer354/ex/ex3-ara-cortinas-q57/` (`bs1603.pdf`, `ga_springer.pdf`).

## 1. What Brownlowe--Sørensen prove (verbatim)
- **Abstract.** "We show that the tensor product L2,Z ⊗ L2,Z does not embed in L2,Z (as a unital ∗-algebra). We also
  prove a partial non-embedding result for the more general L2,R ⊗ L2,R."
- **Open status (p. 2).** "Indeed, this question is an open problem in the subject, and has attracted enough attention
  to be included on the Graph Algebra Problem Page".
- **Theorem 4.1.** "There is no unital ∗-algebraic embedding of L2,Z ⊗ L2,Z into L2,Z." **Corollary 6.2** removes
  "unital", using Proposition 6.1: all nonzero projections of `L_{2,Z}` are equivalent to 1.
- **Theorem 3.3** (any commutative unital ring `R`). "There does not exist a ∗-algebraic embedding
  φ : LR[w, w−1, z, z−1] → L2,R with φ(w), φ(z) ∈ UV."
- **Proposition 3.4.** "If u, v ∈ UV commute, then there exists a nonzero polynomial q(w, z) ∈ R[w, z] such that
  q(u, v) = 0."
  - The proof takes preimages `g, h ∈ V`. By Brin, *Higher dimensional Thompson groups* [14, Prop. 10.1], finite
    orbits have bounded length, so the proof passes to powers without finite orbits.
  - It then uses Bleak--Salazar-Díaz, *Free products in R. Thompson's group V* [11, Lemmas 2.5(3), 2.6]: components
    of support of commuting elements are equal or disjoint, and on a common component `(p_k u p_k)^(m_k) = (p_k v p_k)^(n_k)`.
  - With the component projections `p_0, ..., p_(l+1)`, the relation is `q(w,z) = (wz − z) Π_k (w^(m_k) − z^(n_k)) (z − wz)`.
- **Proposition 5.3** (any `R`). "Suppose that φ : L2,R ⊗ L2,R → L2,R is an injective, unital ∗-homomorphism. If
  u, v ∈ U(L2,R) have full spectrum then φ(u ⊗ 1) and φ(1 ⊗ v) cannot both be in UV."
- **Proposition 5.2** (field of characteristic 0). Some image of a generator is not in `span_Z(L^1_{2,K})`.
- **The integer mechanism.**
  - Lemma 2.1: if char `R = 0` then `U_V = U_1`.
  - Proposition 4.4: every unitary of `L_{2,Z}` has a reduced form with coefficients in `{−1, 1}`.
  - Proposition 4.6: `u_+ ∈ U_V`, commuting unitaries have commuting `u_+, v_+`, and relations lift.
  - Positivity of integer coefficients is used in Lemma 2.1 (eq. (2.2)) and in Lemma 4.3.
- **Their own limits.**
  - p. 14: "While we cannot see how to generalise our techniques beyond the case R = Z".
  - Example 2.2: over `Z/2Z` the zero-diagonal all-ones `4×4` matrix gives a self-adjoint unitary in `U_1 \ U_V`.

## 2. What transfers to F_2 (lead (1) of `ex2-q34-commuting-units`)
**The integer argument does not transfer.**
- Question 5.7 asks for ring homomorphisms, so the images of `c ⊗ 1` and `1 ⊗ c` are units, not unitaries. The unit
  group of `L_(F_2)(1,2)` is far larger than `V`: it contains `GL_n(F_2[c^(±1)])` through matrix units.
- Even for ∗-homomorphisms, Lemma 2.1 fails in characteristic 2 (their Example 2.2). The reduced-form argument of
  Proposition 4.4 uses integer positivity.
- So no step of the proof of Theorem 4.1 survives over `F_2`.

**Proposition 3.4 does transfer.** Its proof uses only the dynamics of `V` and the projections onto components of
support. It never uses the involution or the coefficients, and it is stated for every commutative unital `R`.

**Consequence (derived here, short, unreviewed).** Let `K` be a field, `L = L_K(1,2)`, and `f : L ⊗ L -> L` a unital
ring homomorphism. Let `u, v` be units of `L` with no nonzero polynomial relation over `K`, for example the
north--south unit `c`. Then `f(u ⊗ 1)` and `f(1 ⊗ v)` are not both in `U_V`. Moreover, no single unit `w` conjugates
both into `U_V`.
- *Proof.* Tensoring injections over a field gives `K[u^(±1)] ⊗ K[v^(±1)] ⊆ L ⊗ L`, a Laurent ring in two variables.
  `L ⊗ L` is simple, so `f` is injective. The images commute, so Proposition 3.4 gives a nonzero relation, a
  contradiction. For `w`, apply the argument to the unital map `Ad(w^(-1)) ∘ f`. ∎

**Relation to the ex2 results.**
- `leavitt-annulus-north-south-units-have-cyclic-centralizers` excludes one factor conjugate to a clean annulus unit,
  whatever the other factor is.
- The transfer above excludes both factors Thompson, with any dynamics.
- Neither covers linear units with components of both signs in the grading, and that is the case any unital map must use.

## 3. Khanh 2026
- **Abstract.** "We prove that every finitely generated subgroup of the unit group of an idempotent corner of LK(1, 2)
  has solvable word problem. It follows that, if G is a finitely presented group with unsolvable word problem, then
  K[G] is a finitely presented, countably infinite-dimensional unital K-algebra which does not embed into LK(1, 2),
  whether or not embeddings are required to preserve the identity. The resulting counterexamples answer a question of
  Brownlowe and Sørensen over every field."
- **The obstruction is computability.** An algebra whose monomial equality problem is unsolvable does not embed.
  `L ⊗ L` has a computable normal form, so this says nothing about Question 5.7.
- A text search of the PDF finds no occurrence of "tensor".
- **Open question recorded (p. 12, verbatim).** "If char K = p > 0, does there exist an injective K-algebra
  homomorphism A1(K) → LK(1, 2) which need not preserve the identity?"

## 4. Open status of Question 5.7 over fields
- **Still open over every field** as far as this check reaches:
  - Bilich--Hazrat--Nam arXiv:2512.09241v2, Question 2.8 (Dec 2025);
  - Brownlowe--Sørensen p. 2;
  - Khanh 2026, which never mentions it.
- **OpenAlex lists 8 works citing Brownlowe--Sørensen, checked by title only:**
  - Khanh 2026 (read);
  - *Monoids, dynamics and Leavitt path algebras* (2025);
  - *Étale groupoids and Steinberg algebras, a concise introduction* (2020);
  - *Tensor products of Steinberg algebras* (2019);
  - two chapters of the Abrams--Ara--Siles Molina monograph (2017);
  - Johansen--Sørensen, *The Cuntz splice does not preserve ∗-isomorphism of Leavitt path algebras over Z* (2016);
  - Brownlowe--Sørensen, *Leavitt R-algebras over countable graphs embed into L2,R* (2016).

  None of the six unread works announces an answer in its title.
- **Bound on the search.** The arXiv API was rate-limited, web search was exhausted, and the OpenAlex list of works
  citing Ara--Cortiñas was not obtained (HTTP 429).

## 5. Sharpest next targets (open, not attempted here)
1. **Extend Proposition 3.4 to one Thompson unit of infinite order and any commuting linear unit.** Work flow
   component by flow component, with the annulus theorem as the base case. This is lead (2) of `ex2-q34-commuting-units`.
   It would exclude `f(u ⊗ 1) ∈ w U_V w^(-1)` for transcendental `u`, whatever the second factor.
2. **A plane-free conjecture: `L_K(1,2)` contains no subalgebra isomorphic to `K[X,Y]`.**
   - It implies a negative answer to Question 5.7, because `s_0 ⊗ 1` and `1 ⊗ s_0` generate `K[X,Y]` in `L ⊗ L`.
   - It implies a negative answer to Khanh's question in characteristic `p`, since `x^p` and `y^p` are central and
     algebraically independent in `A_1(K)`.
   - It is stronger than `leavitt-commuting-units-are-algebraically-dependent`.
   - It holds in the locally matricial core and, by Bergman's centralizer theorem, in the free subalgebra
     `K<s_0,s_1>`. It fails in `L ⊗ L` and in `O_2 ⊇ C(T^2)`, so any proof must use finite depth.
