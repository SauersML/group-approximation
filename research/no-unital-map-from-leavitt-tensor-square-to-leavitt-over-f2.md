---
rg: 2
id: no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2
kind: claim
title: There is no unital homomorphism from L_(F_2)(1,2) ⊗ L_(F_2)(1,2) to L_(F_2)(1,2)
distinct_from:
  leavitt-tensor-powers-are-left-coherent: that is coherence of tensor powers, whose Attempts record the embedding question as open; this is the embedding question itself in characteristic two, as a target for implications.
  leavitt-commuting-units-are-algebraically-dependent: that is a statement about pairs of commuting units; this is the tensor-square nonembedding that it implies.
artifacts:
  - research/artifacts/brownlowe-sorensen-transfer-to-f2-2026-09-13.md
root: true
---

**Root (2026-09-13, ex-steward).** The case `k = F_2` of Ara--Cortiñas, *Tensor products of Leavitt path algebras*, arXiv:1108.0352v3, p. 8, Question 5.7, quoted below.

**OPEN.** Let `L = L_(F_2)(1,2)`. No unital ring homomorphism `L ⊗_(F_2) L -> L` exists. Since `L ⊗ L` is
simple, the same statement holds for unital embeddings.

**Source of the question.** P. Ara and G. Cortiñas, *Tensor products of Leavitt path algebras*,
arXiv:1108.0352v3, page 8, checked against the PDF on 2026-09-13. The paper works over a field `k`.
- The question reads verbatim: "Question 5.7. Is there a unital homomorphism φ: L_2 ⊗ L_2 → L_2?"
- The paper then observes: "to build a unital homomorphism φ: L_2 ⊗ L_2 → L_2, it is enough to exhibit a
  non-zero homomorphism ψ: L_2 ⊗ L_2 → L_2, because eL_2e ≅ L_2 for every non-zero idempotent e in L_2."

So this claim is the case `k = F_2`, and it is equivalent to the absence of any nonzero homomorphism
`L ⊗ L -> L`.

**Status (bounded check, 2026-09-13, lane `ex2-q34-commuting-units`).** The question is recorded as open over
fields in B. Bilich, R. Hazrat and T. G. Nam, *Embedding k-algebras into Leavitt algebra L_k(1,2)*,
arXiv:2512.09241v2 (22 Dec 2025), page 6, Question 2.8, read from the PDF:
- "It is not yet known whether Kumjian-Pask algebras can be embedded into L_k(1,2)."
- "If affirmative, this in particular answers the question whether L_k(1,2) ⊗_k L_k(1,2) embeds into
  L_k(1,2) as L_k(1,2) ⊗_k L_k(1,2) can be realized as the Kumjian-Pask algebra of the 2-graph".
- N. Brownlowe and A. P. W. Sørensen, *L_{2,Z} ⊗ L_{2,Z} does not embed in L_{2,Z}*, arXiv:1603.03618v1, J. Algebra
  456 (2016) 1–22, read from the PDF on 2026-09-13 by lane `ex3-ara-cortinas-q57`.
  - Theorem 4.1 reads: "There is no unital ∗-algebraic embedding of L2,Z ⊗ L2,Z into L2,Z."
  - Page 2 calls the question over fields "an open problem in the subject".
  - The proof needs integer positivity (Lemma 2.1, Proposition 4.4), and their Example 2.2 shows it fails over
    `Z/2Z`. So nothing over `F_2` follows (artifact, Sections 1–2).
- Their Weyl-algebra obstruction (Theorem 3.5) passes through a C*-norm and needs characteristic zero. It says
  nothing over `F_2`.

**Later check (lane `ex3-ara-cortinas-q57`).**
- *Read and does not address the question.* H. V. Khanh, *Group algebras that do not embed into L_K(1,2)*,
  Res. Math. Sci. 13 (2026) 72. Its obstruction is an unsolvable word problem.
- *Checked by title only.* The other seven works that OpenAlex lists as citing Brownlowe–Sørensen. None announces an
  answer.
- *Not searched.* Web search was exhausted and the arXiv API was rate-limited. See the artifact, Sections 3–4.

**What it would change.**
- A positive answer, a unital embedding, would put the Brin--Thompson-type unit group `(L ⊗ L)^x`, which contains
  `V × V`, inside `L^x`.
- It would also refute `leavitt-commuting-units-are-algebraically-dependent` and
  `leavitt-unit-centralizers-have-finite-rank`.
- A negative answer follows from `leavitt-commuting-units-are-algebraically-dependent`
  (`tensor-square-nonembedding-from-algebraic-dependence`).

## Attempts

**K-theory.** It gives no obstruction: `K_*(L) = K_*(L ⊗ L) = 0` (`ara-cortinas-leavitt-tensor-k-theory-vanishes`).

**Commuting units.** A unital map sends `c ⊗ 1` and `1 ⊗ c`, for the north--south unit `c`, to algebraically
independent commuting units. An obstruction to such pairs in `L` therefore decides the question; see the route
above. No such obstruction is proved.

**Thompson units (Brownlowe--Sørensen transfer, lane `ex3-ara-cortinas-q57`, unreviewed).**
- *Their integer argument does not transfer.* Images here are arbitrary units, not unitaries, and even ∗-unitaries
  over `F_2` need not be monomial (their Example 2.2).
- *Their Proposition 3.4 does transfer.* Commuting elements of `U_V` satisfy a nonzero polynomial relation, over any
  commutative ring, and the proof uses only the dynamics of `V`.
- *Consequence.* For any unital `f` and any transcendental units `u, v` (e.g. `c`), `f(u ⊗ 1)` and `f(1 ⊗ v)` are not
  both conjugate, by one unit, into `U_V` (artifact, Section 2).
- *Where it dies.* Linear units with components of both signs.

**Relative commutants (proved reformulation, lane `ex2-q34-commuting-units`).** Put `R = L` and
`phi(z) = s_0 z t_0 + s_1 z t_1`, a unital endomorphism.
1. *Unital endomorphisms are units.* Every unit `u` gives the Leavitt family `(u s_i, t_i u^(-1))`, hence a
   unital endomorphism `rho_u`. Conversely, for unital `rho` put `u = rho(s_0) t_0 + rho(s_1) t_1` and
   `u' = s_0 rho(t_0) + s_1 rho(t_1)`. Then `u u' = Σ_i rho(s_i) rho(t_i) = 1`, `u' u = Σ_i s_i t_i = 1`,
   `u s_i = rho(s_i)` and `t_i u' = rho(t_i)`, so `rho = rho_u`.
2. *The question is about commutants.* A unital `f : L ⊗ L -> L` is `f(x ⊗ y) = rho_u(x) psi(y)` with
   `u` as in 1 and `psi = f(1 ⊗ -)` a unital map into `C_u = C_R(rho_u(R))`. Conversely such a `psi` defines `f`.
   So a unital map exists iff some `C_u` contains a unital homomorphic image of `L`.
3. *Formula.* `C_u = { z : z u s_i = u s_i z, i = 0, 1 } = { z : u phi(z) u^(-1) = z }`.
   - Commuting with `u s_j` gives commuting with `t_i u^(-1)`:
     `t_i u^(-1) z = Σ_j t_i u^(-1) z u s_j t_j u^(-1) = Σ_j t_i s_j z t_j u^(-1) = z t_i u^(-1)`.
   - If `z u s_i = u s_i z`, then `u^(-1) z u = Σ_i u^(-1) z u s_i t_i = Σ_i s_i z t_i = phi(z)`.
     Conversely `u phi(z) u^(-1) = z` gives `z u s_i = u phi(z) s_i = u s_i z`.
4. *Controls.* `u = 1` gives the center `F_2`. The flip `u = s_00 t_00 + s_10 t_01 + s_01 t_10 + s_11 t_11`
   gives `rho_u = phi`. Under `R ≅ M_2(R)`, `phi(R)` is the diagonal, so `C_u = M_2(F_2) = span{ s_i t_j }`.

**Exact screen (MSI, `relcomm.py` in `/projects/standard/hsiehph/sauer354/ex/ex2-q34-commuting-units/`).**
`dim(C_u ∩ R_N)` was computed by linear algebra for `N = 1, 2, 3`.
- Controls: `1`, the Thompson units `A` (north--south) and `C`, and the transvection words `X`, `Z`, `XY`,
  `ZR` give `1` at every `N <= 4`, and the flip gives `4`.
- 843 distinct random units (words of length 2–10 in the thirteen generators of the predecessor's squaring
  screen, depth `<= 4`): 842 give `[1, 1, 1]`, and `PBa` gives `[2, 2, 2]`. None grows with `N`.

A positive answer needs a unit whose relative commutant is infinite-dimensional. Random short words do not
produce one.

**What is proved about a hypothetical unital map (lane `ex2-q34-commuting-units`).**
- *Triangular units.* The first-factor unit `u` has no twisted conjugate `w u phi(w)^(-1)` in `H_<=` or
  `H_>=`, over any field (`leavitt-triangular-endomorphism-commutants-are-finite`).
- *Annulus units.* No `f(g ⊗ 1)` or `f(1 ⊗ g)` is conjugate to a north--south annulus unit
  (`leavitt-annulus-north-south-units-have-cyclic-centralizers`).
- *Diagonal copies.* Every `z ∈ f(1 ⊗ L)` satisfies `z = u phi(z) u^(-1)`, so it is conjugate to its own
  diagonal copy and has trace zero in `HH_0(L)`.
- *Open premises.* Three open claims would each give a negative answer: `leavitt-endomorphism-relative-commutants-are-finite`,
  `leavitt-units-are-not-conjugate-to-diagonal-copies`, and `leavitt-commuting-units-are-algebraically-dependent`.
