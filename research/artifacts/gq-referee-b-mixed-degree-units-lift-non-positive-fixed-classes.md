# Referee report (gq-referee-b, citation lens): mixed-degree units lift non-positive fixed classes

**Reviewed.** `mixed-degree-units-lift-non-positive-fixed-classes` and its `-proof` (lane gq-infinite-primes,
48c3f0945), read on origin/main.

**Source read.** Ara–Brustenga–Cortiñas (ABC), *K-theory of Leavitt path algebras*, arXiv:0903.0056v2, PDF pages 5–7
and 13–19 (journal pages 100003–100017).

**Verdict: PASS.**
- Items 1–3 are correct. The example checks.
- Item 4 is honestly stated as an implication from (CSL).
- The first bullet of (CSL), `NK = 0`, can be derived from ABC by an argument I pin below. The other two bullets,
  `K_*(Q)`-linearity and the index formula, are not stated in the ABC pages I read.

## Where ABC prove NK vanishing for a corner isomorphism

It is **not** in the proof of Theorem 7.6. That proof reads "The case when E is finite follows from Proposition 7.5
and the argument of the proof of Theorem 6.3". The step is in the **proof of Proposition 7.5**, p. 100013:

> "Let B = φ^(-1)L_0, where φ = φ ⊗ 1 : L_0 = L_0^Z ⊗ k → L_0 is the corner-isomorphism defined by φ(x) = t_+ x t_−,
> as in Section 5. Note that since k is regular supercoherent and B is H′-unital we have NK(B̃, φ̂)_± =
> NK(B ⊕ k, φ̂)_±, where B ⊕ k denotes the k-unitization of B. Now it follows from Proposition 7.1 that B ⊕ k is
> regular supercoherent. Therefore Lemma 7.2 gives that NK(B ⊕ k, φ̂)_± = 0. It follows that NK(L_0, φ)_± =
> NK(B̃, φ̂)_± = NK(B ⊕ k, φ̂)_± = 0".

Its ingredients:
- **The definition.** p. 100004: for an endomorphism `φ : A → A`, `B = φ^(-1)A` is the colimit, `φ̂` the induced
  automorphism, and "NK(A, φ)_± := NK(B̃, φ̂)_±".
- **Theorem 3.6**, p. 100004: "Let R be a unital ring and let A be a ring. Let φ : R → pRp be a corner-isomorphism.
  Assume that R ⊗ A is H′-unital. Then there is a homotopy fibration of nonconnective spectra
  K(R ⊗ A) → K(R ⊗ A) ⊕ NK(R ⊗ A, φ ⊗ 1)_+ ⊕ NK(R ⊗ A, φ ⊗ 1)_− → K((R ⊗ A)[t_+, t_−, φ ⊗ 1])", with first map
  `1 − φ ⊗ 1`.
- **Proposition 7.1**, p. 100011. This is the only quiver-specific input: "Let E be a finite quiver without sources
  and let k be a regular supercoherent ring. Let B = φ^(-1)L_0, where L_0 is the homogeneous component of degree 0 of
  L_k(E). Let D = B ⊕ k be the k-unitization of B. Then D is regular supercoherent."
- **Lemma 7.2**, p. 100012: for `R` regular supercoherent and `φ` an automorphism, `NK_n(R[t_1^(±1), …], φ)_± = 0`.

**Transfer to this node's core.** `R_0` is ultramatricial over `Q`, and `α = t_+(·)t_−` is a corner isomorphism
`R_0 → g R_0 g`, with inverse `x ↦ t_− x t_+`. The ABC argument goes through with Proposition 7.1 replaced by an easier
fact.
- `B = α^(-1) R_0` is a directed union of finite-dimensional semisimple `Q`-algebras.
- So `B ⊕ Q` is ultramatricial.
- Hence `B ⊕ Q` is regular supercoherent. Unital inclusions of semisimple algebras are flat, polynomial rings over
  them are regular noetherian, and flat colimits of regular coherent rings are regular coherent (Gersten, cited by
  ABC as "[17, Proposition 1.6]" in the proof of Proposition 7.1).
- `B` has local units, so it is H′-unital. ABC Remark 2.2 says H′ = H for `Z`-flat rings.
- Theorem 3.6 with `A = Z` then gives the sequence of (CSL), bullet 1.

**Recommendation.** Record bullet 1 of (CSL) as a consequence of ABC Theorem 3.6, Lemma 7.2 and the Proposition 7.5
argument, with the ultramatricial substitute for Proposition 7.1. Gersten's Proposition 1.6 itself was not read.

**Bullets 2–3 of (CSL): not found.**
- ABC state the fibration and the Leavitt-path corollaries (Theorem 7.6, Corollary 7.7) without a formula for `∂` on
  units, and without `K_*(k)`-linearity, in the pages read.
- These remain the trust surface, shared with T1 of `laurent-rational-symbols-block-fp-elementary-groups`.
- ABC's reference [2], Ara–Brustenga, *Module theory over Leavitt path algebras and K-theory*, may contain the index
  description. It was not reached.

**AGGP.** The name is confirmed. ABC cite "[3] P. Ara, M.A. González-Barroso, K.R. Goodearl, E. Pardo. Fractional
skew monoid rings. J. Algebra 278 (2004) 104–126" for the construction of `S[t_+, t_−, φ]`. The paper itself was not
read.

## Steps checked

- **Item 1.**
  - `ι_n(c) = S_n c T_n` is unital and injective, and the transition maps are `c ↦ φ(c)`.
  - So `R_0` is ultramatricial, and `K_0(R_0) = colim_A Q^m`.
  - `w_g = Sφ(g)` has domain `φ(g)` and range `g`, so `[E] = A^(-1)[D]`.
- **Item 2.**
  - There is an idempotent `g` with `[g] = A^(-1)[1_B]`, and cancellation gives `φ(g) = xy`, `yx = 1`.
  - `t_− t_+ = ypx = 1` and `t_+ t_− = g`.
- **Item 3, the example.**
  - `A^(-1) = (1/4)[[3,−1],[−2,2]]`, so `A^(-1)(1,1) = (1/2, 0)`.
  - `dom_+ = (2,2)`, `ran_+ = (1,0)`, `dom_− = (0,1)`, `ran_− = (1,3)`. Both totals are `(2,3)`, and
    `(2,2) − (1,3) = (1,−1)`.
  - Correct.
- **Item 4.**
  - `K_1(R_0) = Q^x ⊗ K_0(R_0)` for ultramatricial `R_0` over `Q`, via `det`, and the classes `λ ⊗ εv` are
    infinitely generated.
  - The last sentence is correctly limited: "invertible `A` and a corner isometry", conditional on (CSL).
