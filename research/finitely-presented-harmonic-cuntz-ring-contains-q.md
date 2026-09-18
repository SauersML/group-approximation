---
rg: 2
id: finitely-presented-harmonic-cuntz-ring-contains-q
kind: claim
title: An explicit six-generator finitely presented *-ring with a Leavitt family contains Q and maps onto the harmonic Cuntz ring and into O_2
distinct_from:
  harmonic-cuntz-ring-is-purely-infinite-simple: that is the concrete operator ring C_h, with division and centre; this is an abstract finitely presented ring mapping onto it, whose kernel is not known.
  infinite-field-leavitt-units-are-not-finitely-generated: that shows no finitely generated subring of a Leavitt algebra over a field contains Q; this finitely presented ring contains Q because of its two extra generators.
  algebra-boone-higman-conjecture: that asks for simple finitely presented algebras containing decidable ones; this is a finitely presented ring containing Q with no simplicity claim.
artifacts:
  - research/artifacts/gq-gq-cuntz-cstar-dictionary.md
  - research/artifacts/gq-referee-a-finitely-presented-harmonic-cuntz-ring-contains-q.md
---

**ESTABLISHED** by `finitely-presented-harmonic-cuntz-ring-proof` (elementary;
proof-gap review PASS by lane `gq-referee-a`,
`research/artifacts/gq-referee-a-finitely-presented-harmonic-cuntz-ring-contains-q.md`;
no priority claimed: an explicit finitely presented ring containing `Q` may well be
folklore).

Let `R_Q` be the unital ring with generators `s_0, s_1, t_0, t_1, h, g` and relations
- (L) `t_i s_j = δ_ij` for `i, j ∈ {0,1}`, and `s_0 t_0 + s_1 t_1 = 1`;
- (D) `h s_0 t_0 = s_0 t_0 h` and `g s_0 t_0 = s_0 t_0 g`;
- (I) `g(1 + h) = 1 = (1 + h) g`;
- (E0) `t_0 h s_0 = 1`;
- (E1) `t_1 h s_1 = h g`.

Then:
1. **Q inside.** Every nonzero integer is invertible in `R_Q`, and `R_Q ≠ 0`. So
   `Q ⊂ R_Q` as a unital central subring.
2. **Matrix stability.** `R_Q ≅ M_n(R_Q)` as unital rings, for every `n >= 1`.
3. **Onto C_h.** `s_i ↦ s_i`, `t_i ↦ t_i`, `h ↦ m_η`, `g ↦ m_ζ` extends to a
   surjective unital ring homomorphism onto the harmonic Cuntz ring
   (`harmonic-cuntz-ring-is-purely-infinite-simple`).
4. **Into O_2.** With `s_i^* = t_i`, `h^* = h`, `g^* = g`, `R_Q` is a *-ring. Sending
   `s_i` to the Cuntz isometries on `L^2(X)` and `h, g` to multiplication by the
   continuous functions `η, ζ` gives a unital *-homomorphism into `O_2` whose image
   is dense.

So `GL_n(Q) ⊂ GL_n(R_Q) ≅ R_Q^x` for every `n`. The proof uses only the six
generators and five relation families, so `R_Q` is a concrete input for
finite-presentation arguments about Steinberg groups.
- **Central quotients fail.** `R_Q` contains `Q` centrally and a Leavitt family, so
  by `leavitt-scalar-commutators-block-fp-central-quotients` no central quotient of
  `R_Q^x`, or of `E_N(R_Q)` modulo its centre, is finitely presented.
- **Steinberg overgroups (referee's remark, not checked here).** The review artifact
  notes that the landed Steinberg finite-presentation lemmas (commits fbbb1c736 and
  0b381f2c1, the latter conditional on its citations) apply to `R_Q`. So `St_4(R_Q)`
  and `St_(6n+7)(R_Q)` would be further finitely presented overgroups of `GL_n(Q)`.
  They are not simple.

**Open.** Is `R_Q -> C_h` injective? `C_h` is simple, so the kernel is a maximal
ideal.
