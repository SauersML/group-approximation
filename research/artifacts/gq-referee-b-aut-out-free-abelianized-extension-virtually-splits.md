# gq-referee-b: `aut-out-free-abelianized-extension-virtually-splits` (citation and scope lens)

Node, route and the Attempt-4 edit of `out-free-groups-virtually-embed-in-aut-free-groups`, as landed at 518dae5bd
(lane bh-outfn). Lens: conventions against the imported node, novelty against the literature, and scope statements
against what is proved. The proof was passed by gq-referee-a (329ff16a3).

**Verdict: PASS.**
- The cocycle conventions match the imported node exactly.
- "No novelty claimed" is right. I found a published source for the key input: Kawazumi's first Johnson map, whose
  contraction is a crossed homomorphism `Aut(F_n) -> H` equal to `(1 − n)`·abelianization on `Inn(F_n)`.
- The scope statements hold.
- One wording point on the Attempt-4 edit (W1).

## 1. Conventions against `aut-out-free-abelianized-extension-splits-rationally`

- **Crossed-homomorphism rule.** The imported route (`aut-out-free-abelianized-extension-proof`, item 1) derives
  `h(φψ) = h(φ) + φ_* h(ψ)` from `M̄(φψ) = φ_*(M̄(ψ))·M̄(φ)`, where `M(φ)_ki = ∂φ(x_k)/∂x_i`.
  - I rechecked this from the Fox chain rule, `∂φ(w)/∂x_i = Σ_j φ(∂w/∂x_j)·∂φ(x_j)/∂x_i`.
  - The target uses the same identity. ✓
- **Value on inner automorphisms.** `h(ι_g) = (n − 1)[g]`, with `ι_g(x) = g x g^(-1)`.
  - Abelianizing gives `M̄(ι_g) = tI + uv^T`, with `u_k = 1 − t_k` and `v_i = ∂̄_i g`.
  - The fundamental formula gives `v^T u = 1 − t`, so `det = t^(n−1)(t + v^T u) = t^(n−1)`. ✓
- **The semidirect product in route item 1.** The multiplication `(a, A)(b, B) = (a + Ab, AB)` is the one for which a
  crossed homomorphism with that rule is a homomorphism. `{0} × GL(M)` is a subgroup. ✓
- **The two quotients agree.** The imported node's `Aut(F_n)/[Inn, Inn]` and the target's `Aut(F_n)/Inn([F_n,F_n])`
  are the same group, since `Inn(F_n) ≅ F_n` for `n ≥ 2`.
  - The kernel `Inn/Inn([F_n,F_n]) ≅ H` carries the natural `Out(F_n)`-action, which is the one used for `c`. ✓
- Items 1–7 of the route are correct as written. This agrees with referee a.

## 2. Novelty and a source

- **The input crossed homomorphism is in print.** N. Kawazumi, *Cohomological aspects of Magnus expansions*,
  arXiv:math/0505497v3, §2, read at source, pp. 9–11.
  - The first Johnson map `τ_1^θ : Aut(F_n) -> H* ⊗ H^(⊗2)` satisfies `τ_1^θ(φψ) = τ_1^θ(φ) + |φ| τ_1^θ(ψ)` (p. 10).
    So it is a twisted 1-cocycle (Lemma 2.1, (2.5)).
  - On inner automorphisms, (2.11) p. 11: `τ_1^θ(ι(γ))a = [γ]a − a[γ]`.
  - Contracting `H*` against the first `H`, via `f ⊗ x ⊗ y ↦ f(x) y`, gives a crossed homomorphism `Aut(F_n) -> H`.
    Its value on `ι(γ)` is `Σ_i e_i*([γ]) e_i − Σ_i e_i*(e_i)[γ] = (1 − n)[γ]`.
  - This is exactly the "equivariant contraction ..., which restricts to `(1 − n)` on `H`" of the route's
    independent-check paragraph. So the route's second proof is Kawazumi's cocycle, and the lane's Fox-determinant
    cocycle has the same restriction up to sign.
  - For surfaces, Kawazumi (p. 2) credits Earle's integral 1-cocycle `(2 − 2g)ψ` and Morita's `k̃`. These are the
    analogues the claim node mentions.
- **The deduction is routine.** Divide by `n − 1` where the cocycle is divisible, and take the zero set. I found no
  printed statement that the abelianized extension splits over `{h ∈ (n − 1)H}`. That search was bounded: Kawazumi
  §§1–3 only. Satoh's computations of the twisted (co)homology of `Aut(F_n)` with coefficients in `H` are not on arXiv
  and were not read.
- So "no novelty claimed" is right. Suggest adding "the crossed homomorphism is the contraction of Kawazumi's first
  Johnson map (arXiv:math/0505497, (2.5), (2.11)), up to sign".

## 3. Scope

- **No virtual section is claimed.** The claim says so explicitly: "It does not give a virtual section". The Attempt-4
  edit says "No virtual section ... is constructed" in the commit message, and "What remains ..." in the text. ✓
- **No Boone–Higman consequence is claimed.** "It does not touch Boone--Higman for `Out(F_n)` directly
  (`out-free-groups-satisfy-boone-higman`, OPEN)." ✓
- **"So neither rational nor integral cohomology of the abelianized extension can exclude a virtual section."**
  Correct: `c|_(Γ_n) = 0`, and a virtual section over `Γ' ≤ Γ_n` is compatible with a split extension. ✓
- **The `n = 2` case.** `A_2 = Aut(F_2)`, so the abelianized extension of `GL_2(Z) = Out(F_2)` by `Z^2` splits. This
  claim is about the abelianized extension only, and it is consistent with any statement about `Aut(F_2) -> Out(F_2)`
  itself. ✓

## Warning (wording only)

- **W1 (Attempt-4 edit).** "What remains is whether the extension of that finite-index subgroup by `[F_n, F_n]`
  virtually splits". Read literally, this makes the `K_n`-extension question equivalent to a virtual section. The claim
  node, after referee a's W1, is careful that it is only sufficient:
  - A virtual section `s` lands, after conjugating by an inner automorphism, in `K_n` exactly when the crossed
    homomorphism `k∘s : Γ' -> H` is virtually principal.
  - `H^1` of finite-index subgroups of `Out(F_n)` with coefficients `H` is not controlled here.
  - Suggest: "A virtual splitting of the extension of `Γ_n` by `[F_n, F_n]` would give a virtual section. The converse
    holds when `k∘s` is virtually principal. This is the nonabelian question."
