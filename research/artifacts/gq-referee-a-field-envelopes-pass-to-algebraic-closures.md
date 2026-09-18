# Referee report (gq-referee-a, proof-gap lens): field envelopes pass to algebraic closures

**Reviewed:** `field-envelopes-pass-to-algebraic-closures` and its route `-proof` (lane gq-ring-fp-simple,
36d65161f), read on origin/main.

**Verdict: PASS for parts 1 and 2 and for the proof.** Part 3 overstates in two places, both fixable by
rewording (§4 below).

## 1. §1: the host
- `R` is a `Q`-algebra. It has a copy of `K`, so it has characteristic 0, and the centre of a simple unital
  ring of characteristic 0 is a field containing `Q`.
- `R ⊗_Q L_Q` is simple by the tensor lemma, since `L_Q` is simple with centre `Q`. This is the standard
  central-simple tensor lemma, and I read its proof in `polynomially-representable-envelopes-via-leavitt-tensors`
  §2.
- `R ⊗_Q L_Q = R ⊗_Z L_Z(1,2)` is presented by the two presentations together with commutation relations.
- Flatness gives `L_K = K ⊗_Q L_Q ↪ R ⊗_Q L_Q`. When `K ⊆ R` is not unital, the map `K → R` is still
  `Q`-linear, because `φ(x/m)` is the unique `y` with `my = φ(x)`.

## 2. §2: matrix absorption (the author's point (c))
- **The isomorphisms `θ_r`.** `L_F ≅ L_F^r` as right modules, which gives unital `F`-algebra isomorphisms
  `θ_r: L_F → M_r(L_F)`.
  - `θ_r(f) = f·I_r` for `f ∈ F`, because `f` is central and the module isomorphism is right-linear.
- **The chain.** `φ_{i+1} = M_{d_i}(θ_{r_i})∘φ_i`, and `ι_i(x) = φ_i^{-1}(x·1)`.
- **Compatibility.** The `(a,b)` block of `κ_i(x)` is `x_{ab} I_{r_i}`. Applying `θ_{r_i}^{-1}` to each block
  gives `x_{ab}·1`. So `ι_{i+1}∘κ_i = ι_i`.
- **The one convention to keep.** The block identification `M_{d_i}(M_{r_i}) = M_{d_{i+1}}` in `φ_{i+1}` and the
  Kronecker map `κ_i = x ⊗ I_{r_i}` must use the same outer index. Both put the `d_i`-index outer, so they
  agree.

## 3. §3: algebraic extensions
- **The basis ordering must be stated.** `ρ_{i+1}|_{E_i} = κ_i∘ρ_i` holds exactly when the basis `{bc}` of
  `E_{i+1}` is ordered with the `E_i`-basis index `b` outer and `c` inner.
  - Check: `α(bc) = Σ_{b'} ρ_i(α)_{b'b} b'c`, so the entry at `((b',c'),(b,c))` is `ρ_i(α)_{b'b} δ_{c'c}`.
  - Add one sentence fixing this ordering. The first step should start from `E_0 = F`, with `d_0 = 1` and
    `φ_0 = id`.
- **The embedding.** With that ordering the maps are well defined, unital, injective ring homomorphisms. `K̄` is
  countable because `R` is.
- **§4.** Correct. A field of transcendence degree `k` is algebraic over `F_k ⊆ R_k`.
  - For `k = 0`: `L_Q ⊆ R_L`, because the Leavitt family of `R_L` gives a unital map from the simple ring `L_Q`.
    So `Q̄ ⊆ R_L`.

## 4. Part 3 overstates
1. "`GL_n(Q̄)` embeds in `R_L^x`, and so does `GL_n(K)` for every countable field `K` of characteristic zero and
   finite transcendence degree."
   - For transcendence degree `≥ 1`, the proof gives `GL_n(K) ≤ (R_k ⊗_Q L_Q)^x`, not `R_L^x`.
   - Nothing shown here puts `Q(t)` inside `R_L`.
   - Reword to "in the unit group of the finitely presented simple ring `R_k ⊗_Q L_Q`".
2. "such unit groups have no finitely presented central quotients".
   - The cited lemma covers only quotients by central subgroups that contain `Q^x`.
   - Reword accordingly.
