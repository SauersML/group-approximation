# sk-cstar-idempotent part 1: the commutator lemma for unit groups, and where it cannot start

Lane sk-cstar-idempotent (wave 11). Sources read at source on MSI:
- Le Boudec–Matte Bon, arXiv:2006.08677 (`tran-confined-LBMB.tex`): §3 l.419–694, the proof of Theorem 3.17 and Proposition 3.x; §4 l.695–756 (Lemmas 4.1–4.4 and Theorem 4.5).

## 1. Theorem A (commutator lemma for confined subgroups of unit groups)

**Setting.** `M` is a unital ring and `L = M^×`. For a nonzero idempotent `E ∈ M`:
- `Stab(E) = {g ∈ L : gE = Eg}`, and `p_E : Stab(E) → (EME)^×`, `g ↦ EgE`, is a homomorphism;
- `g` is *supported in* `E` if `g − 1 ∈ EME` (then `g ∈ Stab(E)` and `g = 1 − E + p_E(g)`, so `p_E` is injective on such `g`);
- `g` is *trivial on* `E` if `gE = Eg = E`;
- `E ⊥ F` means `EF = FE = 0`.

**Theorem A.** Let `G, H ≤ L`, with `H` confined by `G`, `P` a confining subset and `r = |P|`. Let `{E_σ}_{σ∈P}` be nonzero idempotents, and for each `σ` let `R_σ ≤ G` be a nontrivial subgroup of elements supported in `E_σ`, with `R_σ = R_ρ` whenever `E_σ = E_ρ`, and `FC_{≤r}(R_σ) = 1`. Assume:
- (C1) `E_σ = E_ρ` or `E_σ ⊥ E_ρ`;
- (C3) for all `σ, ρ`: `σ` is trivial on `E_ρ`, or `σE_ρσ^{-1} ⊥ E_α` for all `α`;
- (C4) for all `σ`: `σE_σσ^{-1} ⊥ E_α` and `σE_σσ^{-1} ⊥ σ^{-1}E_ασ` for all `α`.

Then there are `ρ ∈ P` and a nontrivial `N ≤ H ∩ R_ρ` whose normalizer in `R_ρ` has index at most `r`.

**Corollary A′.** If moreover every `R_σ` is an infinite simple group, then `H ⊇ R_ρ` for some `ρ`. In particular, if some `R_ρ` is nonamenable, `H` is not amenable.
- Proof: an infinite simple group has no proper finite-index subgroup, so `N ⊴ R_ρ`, and so `N = R_ρ`.
- Infinite simple groups have trivial FC-center, since the FC-center is normal.

## 2. Proof of Theorem A: LBMB's proof, read in the ring dictionary

The proof of Theorem 3.17 in arXiv:2006.08677 (§3.3–3.4) uses sets only through four operations. Each has a ring version.

| LBMB (sets `Ω`) | ring (idempotents `E`) |
|---|---|
| `Ω ∩ Ω' = ∅` | `E ⊥ E'` |
| `σ(Ω)` | `σEσ^{-1}` |
| `g` supported in `⋃Ω_i`, preserving each `Ω_i` (pairwise disjoint) | `g − 1 = Σ_i E_i(g−1)E_i` for a pairwise orthogonal family `E_i` |
| restriction `p_Ω` | compression `p_E` |

**Group theory.** Neumann's covering lemma (Lemma 3.9 there) and the product decomposition `R = ∏_{distinct E} R_E` are unchanged.
- If `E ⊥ E'`, elements supported in `E` and in `E'` commute: `(1+x)(1+y) = 1+x+y = (1+y)(1+x)` since `xy = yx = 0` for `x ∈ EME`, `y ∈ E'ME'`.
- They meet only in `1`: `x = y` forces both to be `0`.

The rigid groups `R_σ` enter only through two facts:
- being supported in `E_σ`;
- `σR_ασ^{-1}` is supported in `σE_ασ^{-1}`.

So the proof never needs the full pointwise fixator, and any chosen subgroups work.

**The idempotents that occur, for fixed `σ`.** Define `M_σ` and `F_σ` as in LBMB, with (C3) giving `P = M_σ ⊔ F_σ`. The proof uses the family
`𝔉_σ = {E_α : α ∈ P} ∪ {σ^{-1}E_ρσ : ρ ∈ M_σ} ∪ {σE_ρσ^{-1} : ρ ∈ M_σ}`
and needs every pair from the same support list to be equal or orthogonal:
- `E_α, E_β`: (C1).
- `σE_ρσ^{-1}, E_α` for `ρ ∈ M_σ`: definition of `M_σ`.
- `σ^{-1}E_ρσ, E_α` for `ρ ∈ M_σ`. If `α ∈ M_σ`, then `σ^{-1}E_ρσ·E_α = σ^{-1}(E_ρ·σE_ασ^{-1})σ = 0`, and similarly on the other side. If `α ∈ F_σ`, then `σ^{-1}E_ρσ·E_α = σ^{-1}E_ρE_ασ = 0`: `σ` is trivial on `E_α`, and `E_ρ ≠ E_α` because `σ` cannot both fix and displace a nonzero idempotent. (LBMB Remark after Def. 3.12.)
- `σ^{±1}E_ρσ^{∓1}` versus `σ^{±1}E_{ρ'}σ^{∓1}`: conjugates of (C1).
- `σE_σσ^{-1}` versus `σ^{-1}E_ασ`: (C4). This is the only mixed pair the proof needs (the Claim in Prop. 3.x). The supports of `A^ρ_{σ,k}` and of `h` are `{E_ρ} ∪ {σ^{-1}E_ασ}_{α∈M_σ}` and `{E_α}_{α∈M_σ} ∪ {σE_σσ^{-1}}`, and every cross pair is orthogonal except `E_ρ = E_α`.

**Line-by-line checks** (LBMB lemma numbers as in the source).
- **Lemma A-supp (i).** For `γ, δ ∈ R`, `c = σ^{-1}δ^{-1}γσ` is supported in `σ^{-1}Fσ`, where `F = Σ_{distinct} E_α`. Here `σ^{-1}Fσ = Σ_{F_σ} E_α + Σ_{M_σ} σ^{-1}E_ασ`, a sum of pairwise orthogonal idempotents, each orthogonal to or equal to the `E_α`. So `a_{δ,γ} = δcγ^{-1}` is supported in the join and preserves every piece.
  - On `E_α` with `α ∈ F_σ`: `E_ασ^{-1} = E_α = σE_α`, so `E_α c E_α = E_α δ^{-1}γ E_α`, and `a` is trivial on `E_α`.
- **Lemma A-supp (ii).** For `ρ ∈ M_σ`, `E_ρ ⊥ σ^{-1}Fσ`, so `c` is trivial on `E_ρ` and `p_{E_ρ}(a) = p_{E_ρ}(δγ^{-1})`.
- **Lemma B-supp.** `λ ∈ R` is supported in `F`, and `σ^{-1}E_ρσ ⊥ F` for `ρ ∈ M_σ`. So `λσλ^{-1}` conjugates `σ^{-1}E_ρσ` to `E_ρ` and `E_ρ` to `σE_ρσ^{-1}`, exactly as the set proof says. The compression identity `p_{E_ρ}(λσλ^{-1} a λσ^{-1}λ^{-1}) = p_{E_ρ}(λδ^{-1}γλ^{-1})` holds because `σλ^{-1}δσ^{-1}` and `σγ^{-1}λσ^{-1}` are supported in `σFσ^{-1}`, which is orthogonal to `E_ρ`.
- **Lemma proj-Ai.** For `a ∈ A_{σ,k}^ρ`, `p_ρ(a) = p_ρ(d)` with `d ∈ D_{σ,k}`. So `p_ρ(A^ρ) ⊇ D ∩ R_ρ`, and `(R_ρ : p_ρ(A^ρ)) ≤ (R_ρ : D ∩ R_ρ) ≤ (R : D)`.
- **Claim of the Proposition.** `f ∈ A^σ` with `p_σ(f) ≠ 1`. `h = λσλ^{-1} f λσ^{-1}λ^{-1}` is supported in `Σ_{α∈M_σ}E_α + σE_σσ^{-1}` and preserves the pieces. `A^ρ` is supported in `E_ρ + Σ_{α∈M_σ}σ^{-1}E_ασ`. Both elements are block diagonal over the orthogonal family `{E_ρ} ∪ {σ^{-1}E_ασ} ∪ {E_α}_{α≠ρ} ∪ {σE_σσ^{-1}}`, and they share only the block `E_ρ`. So `[a,h] = 1 − E_ρ + [p_ρ(a), p_ρ(h)]`, which is supported in `E_ρ`.
  - `p_ρ(a), p_ρ(h) ∈ R_ρ` (Lemma B-supp), so `[a,h] ∈ H ∩ R_ρ`.
  - FC-triviality gives `a` with `[a,h] ≠ 1`, as in the source.
- **Conclusion of the Proposition.** `N = ⟨a h_0 a^{-1} : a ∈ A_S⟩ ≤ H ∩ R_ρ` is normalized by `p_ρ(D_{σ,k})`, which has index `≤ r` in `R_ρ`.

Every other sentence of LBMB §3.3–3.4 is formal group theory. So Theorem A holds with the same constants (`n = 1`). ∎

## 3. Lemma B: idempotent displacement cannot start for units with short polynomial identities

**Lemma B.** Let `M` be a unital ring, `σ ∈ M^×`, `E ∈ M` an idempotent, and `K ⊆ Z ∖ {0}` finite. Suppose `Eσ^kE = 0` for all `k ∈ K` and `1 = Σ_{k∈K} c_k σ^k` with `c_k` central. Then `E = 0`.

**Proof.** `E = E·1·E = Σ c_k Eσ^kE = 0`. ∎

**Displacement conditions give exactly these zeros.**
- `E ⊥ σEσ^{-1}` ⟺ `EσE = 0 = Eσ^{-1}E`. From `EσEσ^{-1} = 0`, multiply by `σ` on the right; from `σEσ^{-1}E = 0`, multiply by `σ^{-1}` on the left.
- (C4) at `α = σ` adds `σEσ^{-1} ⊥ σ^{-1}Eσ` ⟺ `Eσ^{-2}E = 0 = Eσ^2E`.

**Corollary B′** (for `F_2`-algebras):
1. If `σ + σ^{-1} = 1`, i.e. `σ^2 + σ + 1 = 0`, no nonzero idempotent is displaced by `σ`.
2. If `1 ∈ span_{F_2}{σ, σ^{-1}, σ^2, σ^{-2}}`, no nonzero idempotent satisfies (C4) for `σ`. So no confining set containing `σ` has an idempotent displacement configuration, in any ring containing `σ`.

**These classes occur in `G_X = EL_3(LC(X,F_2)⋊Z)` as constant matrices in `EL_3(F_2) ≤ G_X`:**
- **involutions**, e.g. every transvection `e_ij(r)`: `σ^2 = 1`;
- **order-4 unipotents** `σ = I + N`, `N = E_12 + E_23`: `σ^{-1} = I + N + N^2` and `σ^2 = I + N^2`, so `σ + σ^{-1} + σ^2 = I`;
- **Singer elements** of order 7 acting as `α` on `F_8 = F_2^3`: `α, α^2, α^5 = α^{-2}, α^6 = α^{-1}` span `F_8`, which contains `1`.

Order-3 elements of `GL_3(F_2)` never satisfy `σ^2+σ+1 = 0`, since `F_2^3` has odd dimension. Constant fibrewise units can therefore always be displaced once, but (C4) fails for orders 2, 4 and 7.

**Contrast with LBMB §4.** For homeomorphisms, (C4) is available whenever `σ^2 ≠ 1` (their Lemma 4.1), and involutions are excluded by Lemmas 3.3 and 4.3. Their compactness Lemma 3.3 works for any subset `B ⊂ L`: either `H` has a confining subset avoiding `B`, or some `K` in the orbit closure of `H` satisfies `K ⊆ B ∪ {1}`. `K` is again confined, and amenable if `H` is (Chabauty limits of amenable subgroups of a discrete group are amenable). So the idempotent route to C*-simplicity of `G_X` needs:
- (L3) a pigeonhole lemma excluding confined subgroups inside `B_4 ∪ {1}`, where `B_4 = {σ : 1 ∈ span_{F_2}(σ^{±1}, σ^{±2})}`. These are all torsion of bounded order, since `dim F_2[σ] ≤ 4`. It needs single displacement of the confining elements, and Lemma B blocks that for `σ^2+σ+1 = 0`.
- (L4) configurations for finite subsets of `G_X ∖ B_4`, whose rigid groups are `EL_3` of first-return crossed products.

Status: Theorem A and Lemma B are established here (unreviewed). (L3) and (L4) are open; see part 2 when landed.
