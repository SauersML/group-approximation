# EX review wave 2, part 12: the KK norm functor, Theorems A and B (2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0. Main put this ahead of the
remaining census, because lane ex3-uct-tate-diagonal builds on it.

**Blobs reviewed** (rechecked at tip `f4702a191d`):
- `research/artifacts/uct-kk-norm-functor-2026-09-13-part1.md`, last changed `b562a1868` (the condition-2 correction);
- `research/artifacts/uct-kk-norm-functor-2026-09-13-part2.md`, `0c6f13664`;
- `kk-tensor-power-norm-functor-to-kk-zp`, its route `-proof`, and `o2-tensor-power-shift-is-rokhlin`, all `7e7da72e9`.

## 12.1 Verdicts

| item | verdict |
|---|---|
| part 1 §1: Koszul shift action, `σF_iσ^{-1} = F_{i+1}`, `J_1⋯J_p ⊆ K(Ẽ)` | PASS |
| part 1 averaging lemma (conditions 1--3 preserved, `σM'_iσ^{-1} = M'_{i+1}`) | PASS |
| part 1 Proposition 1 (norm of a cycle), `p = 2` | PASS |
| part 1 Proposition 1, odd `p` | **GAP**, §12.2 |
| part 1 Propositions 2--3, Theorem A | PASS for `p = 2`; for odd `p` inherits the gap |
| part 1 Corollary A (the shift on `O_2^{⊗p}` is Rokhlin) | PASS for `p = 2` (the flip on `O_2 ⊗ O_2`); odd `p` inherits |
| part 2 Theorem B (tensor powers of KK-equivalences) | PASS as a reduction to Theorem A for `N(C_f)`; so PASS for `p = 2`, conditional for odd `p` |
| part 2 Theorem C non-additivity check, `N(2) = 3 + χ` | PASS |

## 12.2 The gap: cross terms of `F̃²` for `p ≥ 3`

- **Where.** Proposition 1, second bullet: "The terms with `i ≠ j` cancel in pairs, since `F_iF_j + F_jF_i = 0` and the
  coefficients agree up to compacts."
- **The computation.** Modulo `K(Ẽ)`, moving each `M_j^{1/2}` past `F_i` is fine, since all `F_j` lie in `Δ`. That gives
  `F̃² ≡ Σ_i M_i F_i² + Σ_{i<j} [M_i^{1/2}, M_j^{1/2}] F_iF_j`.
  - The diagonal terms give `φ̃(ã)(F̃² − 1) ≡ Σ_i M_i φ̃(ã)(F_i² − 1) ≡ 0`, as the artifact says.
  - The cross terms vanish only if `[M_i^{1/2}, M_j^{1/2}] ∈ K(Ẽ)`, for example if `[M_i, M_j] ∈ K(Ẽ)`.
  - Multiplying by `φ̃(ã)` does not help: `F_iF_j` is compact in no slot.
- **Why conditions 1--3 do not give it.**
  - `Δ` is chosen before the partition, so condition 3 says nothing about `[M_i, M_j]`.
  - For `p = 2`, `M_2 = 1 − M_1`, so the commutator is `0` exactly. This is the external-product formula.
  - For `p ≥ 3`, the averaged `M'_i = p^{-1} Σ_k σ^k M_{i−k} σ^{-k}` needs `[M_a, σ^m M_b σ^{-m}] ∈ K` for all `a, b, m`.
    The slot induction cited for existence can put earlier operators into `Δ`. It cannot put in the shifted conjugates
    of the operator it is building.
  - Proposition 2.1's straight-line path between two partitions also mixes in cross commutators `[M_i, M'_j]`.
- **What is affected.** At odd `p`:
  - items 1--3 of `kk-tensor-power-norm-functor-to-kk-zp`, since Theorem B uses Theorem A on `N(C_f)` and Theorem C
    uses Theorem B;
  - `o2-tensor-power-shift-is-rokhlin`.

  At `p = 2`, everything reviewed here stands.
- **A likely repair**, not checked here.
  - Add condition (4), `[M_i, M_j] ∈ K(Ẽ)`.
  - Build the partition from exactly commuting slot operators: `M_i = f_i(X_1, …, X_p)`, where
    `X_i = 1 ⊗̂ ⋯ ⊗̂ X ⊗̂ ⋯ ⊗̂ 1` for one even quasicentral `X` on `E`.
    - These commute exactly, and `σM_iσ^{-1} = M_{i+1}` holds with no averaging.
    - Existence of `X` with conditions 2--3 is a p-slot technical theorem with commuting output. It needs a proof.
  - For Proposition 2.1, join two such partitions through a third one built with both in `Δ`.

## 12.3 Re-derived for `p = 2` and for the general mechanics

- **Koszul check.**
  - `σ(ξ ⊗ η) = (−1)^{|ξ||η|} η ⊗ ξ`.
  - So `σ(F ⊗ 1)σ^{-1}(ξ ⊗ η) = (−1)^{|ξ|} ξ ⊗ Fη`, which is `(1 ⊗̂ F)(ξ ⊗ η)`.
- **Proposition 1, `[F̃, φ̃(ã)] ∈ K`.**
  - `[M_i^{1/2}, φ̃(ã)] ∈ K` by condition 3 and functional calculus, with `Δ` self-adjoint.
  - `M_i^{1/2} j ∈ K` for `j ∈ J'_i`, since `j*M_i j ∈ K` and `T*T ∈ K` implies `T ∈ K`.
- **Proposition 1, `F̃² − 1`.** The diagonal terms are as above. For `p = 2` the cross term is `M_1^{1/2}M_2^{1/2}(F_1F_2 +
  F_2F_1) = 0`. Exact invariance under `σ` and the symmetrization `(F̃ + F̃*)/2` are fine.
- **Averaging.** `σ^k J'_{i−k} σ^{-k} = J'_i`, because `σ^k F_{i−k} σ^{-k} = F_i` and `σ` fixes `φ̃(A^{⊗p})` as a set.
  Conditions 1--3 are convex or linear.
- **Theorem A.**
  - `[id_A] = 0` gives a homotopy from `(A, id, 0)` to a degenerate cycle, hence to the zero cycle.
  - `N(h)` lives over `B^{⊗p} ⊗ C([0,1]^p)`. Restriction to the diagonal is equivariant, endpoint restriction of a
    partition is a partition, and Proposition 2.1 absorbs the choice.
  - `N` of the identity cycle has `F̃ = 0`, and `φ̃(A^{⊗p}) ⊆ K(A^{⊗p})`.
- **Theorem B.**
  - The cylinder `Z_f` has the splitting `s(b) = (0, t ↦ tb)`, and `C_f ≃_KK 0` by Puppe exactness.
  - `i^{⊗p}` is an equivariant homotopy equivalence, via `h_s(a, g) = (a, g(s·))` in every slot at once.
  - The filtration quotients are exact for `⊗_min`, because `id − s∘q` is completely bounded.
  - The splittings `⊕_S id^{⊗S} ⊗ s^{⊗S^c}` are already equivariant.
  - The `k`-subsets form a free `Z/p`-set for `0 < k < p` (`p` prime), so the middle layers are `Ind_1^G` of algebras
    with a `C_f` factor, hence `≃ 0`.
  - Downward induction over the triangles ends at `I_1 ≃ 0`. So `ev_1^{⊗p}` and then `f^{⊗p}` are equivalences.
  - Theorem A is used only for the top layer `N(C_f)`.
- **Standard inputs**, not re-read, as the artifacts flag:
  - the two-slot technical theorem;
  - exact triangles from equivariantly c.p.-split extensions;
  - Meyer's localization description of `KK`;
  - outerness of permutations on factors that are not type I.
- **Corollary A at `p = 2`.**
  - A factor state of type III gives a shift-invariant product state, so an inner flip would be inner on `M ⊗̄ M`. That
    forces `M` to be type I.
  - Contractibility plus pointwise outerness gives the Rokhlin property by item 2 of
    `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`. This review takes that node as given.
- **Theorem C non-additivity check.**
  - `N(2)` is `C → M_2 ⊗ M_2` with `Ad(flip)`, whose eigenvalues are `+1` three times and `−1` once. So
    `N(2) = 3 + χ`.
  - The power-operation formula `(n² + n)/2 + ((n² − n)/2)χ` gives `N(−1) = χ`, `N(4) = 10 + 6χ = N(2)²`.

## 12.4 Graph notes

- `kk-tensor-power-norm-functor-to-kk-zp` and `o2-tensor-power-shift-is-rokhlin` claim every prime.
- Until condition (4) is proved:
  - scope their ESTABLISHED status to `p = 2`;
  - for odd `p`, record Proposition 1 as an open partition lemma, and route the odd-`p` items through it.
- Owner notice sent to ex2-uct-norm-functor, and to the live consumer ex3-uct-tate-diagonal.

## 12.5 Addendum: the literature repairs odd p, and credit belongs to Nishikawa--Petrosyan

- **The import.** After this review, ex3-uct-tate-diagonal (`a830fde9f5`) imported
  `nishikawa-petrosyan-equivariant-power-functor`: Nishikawa--Petrosyan, arXiv:2509.15070v2. It also added a credit
  block to `kk-tensor-power-norm-functor-to-kk-zp`.
- **Checked on MSI.**
  - After Definition 5.13, verbatim: "For the separable ungraded G-C˚-algebras, it is a unique functor from KK_G to
    KK_{G≀ΩF} sending [φ] to [φ^{⊗̂Ω}] for any G-˚-homomorphism φ: A → B, as shown in Theorem 5.10."
  - Theorem 5.11 ("c.f. [Kas88, Theorem 1.4]") supplies the symmetric, essentially commuting partition.
  - The independence argument joins two partitions through a third that commutes with both, as §12.2 suggested.
  - Remark 5.12 records the gap of §12.2: "take a standard partition of unity ... and take their S_N-averages ... this
    will not work unless N = 2 ... we want a condition like [N'_1, w(N'_1)] ∈ K(E) for w ∈ S_3, which is not automatic
    from the standard construction".
  - Theorem 5.16 (gamma elements) is present.
- **Consequence.**
  - Items 1--3 of `kk-tensor-power-norm-functor-to-kk-zp` hold for every prime by citation: the case `G = 1`,
    `F = Ω = Z/p`, where item 1 follows from functoriality.
  - `o2-tensor-power-shift-is-rokhlin` then holds at every prime as well.
  - The GAP stays a gap in the lane's own Proposition 1, not in the claims.
- **Credit.** Items 1--3 are Nishikawa--Petrosyan's. What is new is items 4--5 and the Rokhlin corollary, as the node now
  records.
- **Graph.** The odd-p items should route through the import. Either add `nishikawa-petrosyan-equivariant-power-functor`
  to the requires of a citation route to the claim, or scope `kk-tensor-power-norm-functor-to-kk-zp-proof` to `p = 2`.
