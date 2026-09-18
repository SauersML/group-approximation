# Referee report (gq-referee-a, proof-gap lens): the abelianized Aut/Out(F_n) extension virtually splits

**Reviewed:** `aut-out-free-abelianized-extension-virtually-splits` and its `-proof` (lane bh-outfn, 518dae5bd), read on
origin/main. The one input is item 1 of `aut-out-free-abelianized-extension-splits-rationally`: the crossed homomorphism
`h` with `h(ι_g) = (n−1)[g]`.

**Verdict: PASS** for items 1–3. There is one wording fix (W1) in the scope section. The recorded second proof, through
`F_n/γ_3F_n`, is marked as a check only and is not reviewed.

## The three points the author asked about
- **The finite-index homomorphism `Φ`.**
  - In `M ⋊ GL(M)` with `M = H/mH`, the product `(a,A)(b,B) = (a + Ab, AB)` matches
    `h(φψ) = h(φ) + φ_*h(ψ)`. So `Φ` is a homomorphism. ✓
  - `{0} × GL(M)` is a subgroup, since `(0,A)(0,B) = (0,AB)`, so `A_n = Φ^(−1)({0} × GL(M))` is a subgroup. Its index
    is at most `|M|`.
  - `h(ι_g) = m[g]` puts `Inn(F_n)` in `A_n`.
  - `h(φι_g) = h(φ) + φ_*(m[g]) ≡ h(φ) mod mH`, so `A_n` is a union of `Inn`-cosets. Hence `π^(−1)(Γ_n) = A_n`, and
    `Γ_n` has finite index. ✓
- **The complement argument (items 5–6).**
  - `H` is torsion-free, so `k = h/m` is well defined on `A_n`, and it is a crossed homomorphism.
  - `K_n = k^(−1)(0)` is a subgroup.
  - *Item 5.* `k(ι_g) = [g]` vanishes exactly on `g ∈ [F_n,F_n]`. Since `Z(F_n) = 1`, `Inn(F_n) ≅ F_n`, and so
    `K_n ∩ Inn = Inn([F_n,F_n])`. ✓
  - *Item 6.* For `φ ∈ A_n`, choose `g` with `[g] = −φ_*^(−1)k(φ)`. Then `k(φι_g) = k(φ) + φ_*[g] = 0`. ✓
  - *The complement.* `Inn([F_n,F_n])` is normal in `Aut(F_n)`, because `[F_n,F_n]` is characteristic. So
    `K_n/Inn([F,F]) ≅ K_nInn/Inn = A_n/Inn ≅ Γ_n`. This is a complement to `H = Inn/Inn([F,F])` in
    `A_n/Inn([F,F]) = π̄^(−1)(Γ_n)`. So the restricted extension splits, and `c|_(Γ_n) = 0`.
  - For `n = 2`, `M = 0`, so `A_2 = Aut(F_2)`. ✓
- **The scope.** The proof uses only `n ≥ 2` and the landed cocycle identity, as claimed. One sentence in "What this
  settles" overstates, though (W1).

## Wording fix
- **W1 ("a virtual section exists exactly when this extension splits over a finite-index subgroup of `Γ_n`").** Only
  one direction is clear.
  - *Clear.* A splitting of `1 → [F_n,F_n] → K_n → Γ_n → 1` over a finite-index `Γ'` is a virtual section of
    `Aut → Out`.
  - *The converse is not shown.* A virtual section `s` over `Γ'` lands in `K_n` only if the crossed homomorphism
    `κ = k∘s : Γ' ∩ Γ_n → H` vanishes.
    - Modifying `s` to `s'(γ) = ι_(c(γ))s(γ)` needs a nonabelian crossed homomorphism `c : Γ'' → F_n` with
      `[c(γ)] = −κ(γ)`. That is, `−κ` must lift from `H` to `F_n`.
    - Such a lift need not exist, and the zero set of `κ` need not have finite index.
  - Suggested text: "a splitting of this extension over a finite-index subgroup gives a virtual section. Conversely,
    a virtual section gives such a splitting when its Fox crossed homomorphism `k∘s` vanishes on a finite-index
    subgroup, or lifts to `F_n`."
