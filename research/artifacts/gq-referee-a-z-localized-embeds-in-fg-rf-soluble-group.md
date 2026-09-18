# Referee report (gq-referee-a, proof-gap lens): the Euler lamplighter

**Reviewed:** `z-localized-embeds-in-fg-rf-soluble-group` and its route `-proof` (lane gq-infinite-primes,
4cd432d26), read on origin/main.

**Verdict: PASS for parts 1, 2, 4 and 5.** In part 3, the lower bound "at least 3" rests on
`fg-metabelian-groups-have-roots-at-finitely-many-primes`, which I have not reviewed. The upper bound "at most 3"
is immediate.

## 1. `H ≅ Z ≀ Z`
- **The conjugates.** `β_k f_j = (1 + l(j−k)) f_j`, so the `β_k` are diagonal and commute.
- **Independence.**
  - Suppose `∏ β_k^{n_k} = 1`. Then `∏_k (1 + l(t−k))^{n_k}`, as a rational function of `t`, equals 1 at every
    integer, hence identically.
  - The factors `lt + (1 − lk)` are pairwise non-associate linear polynomials, with roots `k − 1/l`.
  - Unique factorization then gives `n_k = 0` for all `k`.
- **The semidirect structure.** `x β_k x^{-1} = β_{k−1}`, and no nontrivial power of `x` is diagonal. So
  `H = (⊕_k Z β_k) ⋊ ⟨x⟩`.

## 2. Generation
- **The orbit of `f_0`.** Conjugation in `M ⋊ H` gives `h f_0 h^{-1} = h(f_0)`. So `⟨f_0, x, β⟩` contains the
  `Z`-span of the `H`-orbit of `f_0`.
- **Denominators `≡ 1 (mod l)`.** That span contains `β_k^{∓1} f_0 = (1 − lk)^{∓1} f_0`, so it contains
  `(1/m) f_0` for every `m ≡ 1 (mod l)`.
- **All of `Z_(l)`.** For `l ∤ b`, `1/b = b^{l−2}/b^{l−1}`, and `b^{l−1} ≡ 1 (mod l)`. So `Z_(l) f_0` lies in the
  span.
- **All of `M`.** Shifting by `x` gives every `Z_(l) f_j`, hence all of `M`.

## 4. Residual finiteness
- **The quotient module.** Let `N` be a multiple of `l^{r−1}`. Then `β̄` is well defined on
  `M_{r,N} = ⊕_{j ∈ Z/N} (Z/l^r) f_j`, because `lj mod l^r` depends only on `j mod l^{r−1}`.
- **The quotient map.** `π` is surjective and equivariant for `x^{±1}` and `β^{±1}`. So `h ↦ h̄` is a
  well-defined homomorphism: two words for the same `h` agree on `π(M) = M_{r,N}`.
- **Separating `(m, h) ≠ 1`.** Every `h` has the form `x^a · diag(d_j)`.
  - If `a ≠ 0`, take `N > |a|`.
  - If `a = 0` and some `d_j ≠ 1`, take `r` large enough that `d_j − 1 ≢ 0 (mod l^r)`.
  - If `h = 1` and `m ≠ 0`, take `N` larger than the support of `m`, and `r` large.
- Correct.

## 5. Algorithms
- **Normal form.** `h` is given by `(a, (n_k))`, and this pair is unique by the independence in §1. `m` is a
  finitely supported vector with rational coefficients.
- **Computability.** Products are computable, because the diagonal entries are explicit rational functions of `j`.
  So the word problem is solvable.
- **Effective RF.** A search over pairs `(r, N)` with `l^{r−1} | N` terminates for each `w ≠ 1`, by §4, and
  returns an explicit finite quotient in which `w` survives. Correct.
