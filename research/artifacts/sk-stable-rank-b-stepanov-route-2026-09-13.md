# sk-stable-rank-b: the stable-rank route, and a shorter route through Stepanov (2026-09-13)

- Lane: sk-stable-rank-b.
- Status: UNREVIEWED; review requested from sk-referee-1.
- Line numbers refer to `$SK/manuscript-disk-1646.tex` (md5 7b3dc4ec92b4581553bc0dc2b0edcb99).

## 1. Summary
- **Stable-rank shortcut.** It would replace the tower proof (l.154-227) by a citation. It needs `sr(R) ≤ 2` for
  `R = LC(X,F_q) ⋊ Z`: Bass 1964, Theorem 4.2(e), or Vaserstein 1981, Theorems 1 and 4 (§2.2, §2.3). That bound is OPEN
  here; the attempts are in `subshift-crossed-product-ring-has-bass-stable-rank-at-most-two`.
- **Stepanov route.** It needs no stable rank. For a simple ring, Stepanov's Theorem 4.4 only asks that each
  `a ∈ GL_n(R)` have a nonzero column `α` with `α_i = (aα)_j = 0`.
  - In `LC(X,K) ⋊ Γ` with `Γ` amenable, any two elements `p, q` satisfy `pr + qs = 0` with `(r,s) ≠ 0`, by a dimension
    count over one cylinder. Taking `α = (0, r, s)^T` for `p = a_12`, `q = a_13` gives (b).
  - So l.154-227 (74 lines) can become about 20 lines, citing a theorem the note already cites.

## 2. Sources (read by this lane)

### 2.1 Stepanov
A. V. Stepanov, *On the normal structure of the general linear group over a ring*, J. Math. Sci. 95 (1999) 2146-2155
(Zap. POMI 236 (1997)). The Springer page images (MSI `/projects/standard/hsiehph/sauer354/un-stepanov/stepanov.pdf`,
744600 bytes) were copied and pp. 2146-2153 read locally. This is a second independent reading; the first is
`un-stepanov-credit`.
- §1.1: "x^y = y^{-1}xy the conjugate of x by y".
- §1.4: "Let R be an associative ring with 1 ... We always assume that n ≥ 3."
- §1.5:
  - "The kernel of the homomorphism ρ_I is denoted by GL(n,R,I) ... The inverse image of C(n,R/I) under the reduction
    homomorphism ρ_I is denoted by C(n,R,I) and is called the full congruence subgroup of level I."
  - "The relative elementary subgroup of level I is the group E(n,R,I) = ⟨t_ij(ξ) | ξ ∈ I, 1 ≤ i ≠ j ≤ n⟩^{E(n,R)}."
- §1.6 (p. 2148):
  - "(3) for any subgroup H ≤ GL(n,R) normalized by E(n,R), there exists a unique ideal I ≤ R such that
    E(n,R,I) ≤ H ≤ C(n,R,I);"
  - "We say that the normal structure of the general linear group is standard if parts (1), (2), and (3) hold."
- Theorem 4.4 (pp. 2151-2152): "Assume that for any proper two-sided ideal I in R, the following conditions hold:
  (a) [GL(n,R,I), E(n,R)] = E(n,R,I); (b) for any a ∈ GL(n,R), there exist b ∈ E(n,R/I) and α ∈ (R/I)^n (α ≠ 0) such
  that α_i = (u^b α)_j = 0 for some i, j ∈ {1,…,n}, where u = ρ_I(a) is the image of a in GL(n,R/I). Then the normal
  structure of GL(n,R) is standard."
- The proof ends (p. 2152): "The contradiction shows that a is central. Thus, F is contained in the center of GL(n,R)
  and H ≤ C(n,R,I)." What it proves is part (3) for every `H` normalized by `E(n,R)`, and part (3) is all that is used
  below.
- How (b) is used, checked line by line:
  1. Set `c = a^b`, `β = cα`, and `d = c t_{*i}(αλ) c^{-1} t_{*i}(−αλ) = (e + βλc'_{i*}) t_{*i}(−αλ) ∈ F`.
  2. `α_i = 0` and `β_j = 0`, so row `j` of `d` equals the unit row off column `i`.
  3. Lemma 4.1 then makes `d` central, and Lemma 4.3 contradicts the choice of an entry `ξ` of `β` outside `I^⊥(c)`.
  4. For simple `R` with `H` containing no nontrivial transvection, the associated ideal is `0`. A noncentral `a ∈ H`
     is not scalar (a noncentral scalar `λI` gives the transvection `[λI, t_12(ξ)] = t_12(λξλ^{-1} − ξ)`). So `I(a) = R`
     and `I^⊥(a) = 0`, and (b) is applied to `R` itself.
- Lemmas 4.1 and 4.3, as quoted in `stepanov-linear-dependence-standard-normal-structure`, agree with p. 2151.

### 2.2 Vaserstein
L. N. Vaserstein, *On the normal subgroups of GL_n over a ring*, LNM 854 (1981), p. 456 (page image, MSI
`/projects/standard/hsiehph/sauer354/un-stepanov/vaserstein.pdf`).
- "We write sr(A) ≤ n, if for any b_1,…,b_{n+1} in A satisfying Σ_{i=1}^{n+1} A b_i = A there exist c_i in A such that
  Σ_{i=1}^{n} A(b_i + c_i b_{n+1}) = A."
- "THEOREM 1 (H. Bass [1, 2]). Let sr(A) ≤ n − 1 and n ≥ 3. Then (2) a subgroup H of GL_n A is normalized by E_n A if
  and only if, for a unique ideal B of A, the image of H in GL_n A/B lies in the center and H ⊃ [E_n A, E_n B]."
- "THEOREM 4. Suppose that n ≥ 3 and for every maximal ideal D of the center C of A there exists a multiplicative set
  S ⊂ C − D such that sr(S^{-1}A) ≤ n − 1. Then (2) holds."
- When the centre is a field, `D = 0`, `S ⊆ C^×`, and `S^{-1}A = A`. So Theorem 4 at `n = 3` needs exactly
  `sr(A) ≤ 2`.

### 2.3 Bass
H. Bass, *K-theory and stable algebra*, Publ. Math. IHES 22 (1964), §4 (numdam PDF, pdftotext on MSI, OCR quoted with
light repair).
- "we say n defines a stable range for GL(A) if, for all r > n, given a = (a_1,…,a_r) unimodular in A^r, there exist
  b_1,…,b_{r−1} in A such that (a_1 + b_1 a_r, …, a_{r−1} + b_{r−1} a_r) is unimodular in A^{r−1}".
- "Examples. — If A is a semi-local ring, then n = 1 defines a stable range. If A is a Dedekind ring n = 2 works."
- "Theorem (4.2). — Suppose n defines a stable range for GL(A). ... For r > max(n, 2): ... e) If H ⊂ GL(r, A) is
  normalised by E(r, A), then, for a unique ideal q, E(r, A, q) ⊂ H and the image of H in GL(r, A/q) lies in the
  center."
- So `r = 3` needs `n ≤ 2`, i.e. `sr(A) ≤ 2`, consistent with Vaserstein's Theorem 1.

### 2.4 Ara–Pardo
P. Ara, E. Pardo, *Stable rank of Leavitt path algebras*, arXiv:math/0609354 (text on MSI).
- "Theorem 2.8. Let E be a row-finite graph. Then the values of the stable rank of L(E) are: (1) sr(L(E)) = 1 if E is
  acyclic. (2) sr(L(E)) = ∞ if there exists H ∈ H_E such that the quotient graph E/H is nonempty, finite, cofinal,
  contains no sinks and each cycle has an exit. (3) sr(L(E)) = 2 otherwise."
- p. 1: "if E is a graph such that no cycle has an exit and E contains some cycle, then the stable rank of C*(E) is 1
  ... but the stable rank of L(E) is 2 by Theorem 2.8."
- This is the calibration showing that C\*-algebraic stable rank one does not transfer to algebraic rings.

## 3. Pair dependence
Stated and proved in `amenable-crossed-products-meet-stepanov-condition-b(-proof)`. The `Z` case as it would
appear in the note:
1. Let `w` bound the exponents of `p, q`, and put `h = 2w+1`.
2. Choose a nonempty clopen `U` on which every coefficient `f` of `p` and `q` has `f∘T^m` constant for `|m| ≤ 3w`.
3. For `ρ ∈ F^h` put `r_ρ = Σ_{0≤j<h} ρ_j u^j e_U`.
4. From `f u^m = u^m (f∘T^m)` we get `p r_ρ = Σ_{−w≤m≤3w} (Pρ)_m u^m e_U` for an `(h+2w)×h` matrix `P`, and likewise
   `q r_σ` with a matrix `Q`.
5. Since `2h > h+2w`, some `(ρ,σ) ≠ 0` has `Pρ + Qσ = 0`. Take `r = r_ρ` and `s = r_σ`.

Minimality and aperiodicity are not used.

## 4. The note's theorem through Stepanov
For `R = LC(X,F_2) ⋊ Z` and `G = EL_3(R)`:
1. `R` is simple with `Z(R) = F_2` (l.102-113), and `Z(G) = 1` (l.114-116).
2. Condition (a) holds trivially.
3. Condition (b) follows from §3 applied to `a_12, a_13`.
4. Stepanov then gives: every subgroup of `GL_3(R)` normalized by `G` is central in `GL_3(R)` or contains `G`.
5. A nontrivial normal `N ⊴ G` is not central, since it would lie in `Z(G) = 1`. So `N = G`.

Not needed any more: the partition sentence (l.80-82), the tower rings `B_m(U)` and (eq:absorb), the commutator
`k = [g,h]`, the finite simple groups `GL_d(F_2)`, and the level ideal `I_N` (l.223-227). The Cairn route into
`subshift-elementary-group-is-simple-modulo-centre` covers all `q`.

## 5. Model tests
- `K[u^{±1}]` (one-point `X`): pair dependence with `r = q`, `s = −p`. It is not simple, and Stepanov needs (a) for
  every proper ideal, which for commutative rings is Suslin's theorem. Only the simple case is used here.
- `M_m(D)`: (b) holds (`division-rings-satisfy-stepanov-b-not-local-annihilation`); consistent.
- Leavitt families (paradoxical crossed products, `L_K(1,2)`): pair dependence fails for `(s_0, s_1)`. The group is not
  amenable and the count needs `|SF| < 2|F|`. The Steinberg criterion (local annihilation) still covers them, so the
  two routes do not coincide.
- The hypothesis "Γ amenable" is used exactly once, in the Følner count. A trivial check: for `F_2` acting on its
  boundary, `|SF| ≥ 2|F|` for `S` the generators and their inverses, and item 1 is false there.

## 6. What this changes beyond the note
Whenever `LC(X,K) ⋊ Γ` is simple with `Γ` amenable, every subgroup of `GL_n(R)`, `n ≥ 3`, normalized by `E_n(R)` is
central in `GL_n(R)` or contains `E_n(R)`. This is a GL-level sandwich. It covers:
- the `Z^d` subshifts of `free-minimal-subshift-elementary-groups-are-simple-kazhdan`;
- all fields and all `n ≥ 3`.
The claim node is landed separately once its ring-simplicity input is wired.
