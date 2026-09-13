# EX review, wave 2, part 7: weak-sofic targets and triangle persistence (2026-09-13)

Lane `ex-verify2-groups`. Index: `ex-review2-groups-2026-09-13.md`. Read at tip `0f57d3cdf`.

## 1. ex2-weak-sofic-affine-targets and ex2-weak-sofic-bounded-factors: all four PASS

**`hensel-covering-of-nilpotent-kernels-by-commutators`.** PASS.
- *The layer map.* `[g, γ] ↦ (g - 1)γ̄`. A functional vanishes on `Σ(g_i - 1)M_j` iff it is fixed by every `g_i`, so
  (F) is exactly surjectivity.
- *The correction step.* `[g, βγ] = [g, β] · β[g, γ]β^(-1)`. `β in K` acts trivially on `M_j`, and `M_j` is central in
  `K/K_(j+1)`, so the error moves one layer down. The number of commutators does not grow.
- *The covering form.* A factor `z in C_Q(K)` cancels, and `[P, β] = P · (βP^(-1)β^(-1)) in Cons_(2m)`.
- *The Singer seed.* On `Λ^k` with `1 <= k < n`, `(q-1) Σ q^(i_j) <= q^n - q^(n-k) < q^n - 1`, so no eigenvalue is `1`.

**`relator-width-over-transitive-abelian-extensions`.** PASS.
- *Case (a).* `γ_0 = [h, β_0] = h · (β_0 h^(-1) β_0^(-1)) in Cons_2 ∩ A` is nontrivial, and transitivity conjugates
  it onto every nonzero vector.
- *Case (b).* The normal closure `N` lies in `C_Q(A)`, and `u(a) = pα` with `p in Cons_(LK)`. So
  `[u(a), v(a)] = [p, v(a)] in Cons_(2LK)`, and the template gives `2JLK + J'`.
- *Corollaries.* `SL_n(q)` and `Sp_(2m)(q)` are transitive on nonzero vectors (Witt). The split lifts give the lower
  bound, and no complement is used.

**`simple-group-width-over-congruence-targets`.** PASS at the checked steps.

Part 1 artifact:
- *Lemma 1.1.* `θ_j` is well defined because `j + 1 <= k`. It is a homomorphism because `2j >= j+1`. Its image has
  trace 0, since `det = 1 + π^j tr Y`, and it is onto.
- *Lemma 2.1.*
  - `N(ζ)^(q-1) = 1`, and `(q-1)(q^(n-1) - 1) < q^n - 1`, so `C(σ) = F_(q^n)`.
  - Two conjugate tori meet in a subfield. A common subfield of prime degree is normalized.
  - For `n >= 3`, a transvection normalizing `B` would be `B`-linear. It fixes some `x != 0` in `H ∩ β^(-1)H`, so τ is
    trivial, but `rk(s-1) = 1` is not a multiple of `l`.
  - For `n = 2`, the normalizer has at most `2(q+1)` elements of determinant 1, fewer than `q(q^2-1)`.
- *Lemma 2.2.* For `Z ⊥ im Λ`, `σ^(-1)Zσ = Z + c·1`. Then `oc = 0` with `p ∤ o`, so `Z` is a common scalar.
- *Lemma 3.1 and Proposition 4.1.* As for the Hensel lemma above, applied to lifts of `σ_1, σ_2` inside
  `Z_T · Cons_(k_0)(h)`.
- *§5, cases S, B and P.* Checked. Case S: `ā_x = μ·1` forces `μ^n = 1`, so `a_x in Z_T K_1`, which is nilpotent.

Part 2 artifact (near-scalar residues):
- *Rank calculus (R1)--(R4).* Over a chain ring, submodules of `s`-generated modules are `s`-generated.
- *Lemma 2.1.* `ψ(gg') = ψ(g)ψ(g') + C_g B_(g')`, where `C_g` leaves the rank-`d_0` summand, with (b)--(d).
- *Lemma 3.1.*
  - The conjugators `diag(det d_i^(-1), 1, ...) ⊕ d_i` lie in `SL_n(R)`, reduce to 1, and are block diagonal.
  - The scalars cancel because the pattern's exponent sum is `e_u`.
  - The rank bound `K(u)(2l+2)d_0 + 2|u|d_0 + 2d_0` follows.
- *Lemma 4.1.* `im(g-1) <= W̃ + im[C  E_D]`.
- *Lemma 4.2(ii).* The `(U_b,U_b)` block is `γzβ' + δδ' = 1 + γ(z-1)β'`. The rows into `U_a` and the block out of
  `U_a` each have rank at most `2d_0`, so the total is at most `6d_0`.
- *Lemma 4.3.* By Smith normal form the common kernel has corank `<= f` and the image lies in a summand of rank
  `<= 2f`. The modular law gives `R^n = Ã ⊕ B̃`.
- *§5.*
  - `d' >= 2f >= 20d_0`, so `rk(h̄|Ā - 1) = 2t <= d'/4` equals `ρ`. Both branches give `2td' >= η''d'^2`.
  - The template identity `[P_uρ_u, P_vρ_v] = P_u([ρ_u,P_v] · P_v[ρ_u,ρ_v]P_v^(-1))P_u^(-1) · [P_u, P_vρ_v]` is
    re-derived from `[xy,w] = x[y,w]x^(-1)[x,w]` and `[y,zw] = [y,z] · z[y,w]z^(-1)`.

Item 3 (affine congruence):
- `[(t,h), (v,1)] = ((h-1)v, 1)`, and `(h-1)v` is unimodular when `h̄ != 1`.
- `SL_n(R)` is transitive on unimodular vectors, and `w = e_1 + (w - e_1)`.
- Otherwise the tuple lies in the `p`-group `A ⋊ K_1`.

Imports:
- `perfect-group-relator-width-over-nilpotent-groups`, `relator-width-over-nilpotent-by-locally-finite-groups`,
  `simple-group-relator-width-in-finite-simple-targets` and `simple-group-psl-width-is-finite-field-linear-soficity`
  already PASS in the backlog review.
- `liebeck-shalev-normal-subset-covering` is a literature import, not re-read.
- The near-scalar case is not computed, as the node says.

**`relator-width-survives-abelian-and-central-extensions`.** PASS.
- *(a).* Central factors cancel in commutators, giving `Cons_(2KL + L_0)`.
- *The spanning lemma.* `W^⊥` and `[A,Q]^⊥` are both the characters fixed by `Q`, so the orders agree. No
  coprimality is needed.
- *(b).* `<s_i>A ⊇ <a> = Q`, and `e_x = Π[γ_i, s_i] in Cons_(2n)`.
- *(c).* Normal generation in a finite nilpotent group is generation, because conjugates lie in `sΦ(B)`.

## 2. ex2-triangle-persistence: all six PASS

**`sl2-opposite-root-subgroups-codistance-inverse-sqrt-q`.**
- *Adjacency.* `v ~ w` iff `det(v,w) = 1`.
- *Gram matrix.* `MM^T = qI + J - (q-1)Π`, with spectrum `q^2` on constants, `1` on dilation-invariant functions of
  mean zero (dimension `q`), and `q` on `ker Π` (dimension `q^2-q-2`).
- *Singular values.* `1`, `q^(-1/2)`, `q^(-1)`.
- *Girth.* No 4-cycles. The three pairwise-independent vectors `e_1, e_2, e_1+e_2` give a 6-cycle, because
  `det(e_1+e_2, w) = 2 != 1`.

**`sl2-subfield-root-pair-girth-eight`.**
- Cycles correspond to alternating relations.
- *m = 2.* The `(1,1)` entry forces `a_1b_1 = 0`.
- *m = 3.* The `(1,2)` entry gives `a_1a_2b_1 = a_1 + a_2 + a_3`, whose left side is in `sk \ 0` and right side in
  `k`, while `sk ∩ k = 0`.

**`sl2-subfield-root-links-codistance-q8-q16`.** PASS; certificates rerun.
- *The inequality.* By vertex-transitivity, `σ_2^(2m) <= tr(T^m) - 1 = nW_(2m)/q^(2m) - 1`.
- *Rerun.* `sl2link.py` from main (md5 `684c61f0`), Sage 10.7 Python on MSI, one core, for `(q, s) = (8, g), (8, g^3),
  (16, g), (16, g^3)`. First certifying lengths `2m = 56, 48, 18, 18`, components 1, girth 10. Top singular values
  0.683135, 0.684017, 0.496284 and 0.494194 match `run1.out` and `run2.out`. Wall times 3 to 26 s.
- *Trust boundary.* This reproduces the code's exact walk counts; it is not an audit of the builder.

**`coset-graph-singular-values-bound-fixed-space-angles`** (route-established, no status line).
- `(Mf)(aH) = Σ_h f(ahK) = |H| R_H F`, so `T = R_H R_K R_H`.
- Peter--Weyl gives `σ_2 = max_(π != 1) ||P_(π^H) P_(π^K)||`.
- The isotypic decomposition and Cauchy--Schwarz give the Friedrichs bound, and `π^H ∩ π^K = 0` for `π != 1`, since
  `<H,K> = A`.

**`kassabov-subspace-angle-criterion`** (route-established). Theorem 1.2 and Observation 2.1 are present as quoted in
the arXiv:0911.1983v2 PDF. The Coxeter calibration is correct: the Tits Gram matrix is positive definite exactly for
the finite Coxeter groups.

**`triangle-of-groups-half-girth-structure`** (route-established).
- CCKW arXiv:2011.09276 Theorem 3.1 (i)--(v) is verbatim in the PDF.
- The claim's (iv) says the kernel is torsion-free, where CCKW's (iv) says "virtually torsion-free". The stronger
  form follows from (ii): a torsion element of `ker ψ` lies in a conjugate of some `G_(v_i)`, where `ψ` is injective.

## 3. Verdicts

| claims | verdict |
|---|---|
| weak-sofic affine targets (3), bounded factors (1) | PASS; congruence targets at the checked steps |
| triangle persistence (3 established, 3 route-established) | PASS; q8/q16 certificates rerun and matched |

With parts 5 and 6, every wave-2 census item has a verdict: 28 PASS, one already passed elsewhere, no FAIL, no GAP.
