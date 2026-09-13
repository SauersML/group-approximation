# Simple Kazhdan groups whose simplicity reads off the characteristic: the Grigorchuk groupoid

Lane `un-open-3` (UN swarm, open-ended), 2026-09-13. Status: complete written proofs, **unreviewed**. Imports read
verbatim from the arXiv TeX source of Clark–Exel–Pardo–Sims–Starling (CEPSS), arXiv:1806.04362
(`CEPSS_revision_Mar07_2019.tex`, fetched on MSI); quotes in `cepss-nonhausdorff-steinberg-simplicity-citation`.

## 0. Setting

- `X = {0,1}`, `G` the Grigorchuk group with its faithful self-similar action `(G,X)`, `𝒢 = 𝒢_(G,X)` the groupoid of
  germs of the tight action of `S_(G,X)` (CEPSS §"The Grigorchuk group"). The unit space is `X^ω` (Cantor, compact,
  infinite, Hausdorff). `𝒢` is ample and minimal, and effective because `(G,X)` is faithful (CEPSS, before
  `lem:ssgcalc`). `𝒢` is **not Hausdorff** (CEPSS, after eq. `eq:restrictions`).
- Basic compact open bisections `Θ((α,g,β), C(βη))`: germs of `βηw ↦ α(g·ηw) = α(g·η)(g|_η · w)`.
- `k` a field, `R_k = A_k(𝒢)` the Steinberg algebra (span of `1_B`, `B` compact open bisections, convolution).
- In `R_k` put `s_x = 1_(Θ((x,e,∅),X^ω))`, `s_x^* = 1_(Θ((∅,e,x),C(x)))` for `x ∈ X`, and `u_g = 1_(Θ((∅,g,∅),X^ω))`.

## 1. Theorem A: `A_k(𝒢)` is simple iff `char k ≠ 2`

**Proof.** CEPSS Theorem `thm:simple` (import (S)): for a second-countable ample groupoid with Hausdorff unit space,
`A_k(𝒢)` is simple iff `𝒢` is minimal, effective, and every nonzero `f` has support with nonempty interior. `𝒢`
is minimal and effective, so simplicity is equivalent to: **no nonzero singular element** (support with empty
interior).

*(char k ≠ 2 ⇒ simple.)* CEPSS prove "no nonzero singular element" for characteristic zero through three lemmas.
Characteristic enters in exactly one place, the last line of `lem:LCzero`. There one has
`f = Σ_(g∈{e,b,c,d}) c_g 1_(U_(g,m))`, whose support has empty interior iff the six equations hold:

```text
c_e + c_b = 0    c_c + c_d = 0
c_e + c_c = 0    c_b + c_d = 0
c_e + c_d = 0    c_c + c_b = 0
```

Over any field the first column gives `c_b = c_c = c_d = −c_e`. Then `c_c + c_d = −2c_e = 0`, so `c_e = 0` as
soon as `2 ≠ 0` in `k`, and all four vanish. So `lem:LCzero` holds verbatim for every field with `char k ≠ 2`.
- `lem:zeinterior` ("`f(z_e) ≠ 0` ⇒ `supp(f)` has nonempty interior") uses characteristic only by invoking
  `lem:LCzero` on the restriction `f|_(U_m)`. The other steps are `lem:basisISG`, [St, Lemma 4.14] and `lem:Ugm`, none
  involving the field.
- `lem:grigsingular` ("singular ⇒ zero") uses characteristic only through `lem:zeinterior`. Its other inputs
  (`lem:SupportElementBoundary`, [St, Lemma 4.14], `lem:ssgcalc`, `prop:singularideal`, convolution with bisections)
  are field-free.

So `lem:grigsingular` holds for `char k ≠ 2`, and the CEPSS proof of `thm:grigsimple`(1) ("Theorem `thm:simple`
plus Lemma `lem:grigsingular`") gives simplicity.

*(char k = 2 ⇒ not simple.)* CEPSS Corollary `cor:grigZ2notsimple` takes `f = Σ_g 1_(U_(g,1))`, all `c_g = 1`.
- Over any field of characteristic 2 the six equations hold (`1+1 = 0`), so `supp(f)` has empty interior.
- The proof of `lem:LCzero` gives `U_(g,m) \ (union of the other three) = {z_g}`, and any three of the four sets
  meet emptily. So `f(z_e) = 1 ≠ 0`.
- Hence `f` is a nonzero singular element, and `A_k(𝒢)` is not simple by (S).

CEPSS state the characteristic-2 case over `Z_2` and credit it also to Nekrashevych (IJAC 26 (2016), Example 4.5). The
extension to every characteristic-2 field is the same computation. ∎

**Novelty bound.** The odd-characteristic statement is an immediate reading of the CEPSS proof. It is likely recorded
in later literature on non-Hausdorff groupoid algebras (not checked: web search unavailable). Credit CEPSS and
Nekrashevych.

## 2. Theorem NH: simplicity modulo centre without Hausdorffness

**Statement.** Let `k` be a field and `𝒢` an ample groupoid (not necessarily Hausdorff) with compact, infinite,
Hausdorff unit space, such that `A = A_k(𝒢)` is simple. Then for `n ≥ 3` every normal subgroup of `EL_n(A)` is central or
all of `EL_n(A)`, and `S_n = EL_n(A)/Z(EL_n(A))` is an infinite simple group. If `k` is finite and `A` is finitely
generated as a ring, `S_n` has property (T).

**Proof.**
1. `A` is unital with `1 = 1_(𝒢⁰)` (the unit space is compact open). So two-sided `k`-algebra ideals are exactly
   two-sided ring ideals, and `A` is a simple ring (`IsSimpleRing`).
2. `A` has local annihilation by `steinberg-algebras-have-local-annihilation`. That node assumes only an ample
   groupoid with compact infinite unit space and states that no Hausdorffness is used. Its review
   (`un-review-2026-09-13-part1.md` §1) notes that the argument works for non-Hausdorff `𝒢`, because every
   `f ∈ A` is a finite combination of `χ_B`.
3. `local-annihilation-makes-projective-el-simple` (the Lean theorem
   `Pestov91.isSimpleGroup_elementaryGroup_quotient_center`, with exactly `3 ≤ card ι`, `IsSimpleRing R` and
   `LocalAnnihilation R`) gives normal subgroups central or everything, and `S_n` simple.
4. `S_n` is infinite. The unit space is an infinite compact totally disconnected space, so it has infinitely many
   pairwise disjoint nonempty clopens, and `A` is infinite. If `e_12(a) e_12(b)^(-1) = e_12(a−b)` were central, then
   `[e_12(a−b), e_23(1)] = e_13(a−b) = 1`, so `a = b`. Hence `e_12(A)` injects into `S_n`.
5. (T): `elementary-groups-over-fg-rings-have-property-t` (EJZ), plus quotients of (T) groups. ∎

## 3. Theorem B: the Grigorchuk elementary groups

Let `R_q = A_(F_q)(𝒢)` and `n ≥ 3`.

**(B1) `R_q` is a finitely generated ring.** The proof of CEPSS `lem:zeinterior` states: "By Lemma `lem:basisISG` and
[St, Lemma 4.14], we may assume each element of F is of the form Θ((α, g, β), C(βη))". So `R_q` is spanned by those
characteristic functions. As germs,

```text
Θ((α,g,β),C(βη)) = Θ((α(g·η), g|_η, βη), C(βη)) = Θ((α',e,∅),X^ω) · Θ((∅,h,∅),X^ω) · Θ((∅,e,β'),C(β'))
```

with `α' = α(g·η)`, `h = g|_η`, `β' = βη`. Since `1_B * 1_(B')= 1_(BB')` for bisections, we get
`1_B = s_(α') u_h s_(β')^*`, with `s_γ = s_(γ_1)⋯s_(γ_k)`. Also `u_g u_h = u_(gh)`, and `G = ⟨a,b,c,d⟩`. Hence `R_q` is
generated as a ring by `s_0, s_1, s_0^*, s_1^*, u_a, u_b, u_c, u_d` and one generator of `F_q` over `F_p`.

**(B2) A unital binary Leavitt family.**
- `s_x^* s_y = 1_(Θ((∅,e,x),C(x))·Θ((y,e,∅),X^ω))`. The composite of `w ↦ yw` with `xw' ↦ w'` is defined only when
  `x = y`, and is then the identity of `X^ω`. So `s_x^* s_y = δ_(xy) 1`.
- `s_x s_x^* = 1_(Θ((x,e,x),C(x))) = 1_(C(x))`, and `C(0) ⊔ C(1) = X^ω`, so `s_0 s_0^* + s_1 s_1^* = 1`.

**(B3) Nonsoficity, for every `q`.** `R_q` is a nontrivial countable `F_q`-algebra carrying a binary Leavitt family.
By `d-ary-leavitt-groups-nonsofic-over-finite-fields`, `EL_n(R_q)`, `GL_n(R_q)` and `R_q^×` are nonsofic.

**(B4) No nontrivial MF quotient, for every `q`.** With `s = s_0`, `t = s_0^*`: `ts = 1`, `1 − st = s_1 s_1^*`, and
`s_1^*(s_1 s_1^*) s_1 = 1`, so `1−st` is full. By `full-defect-ring-non-mf-at-rank-two` (tex Thm l.918 at rank two),
every homomorphism from `EL_n(R_q)` to an MF group is trivial (`n ≥ 2`).

**(B5) `q` odd: an infinite f.g. simple Kazhdan group with no MF quotient.** By Theorem A `R_q` is simple. The unit space
is compact, infinite and Hausdorff, so Theorem NH applies: `S = EL_n(R_q)/Z` is infinite and simple. (B1) with EJZ
gives (T), and (T) groups are finitely generated. A homomorphism `S → M` with `M` MF composes to one from `EL_n(R_q)`,
so it is trivial by (B4).
- *Remark, not proved here:* `S` is nonsofic if soficity lifts through the abelian kernel `Z` (Elek–Szabó,
  amenable-by-sofic). That import is not landed in this route.

**(B6) `q` even: not simple modulo centre.**
- By Theorem A the singular ideal `I = 𝒮(𝒢) ⊂ R_q` is nonzero. It is proper, since `supp(1) = X^ω` has nonempty
  interior.
- Let `E = E_n(R_q, I)` be the normal closure of `{e_ij(a) : a ∈ I}` in `EL_n(R_q)`.
- `E` is noncentral: for `0 ≠ f ∈ I`, `[e_12(f), e_23(1)] = e_13(f) ≠ 1`.
- `EZ ≠ EL_n(R_q)`. Otherwise the reduction `EL_n(R_q) → EL_n(R_q/I)`, which kills `E`, would have central image.
  But `R_q/I ≠ 0` and `EL_n(R_q/I)` is nontrivial and perfect for `n ≥ 3` (`e_ij(a) = [e_ik(a), e_kj(1)]`), so it
  is not abelian.
- Hence `EZ/Z` is a nontrivial proper normal subgroup of `EL_n(R_q)/Z`. ∎

**(B7) Amenable inside.** `g ↦ u_g` is an injective homomorphism `G → R_q^×`. A germ `[g,w]` is a unit only if `g` fixes a
neighbourhood of `w`, and a faithful `g ≠ e` moves some point. So the amenable, residually finite Grigorchuk group
sits inside a unit group with nonsofic elementary subgroups.

## 4. What is exotic, and where it stops

- **One groupoid, two characteristics.** For the same non-Hausdorff groupoid, the Kazhdan group `EL_n(A_(F_q)(𝒢))`:
  - is always nonsofic with no MF quotient;
  - is simple modulo centre exactly when `q` is odd.
  Simplicity of the group reads off `q mod 2`. The obstruction is the singular ideal, a characteristic-2 accident of the
  four germs `z_e, z_b, z_c, z_d`.
- **Profile.** On the approximation axes the odd-`q` groups match the Leavitt calibration (paradox side). The new
  features are non-Hausdorffness and the characteristic dependence. Theorem NH makes the reviewed simplicity theorem
  available for all self-similar groups whose algebras are simple.
- **Open.**
  - Is `EL_n(R_q/I)/Z` (`q` even) simple and Kazhdan? It is finitely generated. Simplicity of `R_q/I` is not decided
    here.
  - Which contracting self-similar groups have `A_(F_p)(𝒢)` simple exactly for `p` outside a finite set, and can that
    set be arbitrary?
