---
rg: 2
id: khanh-ara-cortinas-hypotheses-hold-for-leavitt-tensor-hosts
kind: claim
title: Checked at source, every hypothesis of the Khanh and Ara--Cortiñas inputs holds for R = L_p ⊗ L_p over every prime field, so the fp-simple hosts rest only on those published or preprint theorems and on repository steps checked here
distinct_from:
  leavitt-tensor-hosts-acyclic-steinberg-and-fp: that states the transferred Khanh criteria for B ⊗ L conditionally; this checks, against the source texts, that each hypothesis they need holds for B = L_p, and records which trust remains.
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that is the literature import of K_*(L ⊗ L) = 0; this re-reads it at source for every prime field and places it in the full chain.
  prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre: that is the prime-field host theorem; this is the hypothesis audit for its instance B = L_p, including the odd-p modifications.
requires:
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - ara-cortinas-leavitt-tensor-k-theory-vanishes
  - prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
---

**ESTABLISHED as a source audit** (bh-free-26, 2026-09-18, by hand; not independently
reviewed). Sources were read in full at the cited places:
- Khanh, arXiv:2609.08428v1, TeX at `gq/src/on/2609.08428/khanh.tex`, Sections 2--6.
- Ara--Cortiñas, arXiv:1108.0352v3 (PDF, 1 Dec 2011), pp. 1 and 8--9.

## Statement

Let `p` be prime, `L_p = L_(F_p)(1,2)`, and `R = L_p ⊗ L_p`. Every hypothesis of every imported
statement used by `leavitt-square-unit-group-is-fp-simple-and-acyclic` (`p = 2`) and by
`prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` with `B = L_p` holds for `R`.

After this audit, finite presentation and simplicity of `R^x / F_p^x` rest only on the following.

- **(T1) Literature theorems, used as stated.**
  - Ara--Cortiñas Lemma 6.1 and Proposition 6.2 (published).
  - Ara--Brustenga--Cortiñas Theorem 7.6, through Proposition 6.2.
  - Khanh Theorems 2.2 and 5.1 and Lemmas 2.3, 2.4 and 5.2 in their general forms. His
    `L`-specific Lemma 4.1 and Propositions 3.2 and 4.2 are redone for `R` in items 3--5.
    Khanh is an arXiv preprint of 8 Sep 2026, not refereed.
  - The Menal--Moncasi GE remark, Voronetsky §4 Proposition 1, and Krstić--McCool Theorem 3.
- **(T2) Repository steps.** Each was re-checked here by hand and is listed in the audit table:
  - the division lemma over `B ⊗ L`;
  - the odd-`p` forms of Khanh's Lemma 2.3 and Theorem 5.1;
  - the centre.
- **(T3) Simplicity mod centre.** The Lean root-detection theorems for arbitrary rings, applied
  on paper (`central-simple-leavitt-tensor-simplicity-proof`). Their hypotheses were checked:
  - `hdiv` is item 3 below;
  - the Leavitt family comes from the second factor;
  - `hcentral` holds for `p = 2`, and holds modulo `F_p^x` for odd `p`.

  The Lean builds were not re-run, since running code is not allowed in this lane.

So the "conditional on imported criteria" qualifier of the host nodes now means exactly this:
trust in (T1), and in the unreviewed repository steps (T2) and (T3). None of their hypotheses
is open.

## Audit table (`R = L_p ⊗ L_p`, `B = L_p` the first factor)

1. **`K_*(R) = 0`.**
   - *Source:* AC p. 8, Lemma 6.1: "Let E be a finite graph. Then L(E) is regular
     supercoherent." AC p. 9, Proposition 6.2: "Let R be regular supercoherent. Then the
     algebraic K-theories of L_2 and of L_2 ⊗ R are both trivial." The paper works over an
     arbitrary field `k` (abstract), and the proof writes `L_2 ⊗ R = L_R(E)` and applies ABC
     Theorem 7.6.
   - *Hypothesis for `R`:* the second input `L_2 = L_(F_p)(E)` for the rose `E` with two petals,
     a finite graph. So it is regular supercoherent, and `K_i(L_p ⊗ L_p) = 0` for all
     `i ∈ Z`, for every `p`.
2. **`A^2 ≅ A`** (Khanh Theorem 2.2). This comes from the second factor:
   `a ↦ (t_0 a, t_1 a)` with inverse `(x, y) ↦ s_0 x + s_1 y`.
3. **Strong division: every `x ≠ 0` has `y x z = 1`.**
   - Khanh's Lemma 4.1, with coefficients in `B`, gives a right multiplier `x_1` and nonempty
     words `η_i` with `η_i^* a_i x_1 = c_i ⊗ 1`, `c_i ≠ 0`. The steps are: collect identical
     words, separate the lengths `j(L+1)`, and append `e^M f`. These are prefix arguments
     and never use `F_2` coefficients.
   - `B` is simple, so `Σ_k y_(ik) c_i z_(ik) = 1`. With distinct words `β_(ik)` of one
     length, put `Z = Σ z_(ik) ⊗ β_(ik)`, `Y_i = Σ_k y_(ik) ⊗ β_(ik)^*` and `u_i = Y_i η_i^*`.
     Then `u_i a_i (x_1 Z) = 1`.
   - Single `x`: this is `hdiv`. `B ⊗ L` is not a division ring, so it is purely infinite
     simple.
4. **Nonzero free kernels** (Khanh Proposition 4.2). For `y = (c_i ⊗ 1) Z` we have
   `Y_i y = 1`, so `R = yR ⊕ ker Y_i ≅ R ⊕ ker Y_i`. Then
   `ker u_i = η_i ker Y_i ⊕ ker η_i^* ≅ ker Y_i ⊕ R^(|η_i|) ≅ ker Y_i ⊕ R ≅ R`.
   - No Ara--Goodearl--Pardo cancellation is needed.
   - `ker η_i^* ≠ 0` because `|η_i| >= 1`.

   So the frame complexes `X_r(R)` are highly connected and `|X_4(R)|` is simply connected,
   with Khanh's cone argument verbatim.
5. **Standard inclusions are zero on homology** (Khanh Proposition 3.2).
   - The compression `c(u) = e u e^* + f f^*`, the unit `w`, and
     `w c(u) w^(-1) = c(c(u))` use only the Leavitt identities of the second factor.
   - `H_n(GL_∞(R)) = 0` follows from item 1 through the plus construction.
6. **Scalar homology at odd `p`** (Khanh Lemma 2.3, whose source is `F_(2^m)`).
   - `H_j(V; Z)` of an `F_p`-space is killed by `p` for `j > 0`: `Z --p--> Z` is null-homotopic
     after multiplying by `p`.
   - `H^*(V; F_p) = Λ(V^*) ⊗ S(βV^*)` naturally, so the weights on `H_j` are sums of `k <= j`
     powers `p^a` mod `p^m - 1`.
   - Carrying (`p` counters at position `a` become one at `a+1`, cyclically) keeps the residue.
     It ends with fewer than `p` counters at each position and at least one counter in total.
     The total is still at most `k < m`, so the digits are not all `p - 1`. The sum therefore
     lies in `[1, p^m - 2]`, and it is nonzero for `0 < j < m`.
   - The norm kills nontrivial characters, and `p^m - 1` is prime to `p`, so averaging is exact
     on `p`-primary modules.
   - `F_(p^m)` embeds in `R` through `R ≅ M_m(R)`.
7. **Steinberg criterion at odd `p`** (Khanh Theorem 5.1, whose source assumes characteristic 2).
   - Replace `τ = (12)` and `h = (23)` by the Tits lifts `τ'`, `h'`, the images of
     `W = X_12(-1) X_21(1) X_12(-1)` and `W_23`. Then `τ' b_1 = b_2`, and `τ' h' τ' = h' τ' h'` as
     matrices.
   - Khanh's path computations need only `g b_1 = b_2` for the transporter. So Brown's
     presentation holds with `η'(k) = τ' k τ'^(-1) ∈ J`, and `η'(k(a,b,H)) = k(-b, a, H)`.
   - In `St_n`, `W X_1j(c) W^(-1) = X_2j(c)` and `W X_2j(c) W^(-1) = X_1j(-c)`, from the
     Steinberg relations. The two braid words have the same matrix, hence the same action
     on generators, so `z = (W_23 W W_23)(W W_23 W)^(-1)` is central with `φ(z) = 1`.
   - `ψ(T) = W z` satisfies both relations and gives a surjective section. For `p = 2`,
     `z = 1`, and this is Khanh's proof.
8. **GE and perfectness** (Khanh Lemma 5.3). Strong division (item 3) is the hypothesis of the
   Menal--Moncasi remark. Perfectness of `R^x` comes from acyclicity (items 5--6 in Khanh's
   Theorem 2.2), and then `W(u)W(-1) = diag(u, u^(-1))` puts the diagonals in `E_m`.
9. **Finite presentation of the ring.** `R` is generated by `e, f, s, t, e', f', s', t'` with
   relators:
   - `p`;
   - the six Leavitt relators of each copy;
   - the sixteen commutators `[x, x']`.

   So Krstić--McCool Theorem 3 presents `St_5(R) ≅ GL_5(R) ≅ R^x`.
10. **Centre.** `Z(L_p ⊗ L_p) = F_p ⊗ F_p = F_p` (`leavitt-center-is-coefficient-field` for
    each factor, and central ⊗ central). `F_p^x` is finite, so `R^x / F_p^x` is finitely
    presented.

## Beyond `B = L_p`

Items 2--10 use only that `B` is:
- a finitely presented ring;
- a central simple `F_p`-algebra;
- such that `K_*(B ⊗ L_p) = 0`.

AC Proposition 6.2 gives the last condition whenever `B` is regular supercoherent. That holds
for every Leavitt path algebra of a finite graph (AC Lemma 6.1). So the same audit covers
`B = L_(F_p)(E)` for every finite graph `E` whose Leavitt path algebra is simple and central.
The centre of a simple unital Leavitt path algebra is the coefficient field (Aranda
Pino--Crow 2011; cited, not read here).

## Master-route form (gate G3r)

**Corollary.** Let `B` satisfy three conditions:
- it is a finitely presented ring;
- it is a simple `F_p`-algebra with centre `F_p`;
- `K_1(B ⊗ L_p) = K_2(B ⊗ L_p) = 0`.

Then `(B ⊗ L_p)^x / F_p^x` is finitely presented and simple, and it contains `B^x` and every
`GL_n(B)`. The trust is the same as (T1)--(T3) above.

`B` may be an algebraic crossed product `C(X, F_p) ⋊ Λ` once it is simple with centre `F_p`.

*Why only `K_1` and `K_2`.* The audit items use the `K`-theory hypothesis at two points only.
- Item 5 needs `H_n(GL_∞(R)) = 0` for `n <= 2`. `BGL(R)^+` is an H-space with `π_1 = K_1` and
  `π_2 = K_2`, so Hurewicz gives this from `K_1 = K_2 = 0`.
- Khanh's Theorem 2.2 induction, run up to degree 2, gives `H_1 = H_2 = 0` for every `GL_r(R)`.
  That is all item 7 (`N_3 = [S_3, N_3]`) and item 8 (perfectness) use.

The other items use only the three listed properties of `B`. Item 10 becomes
`Z(B ⊗ L_p) = Z(B) ⊗ F_p = F_p`.

*The gate itself.* By `leavitt-tensor-k-theory-is-carried-by-nil-groups`, the hypothesis
`K_1 = K_2 = 0` holds as soon as `B ⊗ L_p` is `K_1`- and `K_2`-regular. So the ring side of the
master route needs Nil-vanishing for `B ⊗ L_p`, and no further `K`-theory computation.

## Lesson for general BH

Once its hypotheses are audited, the Khanh machine is a **general host theorem with one
homological input**. For a finitely presented central simple `F_p`-algebra `B`, the group
`(B ⊗ L_p)^x / F_p^x` is finitely presented and simple as soon as `K_*(B ⊗ L_p) = 0`. The
remaining steps are:
- word reduction, from the second factor;
- GE, Steinberg comparison and Krstić--McCool, which are ring-general.

Ara--Cortiñas supply that input for every regular supercoherent `B`. So the Boone--Higman
question for inputs linear over `B` reduces to one algebraic question: which finitely
presented central simple algebras containing the input are regular supercoherent? This is
the precise reason the tensor-power case `d >= 3` needed a separate `K`-theory claim.

## Referee (bh-ref-misc, 2026-09-18): source match with Khanh's preprint; PASS, with one correction to the trust classification

**Credit.** The ring-side finite presentation and acyclicity of every Leavitt-tensor host in this
graph comes from Huynh Viet Khanh, *General linear and Steinberg groups over the Leavitt algebra
`L_(F_2)(1,2)`*, arXiv:2609.08428v1 (8 Sep 2026). The graph uses:
- his acyclicity criterion (frame complexes with Quillen scalar weights);
- his Steinberg comparison criterion via Brown's presentation;
- his reduction of finite presentation to Krstić–McCool.

The repository steps are transfers of his arguments. They are not independent proofs.

**Source.** I read the v1 e-print (the only version on arXiv on 2026-09-18), TeX
`hvkhanh_general_linear_L_1,2_.tex` (sha256 `91d3f540…`, 761 lines, fetched on MSI to
`/scratch.global/sauer354/bhrefmisc/khanh/`), §§2–6 in full. What it proves, with its hypotheses:

| Khanh | Statement at source | Hypotheses at source |
|---|---|---|
| Thm 2.2 (`thm:acyclicity-criterion`) | `H_n(A^x) = 0` for all `n > 0` | `A` is a nonzero unital `F_2`-algebra (section convention, l.95); `A² ≅ A`; standard inclusions `Γ_(n+2) → Γ_(n+3)` are zero on `H_n`; `H̃_i(X_r(A)) = 0` for `i ≤ r−3`, `r ≥ 4` |
| Lem 2.3, 2.4 | Quillen weights; `2^n K_n = 0`, `(K_n)_C = 0` | characteristic 2 (`F_(2^m)`, 2-primary torsion, odd `d`) |
| Prop 3.2, Lem 4.1, Prop 4.2, Cor 4.3, Thm 4.4 | zero padding, word multiplier, frame cone, acyclicity | `R = L_(F_2)(1,2)` only |
| Thm 5.1 (`thm:raw-criterion`) | `St_n(B) → GL_n(B)` iso | `B` of characteristic two, `n ≥ 4`, `GL_(n−1) = E_(n−1)`, `GL_(n−2) = E_(n−2)`, `j_(n−1)(N_(n−1)) = 1`, the realization of `X_n(B)` simply connected |
| Lem 5.2 | `j_m(N_m)` central in `St_(m+1)` | any unital ring, `m ≥ 3` |
| Lem 5.3, Thm 5.4, Thm 6.1 | `GL_m = E_m`; `St_r ≅ GL_r` for `r ≥ 3` (Voronetsky); `R^x` finitely presented (Krstić–McCool Thm 3) | `R = L_(F_2)(1,2)` only |

**Match with this audit.**
- **`p = 2`.** Thm 2.2, Thm 5.1 and Lem 5.2 are used exactly as stated. `L_2 ⊗ L_2` is an
  `F_2`-algebra of characteristic two. The `R`-specific results are correctly redone here for
  `B ⊗ L` (items 3–5, 8, 9).
- **Odd `p`: correction.** Section 2 of the source is for `F_2`-algebras only. So at odd `p`,
  Thm 2.2 and Lem 2.4 are also used in transferred form, not "as stated", in addition to the Lem 2.3
  and Thm 5.1 transfers listed in (T2). (T1) above should read "Theorem 2.2 and Lemmas 2.3–2.4 at
  `p = 2`; their odd-`p` forms are in (T2)".
  - I located every place the proofs of Lem 2.3, Lem 2.4 and Thm 2.2 use characteristic 2:
    - the embedding `F_(2^m) → M_m(F_2) → A`, which becomes `F_(p^m) → M_m(F_p) → A`;
    - `2H_j(V) = 0` (the lens-space complex gives `pH_j(V) = 0`);
    - `H^*(V; F_2)` polynomial, which becomes `Λ(V^*) ⊗ S(βV^*)`;
    - Quillen's count. It holds with at most `j < m ≤ m(p−1)` summands, so the carry never reaches
      all digits `p−1`;
    - exactness of coinvariants of the order-`(p^m−1)` group on `p`-primary modules;
    - `p^n K_n = 0`.

    All transfer. The rest of the proof of Thm 2.2 is characteristic-free.
  - In the proof of Thm 5.1, characteristic 2 enters only through `w_12² = 1` and the sign-free
    Weyl action. With the Tits lifts of item 7:
    - `τ' b_1 = b_2`, and `τ'` normalizes `K` with `η'(k(a,b,H)) = k(−b, a, H)`;
    - the path computation for the triangle relation is unchanged (`τ'` fixes `b_3`);
    - the central correction `z` makes `ψ(T) = Wz` satisfy both relations.

    So item 7 is correct.
- **The node's degree-truncated form.** Part 1 of `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`
  ("`K_i = 0` for `i ≤ N` gives `H_n = 0` for `n ≤ N`") is not stated by Khanh. It follows from his
  proof: the induction in Thm 2.2 uses hypothesis (1) one degree at a time, and Prop 3.2's plus
  construction gives `H_n(GL_∞) = 0` for `n ≤ N` by Hurewicz.

**Verdict.** No hypothesis mismatch affects any conclusion. The only defect is the (T1)/(T2)
bookkeeping at odd `p`, corrected above. The trust surface is Khanh's unrefereed v1, used at `p = 2`
as stated and at odd `p` through routine transfers checked here, together with the classical
results he cites.
