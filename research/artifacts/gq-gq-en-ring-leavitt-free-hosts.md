# Ring hosts for GL_n(Q) after the scalar obstruction (lane gq-en-ring, 2026-09-17, round 2)

Coordinator targets:
- (A) a finitely presented simple ring `R ⊇ Q`, not Leavitt-type, with
  `ker(Q^x -> K_1(R))` finitely generated and `PE_N(R)` finitely presented and simple; or a
  proof that none exists;
- (B) the subgroup route inside `R_L^x`.

## 1. Proved and landed

`ibn-failure-makes-rational-scalars-elementary` (ESTABLISHED, lane proof, not refereed). Let
`R ⊇ Q` with `R^m ≅ R^(m+k)`. Then `λ^k I_(m'N) ∈ E_(m'N)(R)` for all `λ ∈ Q^x`, all `m' >= m`
and all `N >= 2`. So `PE_M(R)` is not finitely presented at those ranks `M >= 3`.
- **Leavitt families (`m = 1`).** If `R ≅ R^d`, every rank is killed. For `d = 2`, every
  `λ I_N` is elementary.
- **Method.** Corner elementary groups over the Leavitt family form one group `G`,
  independent of the prefix code. The canonical 3-cycles of cones lie in `G`. The diagonal
  units `d_a(λ) = 1 + (λ-1)p_a` normalize `G`, and all proper cones give one class `κ` in
  `Ĝ/G`. The refinement `d_a = d_(a1)..d_(ad)` gives `κ = κ^d`.
- **What it does to (A).** The restriction "not Leavitt-type" in (A) is forced. A host must
  satisfy `R ≇ R^d` for all `d`. IBN failure at a higher rank `m` also kills the ranks
  `m'N`, `m' >= m`.

## 2. (A): no host found; no no-go either

- **Calibration.** `L_Q(E)` for the two-vertex graph in Attempt 4 of
  `q-algebra-with-fp-simple-projective-elementary-group` has these properties:
  - it is purely infinite simple;
  - `[1]` generates `K_0 ≅ Z`, so it has no Leavitt family;
  - `Q^x` injects into `K_1`, by ABC arXiv:0903.0056v2 Thm 7.6; the map identification is
    as recalled;
  - `PE_N` is simple.
  
  Only finite generation fails. So pure infiniteness is not the obstruction; torsion of
  `[1]` is. Any proof that no host exists has to use finite generation of `R`.
- **Easy necessary facts on finite generation (remarks, not landed as claims).**
  - A finitely generated ring containing `Q` embeds in no `M_n(C)` with `C` commutative.
    The entries of the generators generate a finitely generated commutative ring
    containing `Q`, and no such ring exists.
  - Granting Posner–Rowen (prime PI rings embed in matrices over a field; recalled, not
    re-read), a finitely generated simple ring containing `Q` is not PI, so it is
    infinite-dimensional over its centre.
- **Candidate direction.** Build the resolvent ring over a Leavitt path algebra whose unit
  class is free in `K_0`, using a Cuntz–Toeplitz pair instead of a Leavitt pair. This is a
  spark in the node; simplicity and the `K_0` class are open.

## 3. (B): already settled, negatively, on main

`cone-sl2-and-v-put-central-scalars-in-derived-subgroup` (fac901c01, another lane) proves
the following. If `H ≤ R^x` contains `V` and one cone `SL_2(K)`, then
`K^x ≤ [H,H] ∩ Z(H)`, so `H/C` is not finitely presented for central `C ⊇ K^x`. Every `H`
containing `V` and a corner `Ψ(GL_n(Q))` therefore has a derived subgroup that is not simple
and a non-finitely-generated group of central scalars. This lane's independent computation
(Steps 3–6 of the proof above) agrees.

The remaining escapes, as that node lists:
- `H/M` with `M` non-central;
- subgroups avoiding `V`;
- rings with no infinite central field.
