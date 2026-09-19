---
rg: 2
id: mod-s2-holomorphic-torelli-certificates-unbounded-mass-proof
kind: route
title: Igusa's chi_10 turns mass into Hodge degree, and the covering degree over level 3 is at least the image of an infinite monodromy group mod 3n
target: mod-s2-holomorphic-torelli-certificates-have-unbounded-mass
requires: []
artifacts:
  - research/artifacts/van-der-geer-chi10-baily-borel-verified.md
---

Notation is that of the target.

**Verbatim inputs.** These are quoted in `research/artifacts/van-der-geer-chi10-baily-borel-verified.md`.
- **(Q1)** Igusa's cusp form `chi_10` of weight 10 for `Sp_4(Z)` vanishes with multiplicity 2 along the
  diagonal `z = 0`, and its zero divisor in `A_2` is twice the locus of products of elliptic curves.
- **(Q2)** (Baily-Borel) Scalar Siegel modular forms of high weight define an embedding of
  `Gamma_2 \ H_2^*` into projective space.

**Standard inputs, not quoted.**
- **(S1)** `Gamma(N)` is torsion-free for `N >= 3`. It therefore acts freely on the contractible space `H_2`,
  so `H_2 -> A_2(N)` is a universal covering.
- **(S2)** `H_2` is biholomorphic to a bounded domain (the Cayley transform onto the Siegel disc).
- **(S3)** For a nonconstant holomorphic map `h` of compact Riemann surfaces,
  `[pi_1(target) : h_* pi_1(source)] <= deg h`.
- **(S4)** Curves of bounded degree in a projective variety form a family of finite type (Chow or Hilbert
  scheme). Over a finite-type base there is a finite stratification into smooth connected strata such that,
  over each stratum, the normalizations of the fibres form a smooth proper family (Ehresmann applies).

**Step 0: the factorization.** Fix a holomorphic certificate `f : C~ -> A_2(Gamma')` with
`Gamma' <= Gamma(3)`, and put `g = p o f`.
- Since `C~` is smooth and `g` maps onto the irreducible compact curve `C_3`, `g` factors as `g = nu o h`.
  Here `h : C~ -> C~_3` is a nonconstant holomorphic map of compact Riemann surfaces; write `d_1 = deg h`.
- The automorphy factor `det(C tau + D)` defines `lambda` as a line bundle on each `A_2(N)` with `N >= 3`, by
  (S1). Moreover `lambda` on `A_2(Gamma')` is `p^* lambda`.
- Hence `f^* lambda = g^* lambda = h^* nu^* lambda`, and

      deg f^* lambda = d_1 * deg nu^* lambda.        (0.1)

**Step 1: mass = 5 deg lambda (H1).**
- *The divisor of `chi_10` on `H_2`.* By (Q1), the zero set of `chi_10` on `H_2` is the preimage of the
  product locus, that is, the union of the translates `g{z = 0}`. The factor `det(C tau + D)^10` never
  vanishes, so the divisor is `Sp_4(Z)`-invariant, and every translate carries multiplicity 2 as the
  diagonal does.
- *Local form.* Each translate is a smooth hypersurface, and the translates form a locally finite family.
  Near any point of `H_2`, therefore, `chi_10 = u prod_beta h_beta^2`. Here `u` is a unit and `h_beta`
  defines the local branch `beta` (one per translate through the point); the local ring is factorial.
- *Pullback to the curve.* `chi_10` is a section of `lambda^10` on `A_2(Gamma')`. Its pullback `f^* chi_10`
  is not identically zero, because `f(C~)` is not contained in `H_1`. At a point `x` of `C~`,
  `ord_x f^* chi_10 = 2 sum_beta ord_x(h_beta o f~)`, where `f~` is a local lift of `f`. The right side is
  twice the local intersection number of `f` with `H_1` at `x`.
- Summing over `x` gives `10 deg f^* lambda = 2 deg f^* H_1 = 2 chi(b(f))`, that is,
  `chi(b(f)) = 5 deg f^* lambda`.

*Positivity.* By (Q2) there are modular forms `F_0, ..., F_M` of some weight `k` for `Sp_4(Z)` defining an
embedding `phi` of `A_2^*` into `P^M`; in particular they have no common zero on `H_2`.
- Their pullbacks generate `nu^* lambda^k`, so `nu^* lambda^k = (phi o q o nu)^* O(1)`. Here
  `q : A_2(3) -> A_2` is the finite quotient map.
- The map `phi o q o nu` has finite fibres, so it is nonconstant, and `k deg nu^* lambda > 0`.
- So `deg nu^* lambda >= 1`, and by (0.1) `deg f^* lambda >= d_1 >= 1`.

**Step 2: the monodromy of `f` lies in `Gamma'`.** By (S1), `pi_1(A_2(Gamma')) = Gamma'` and
`pi_1(A_2(3)) = Gamma(3)`, and `p_*` is the inclusion, up to conjugacy by the choice of base points. Hence

    nu_* h_* pi_1(C~) = g_* pi_1(C~) = p_* f_* pi_1(C~) <= gamma Gamma' gamma^(-1)

for some `gamma in Gamma(3)`.

**Step 3: the covering degree bounds the index.** By (S3), `h_* pi_1(C~)` has index at most `d_1` in
`pi_1(C~_3)`. The map `nu_*` sends `pi_1(C~_3)` onto `Phi = Phi(f)`, so the image `nu_* h_* pi_1(C~)` has
index at most `d_1` in `Phi`. By Step 2 this image lies in `Phi cap gamma Gamma' gamma^(-1)`, so

    [Phi : Phi cap gamma Gamma' gamma^(-1)] <= d_1.

Now let `Gamma' <= Gamma(3n)`. Since `Gamma(3n)` is normal in `Sp_4(Z)`, `gamma Gamma' gamma^(-1)` lies in
`Gamma(3n)`. Also `Phi cap Gamma(3n)` is the kernel of reduction mod `3n` on `Phi`. Therefore
`|Phi mod 3n| <= d_1`. Combining (0.1), Step 1 and `deg nu^* lambda >= 1`,

    chi(b(f)) = 5 d_1 deg nu^* lambda >= 5 |Phi mod 3n|.

This is the inequality of (H2). The quantity `|Phi mod 3n|` does not change under conjugation by
`Gamma(3)`, again because `Gamma(3n)` is normal.

**Step 4: `Phi` is infinite.** Suppose `Phi` is finite.
- The kernel of `nu_* : pi_1(C~_3) -> Phi` has finite index. The corresponding covering `C' -> C~_3` is a
  finite unbranched covering, so `C'` is a compact Riemann surface.
- The composite `C' -> C~_3 -> A_2(3)` induces the trivial map on `pi_1`. By (S1) it therefore lifts to the
  universal covering `H_2`, giving a holomorphic map `C' -> H_2`.
- By (S2) the coordinates of this map are bounded holomorphic functions on a compact connected Riemann
  surface, hence constant by the maximum principle. So `nu` is constant, which contradicts
  `dim C_3 = 1`.

Therefore `Phi` is infinite, which completes (H2). Since `Phi` is infinite, it contains `m` distinct elements
for any given `m`. Their pairwise differences are nonzero integer matrices, so the elements stay distinct
mod `3n` as soon as `3n` exceeds every entry of every difference. Hence, for each fixed `f`,
`|Phi(f) mod 3n| -> infinity` as `n -> infinity`, along all `n` and not only along a divisibility chain.

**Step 5: uniformity (H3).** Fix `D`. Suppose `f` is a holomorphic certificate at some `Gamma' <= Gamma(3n)`
with mass `<= 5D`.

*Bounded degree.* By Step 3, `d_1 <= D` and `deg nu^* lambda <= D`.
- The quotient map `q` extends to a finite map `A_2(3)^* -> A_2^*` of Satake compactifications. So
  `psi = phi o q` is a finite morphism from the projective variety `A_2(3)^*` to `P^M`, and `psi^* O(1)` is
  ample.
- The curve `C_3` has `psi^* O(1)`-degree `k deg nu^* lambda <= kD`.

*Finitely many families.* By (S4), the irreducible curves of degree `<= kD` in `A_2(3)^*` form a family of
finite type. Meeting the closed boundary is a closed condition in a proper family, so the curves inside
`A_2(3)` form an open subfamily `T`, still of finite type. Stratify `T` as in (S4) into smooth connected strata
`T_1, ..., T_s`, over each of which the normalizations `nu_t` form a smooth proper family.

*Monodromy is constant on strata.* By Ehresmann, two fibres over the same stratum are identified by a
homeomorphism along a path, and `nu_t` and `nu_(t') o (homeomorphism)` are freely homotopic. Hence `Phi` is
constant up to `Gamma(3)`-conjugacy on each stratum. Only finitely many classes `Phi_1, ..., Phi_s` occur,
and each is infinite by Step 4.

*Choice of `n_0`.* By the end of Step 4, there is `n_0(D)` with `|Phi_j mod 3n| > D` for all `j` and all
`n >= n_0(D)`. For such `n`, Step 3 gives `D < |Phi(f) mod 3n| <= d_1 <= D`, a contradiction. This proves
(H3).

## Trust surface

- (Q1) and (Q2) are quoted verbatim from van der Geer's survey. Igusa's and Baily-Borel's originals were not
  read.
- The following are textbook facts used without quotation:
  - (S1) Serre's lemma;
  - (S2) the Cayley transform;
  - (S3) the covering-space argument over the complement of the branch values;
  - (S4) Chow finite type, generic smoothness of normalization in families, and Ehresmann.
- The extension of `q` to Satake compactifications is also used without quotation.
- The Remark in the target (certificates lie in `B`) depends on Mess's Torelli-space description, which is
  not verified. (H1)-(H3) do not use it.
