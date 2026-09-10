# Jacobson elementary groups: exact torsion radical, integral dichotomy, rank-two exclusion (ingestion, 2026-09-09)

## 0. Provenance and verification

Source: a user-supplied note of 2026-09-09, "Jacobson elementary groups:
an exact torsion radical, the integral dichotomy, and the rank-two
exclusion", written against the manuscript's compression criterion
(`normal-kazhdan-defect-non-mf`) and the rank-four torsion proposition
(`finite-additive-order-one-sided-defects-are-mf-invisible`,
`prop:torsion-defect-ring` in `non_mf_groups_exist.tex`).  Every
identity below was re-derived here; the four literature inputs were
checked against the author-hosted or publisher PDFs on 2026-09-09
(Section 6).  Mechanisms: finite-rank ring algebra, finitary determinants,
stable Steinberg groups and classical `K_2`, one theorem on linear groups
of rank two, and the compression criterion as a black box.  No cocycle,
weighted or rescaled norm, rank metric, or lifting theorem.  The excluded
external manuscript is not a premise of anything here.

Notation.  `J = Z<s,t | ts = 1>`, `e = 1 - st`, `f_(ij) = s^i e t^j`,
`I = JeJ = M_fin(N_0, Z)`, `S = Z[z,z^-1] = J/I`, `A_m = J/mI` for
`m >= 2` (characteristic zero; `e` has additive order exactly `m`),
`I_m = A_m e A_m = M_fin(N_0, Z/m)`, `A_m/I_m = S`.
`G_n = EL_n(J)`, `N_n = E_n(J, I)` the relative elementary subgroup,
`T_n = G_n/N_n`.  `GL_fin(B)` and `SL_fin(B)` are the finitary
automorphisms of `B^((n x N_0))` (finite matrices extended by the
identity) and their determinant-one subgroup.

## 1. Symbol kernel and relative elementary subgroup (node A)

`integral-jacobson-symbol-kernel-is-finitary-general-linear`.  For
`n >= 2`:

* `N_n = SL_fin(Z)`.  Relative roots `x_(ij)(a f_(uv))`, `a in Z`, are
  the finitary transvections between distinct external coordinates; a
  transvection inside one external coordinate `i` is
  `[x_(ik)(f_(uw)), x_(ki)(f_(wv))] = diag(.., 1 + f_(uv), ..)` for
  `u != v` and any `k != i`, `w` arbitrary (checked: `f_(uw) f_(wv) =
  f_(uv)`, `f_(wv) f_(uw) = 0`).  These generate `SL_fin(Z)`.  Conversely
  the finitary determinant of a finite-rank perturbation of the identity
  is well defined and conjugation invariant, and every relative root has
  determinant one.
* The sign is elementary: with `U = [[s, e], [0, t]]` (the compressor of
  the manuscript's compression cell, an explicit product of six
  elementary matrices) and `D = diag(-1, 1)`, which normalizes
  `EL_2(J)`,

  ```text
  eta = [U, D] = diag(1 - 2e, 1),        det_fin(eta) = -1,
  ```

  checked: `U D U^-1 D = [[s,e],[0,t]] [[t,0],[-e,s]] = [[st - e, 0],[0, 1]]`.
* Hence `ker(G_n -> EL_n(S)) = GL_fin(Z)`, and `T_n` is a central
  extension `1 -> C_2 -> T_n -> EL_n(S) -> 1`, with `T_n -> T_(n+1)`
  injective (finitary determinant is stable).

## 2. Residual finiteness of the sign quotient (node B)

`integral-jacobson-sign-quotient-is-residually-finite`.  A finite central
extension of a residually finite group need not be residually finite, so
this needs a detector.

* The additive section `lambda : S -> J`, `z^j -> s^j` (`j >= 0`),
  `z^-j -> t^j` (`j > 0`), gives a surjection `St(S) ->> T_oo`,
  `X_(ij)(a) -> x_(ij)(lambda a) N`: additivity and unrelated-root
  commutation are exact, and `lambda(a) lambda(b) - lambda(ab) in I`, so
  the three-index relation holds modulo `N`.  Same for `St_n(S) ->> T_n`
  when `n >= 3`.
* `K_2(Z) = C_2` on `c = {-1,-1}` (Milnor; Weibel III.5.2.2) and
  `K_2(S) = K_2(Z) (+) K_1(Z) = <c_0> (+) <tau>`, `tau = {z, -1}`
  (fundamental theorem for the regular ring `Z`, Weibel V.6.3 and
  V.6.3.1, splitting by multiplication by the unit).  `c_0` dies in
  `T_oo` because the constant Steinberg word evaluates in `E(Z)`, where
  it is trivial.  The kernel of `T_oo -> E(S)` is `C_2`, so
  `T_oo = St(S)/<c_0>` and `tau` maps to the class of `eta`.
* Detector.  `B = Z/4`, `K_2(B) = C_2` on `{-1,-1}` (Weibel III Ex. 5.13),
  and `K_2(r, B) = K_2(B)` for `r >= 3` since `sr(B) = 1` (Weibel
  III.5.5.2), so `St_r(B)` is finite and embeds in `St(B)`.  Put
  `F_r = (St_r(B) x St_r(B)) / <(c-bar_r, c-bar_r)>`, finite.  The two
  evaluations `z -> 1`, `z -> -1` give `beta : St(S) -> St(B) x St(B)`
  with `beta(c_0) = (c-bar, c-bar)` and `beta(tau) = ({1,-1}, {-1,-1}) =
  (1, c-bar)`.  So `[w] -> (p(w), [beta(w)])` is an injective
  homomorphism `T_oo -> E(S) x F_oo`, and restricting to words on the
  first `n` indices, `T_n -> EL_n(S) x F_(max(n,3))` is injective.
  `EL_n(S)` is residually finite, so every `T_n` is.
* `SL_fin(Z)` has no nontrivial finite quotient: for a homomorphism to a
  finite group, pigeonhole two indices `r != s` with equal images of
  `T_(ar)(1), T_(as)(1)`; then `[T_(ar)(1) T_(as)(1)^-1, T_(rb)(1)] =
  T_(ab)(1)` (checked) is killed, and these generate.  Hence
  `Res_fin(G_n) = N_n` and `Rad_MF(G_n) <= N_n` for every `n >= 2`.

## 3. Exact radical for the universal torsion rings (node C)

`universal-torsion-defect-rings-have-exact-mf-radical`.  `pi_m : G_n ->>
EL_n(A_m)` has kernel the finitary integral matrices congruent to `I`
mod `m`, of determinant `+-1` and `= 1 mod m`; for `m > 2` this forces
determinant one, so `ker pi_m <= N_n` and `EL_n(A_m)/pi_m(N_n) = T_n`;
for `m = 2`, `eta in ker pi_2` and the quotient is `EL_n(S)`.  Also
`pi_m(N_n) = E_n(A_m, I_m) = SL_fin(Z/m)` (elementary generation over
`Z/m` by Chinese remainder plus diagonal pairs), and the symbol kernel of
`EL_n(A_m)` is `{g in GL_fin(Z/m) : det g = +-1}`.  For `n >= 4` the
torsion theorem puts `E_n(A_m, I_m)` in the MF radical, and the quotient
is residually finite, hence MF, so

```text
Rad_MF(EL_n(A_m)) = Res_fin(EL_n(A_m)) = E_n(A_m, I_m) = SL_fin(Z/m),
```

and for `m > 2` the symbol kernel exceeds the radical by exactly the
central `C_2` carried by `eta`, which survives in a finite quotient.
Two caveats recorded on the node: in general `Rad_MF(G) = N` iff `G/N`
is MF (countable residually-MF groups are MF by diagonal block sums);
and the equality `Rad_MF(EL_n(R)) = E_n(R, ReR)` is not universal
(`R = J_(F_2) x L_(F_2)(1,2)` with the pair `(s,1),(t,1)`).

## 4. Trivial-or-infinite-order, and the integral dichotomy (nodes D, E)

`central-defect-element-mf-image-is-trivial-or-infinite`.  If `L <= Delta`
is Kazhdan, `zeta in Z(Delta) cap D_Delta(L)`, and `phi : Delta -> M`
with `M` MF, then `phi(zeta) = 1` or `phi(zeta)` has infinite order:
otherwise apply the criterion inside `phi(Delta)` to the finite central
`<phi(zeta)> <= D_(phi(Delta))(phi(L))` and the inclusion into `M`.

`integral-jacobson-mf-radical-is-all-or-nothing`.  For `n >= 4` and
`phi : G_n -> M` MF: if `1 != g in ker phi cap N_n`, choose a finite
block `F` carrying `g - I`, `a in F` with `v = (g - I)e_a != 0`,
`b not in F`; then `[g, T_(ab)(1)] = I + v e_b^T in ker phi` (checked:
`g E_(ab) g^-1 = (e_a + v) e_b^T` since `e_b^T g^-1 = e_b^T`).  With
`i in F`, `v_i = r != 0`, `c not in F cup {b}`,
`[T_(ci)(1), I + v e_b^T] = T_(cb)(r) in ker phi` (checked: `X Y = r E_(cb)`,
`Y X = 0`, squares zero).  A finitary determinant-one signed permutation
carries `T_(cb)(r)` to `zeta^(+-r)`, `zeta = I + f_12 E_44` the
manuscript's central defect element (infinite cyclic over `J`), so
`phi(zeta)` has finite order, hence `phi(zeta) = 1` by node D, hence
`phi(N_n) = 1` because the signed-permutation conjugates of `zeta`
generate `N_n`.  So `phi` is injective or trivial on `N_n`.  If some
`phi` is injective on `N_n`, then `phi x (G_n -> T_n)` is injective into
an MF group and `G_n` is MF; otherwise `Rad_MF(G_n) = N_n`.  Which
alternative holds is not decided.

## 4b. Scalar-center audit of the dichotomy (node G, same day, later note)

A follow-up note audited Theorem 3 of the source note and found its
statement overstated: the proof gives "`phi` restricted to `N_n` is
injective or trivial", not "`phi` is injective or trivial on `N_n`".
Node E states the restricted form `(AN1)`; its title was tightened here.

* `C_(G_n)(N_n) = Z(G_n) = {+-I}`: an integral automorphism commuting
  with every finitary transvection `I + E_(ab)` is scalar (checked: the
  relation on `e_c`, `c != b`, kills off-diagonal entries; on `e_b` it
  equates diagonal entries), and `-I = w_12^2 w_34^2 in EL_4`, not
  finitary.  So the whole-group form is `N_n <= ker phi` or
  `ker phi <= {+-I}`.
* `mf-group-with-order-two-center-has-mf-central-quotient` (node G): a
  countable MF group with center a single involution has MF central
  quotient.  Every step re-derived: spectral rounding of `V_j(c)` with
  the bound `delta/sqrt 2`; averaging and polar parts commuting exactly
  with `J_j`; `Psi_j = (+)_(+-) W_j^(+-) (x) conj W_j^(+-)` with
  `||U (x) conj U - V (x) conj V|| <= 2||U - V||` and `Psi_j(c) = I`; and
  `||U (x) conj U - I|| = max |lambda - mu|` forcing a killed element to
  be asymptotically scalar on both blocks, hence central.
* Consequence: the strong reading of Theorem 3 is equivalent to
  `Rad_MF(G_n) = N_n` (if `G_n` were MF, `G_n -> G_n/{+-I}` would be an
  MF-valued map with kernel `{+-I}` injective on `N_n`).  The prompt
  `/tmp/non_mf_decide_integral_jacobson.txt` item (3) was reworded to the
  restricted form so that no solver can take the strong form as given.
* Exact centerless reformulation, node H
  (`integral-jacobson-centerless-quotient-carries-dichotomy`): `G_n` is
  MF iff `P = G_n/{+-I}` is MF, `C_P(image of N_n) = 1`, and every MF
  homomorphism of `P` is injective or kills the image of `N_n`; for odd
  `n >= 5` the center is trivial and the whole-group dichotomy holds for
  `G_n` itself.  Nothing is decided.

## 5. Rank-two exclusion (node F)

`rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup`.
Guentner--Higson--Weinberger, Publ. IHES 101 (2005), Section 5,
Theorem 4: every countable subgroup of `GL(2, K)`, `K` any field, has the
Haagerup property; so its Kazhdan subgroups are finite.  For Kazhdan
`L <= GL_2(A_m)`, the symbol image in `GL_2(S) <= GL_2(Q(z))` is finite,
and the symbol kernel (finite perturbations over `Z/m`) is locally
finite; a finitely generated group with a finite-index locally finite
subgroup is finite.  Same over `k<s,t | ts = 1>`, `k` finite, with
`k(z)`.  A finite `L` with `u L u^-1 <= L` has `u L u^-1 = L`, so `u`
normalizes `L` and carries `C(L)` to itself: every defect generator is
`1`, `D_Delta(L) = 1` for every subgroup `Delta`, and every homomorphism
into these rank-two groups kills every Kazhdan compression defect of its
source.  Rank three is not settled (`SL_3(Z) <= EL_3`).

## 6. Citation ledger (checked 2026-09-09)

* GHW, `https://www.numdam.org/item/10.1007/s10240-005-0030-5.pdf`,
  Section 5: "4. Theorem. Let K be a field. Every countable subgroup of
  GL(2, K) has the Haagerup property."  Verified verbatim.
* Weibel, K-book III (author-hosted PDF): Example 5.2.2 (`K_2(Z)` cyclic
  of order 2, symbol `{-1,-1}`, Milnor Section 10); Remark 5.5.2
  (`K_2(n,R) = K_2(R)` for `n >= d + 3` when `sr(R) = d + 1`);
  Exercise 5.13 (`K_2(Z/2^n) = K_2(Z/4) = {+-1}` on `{-1,-1}`).  Verified.
* Weibel, K-book V: Theorem 6.3 (`K_n(R[s,s^-1]) = K_n(R) (+) K_(n-1)(R)`
  for regular noetherian `R`) and Corollary 6.3.1 (splitting is
  multiplication by `s in K_1(Z[s,s^-1])`).  Verified.

## 7. Manuscript status

Landed in `non_mf_groups_exist.tex` on 2026-09-09, as the paragraph
following `prop:torsion-defect-ring`: the binary-field exactness
`Rad_MF(EL_n(F_2<s,t | ts = 1>)) = EL_n(J, JeJ) = union SL_N(F_2)` for
`n >= 4` (no `K`-theory needed, the symbol kernel is already
`SL_fin(F_2)`), and the rank-two inertness via GHW Theorem 4 explaining
the rank four as three plus one.  The `K_2(Z/4)` detector, the `A_m`
radical for `m > 2`, and the integral dichotomy are recorded here and in
the graph, not in the manuscript.
