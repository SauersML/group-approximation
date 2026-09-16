# Schur kernels over Sp4(Z): consequence monotonicity, witness shape, and packet pruning

Date: 2026-09-16. Swarm agent on `sp4-schur-kernel-meets-the-deligne-triple-class`.

This artifact proves necessary conditions that any witness for the target
must satisfy. It does not produce a witness and does not refute the target.
Full proofs are here. The claim nodes
`schur-kernel-shrinks-along-consequences-and-hosts` and
`deligne-schur-witness-needs-maslov-carrying-packet` state the results and
cite this file.

## 0. Notation and imported results

- `Gamma = Sp_4(Z)`, `G = Sp_4(R)`, and `p : G~ -> G` is the universal cover
  with deck group `ker p = Z = <z>`. Here `pi_1(G) = pi_1(U(2)) = Z`, detected
  by `det_C` on the maximal compact `U(2)`.
- `Gamma~ = p^{-1}(Gamma)`, a central extension of `Gamma` by `Z`, with class
  `e in H^2(Gamma; Z)`. For `n >= 1`, `Gamma_n = Gamma~/<z^n>` has class
  `e_n = e mod n in H^2(Gamma; Z/n)`. So `E_3 = Gamma_3` and `alpha = e_3`.
- For a coefficient group `A` let `ev : H^2(X; A) -> Hom(H_2(X; Z), A)` be the
  universal-coefficient evaluation. It is natural in the group `X` and in the
  coefficients `A`. Write `<c, y> = ev(c)(y)` and `alpha_H = ev(alpha)`.
- For a group `Q` and a nonsingular `w in Q * <t>` (`deg_t w != 0`) put
  `A_w = (Q * <t>)/<<w>>`, with `q : Q -> A_w`. The Schur kernel is
  `K_2(Q, w) = ker(q_* : H_2(Q; Z) -> H_2(A_w; Z))`. If `phi : Q -> L` is a
  homomorphism, then `w_phi in L * <t>` is `w` with `phi` applied to its
  coefficients.

Imported graph nodes:

- (I1) `nonsingular-adjunction-never-enlarges-schur-multiplier`: `q_*` is
  surjective when `deg_t w != 0`.
- (I2) `projective-unitary-classes-vanish-on-schur-kernel`. Let `Q` be
  countable, `U = (prod U(d_n))/N`, `A` the image of the scalars, and
  `T = U/A`. For every homomorphism `phi : Q -> T`, the multiplier
  `beta_phi in Hom(H_2(Q), A)` vanishes on `K_2(Q, w)`. With a single factor,
  `T = PU(d)` and `A = U(1)`.
- (I3) `aspherical-adjunction-has-zero-schur-kernel`: if
  `(K(Q,1) v S^1) cup_w e^2` is aspherical, then `K_2(Q, w) = 0`.
- (I4) `amenable-t-shape-adjunctions-kill-no-schur-class`: if the
  coefficients of `w` lie in a torsion-free `B <= Q` and the reduced
  `t`-shape of `w` is amenable, then `K_2(Q, w) = 0`.
- (I5) `schur-kernel-localizes-to-coefficient-subgroup`: if `B <= Q` contains
  the coefficients and `B -> (B * <t>)/<<w>>` is injective, then
  `K_2(Q, w) = iota_* K_2(B, w)`.
- (I6) `kervaire-laudenbach-holds-for-hyperlinear`: for hyperlinear `B` and
  nonsingular `w`, `B -> (B * <t>)/<<w>>` is injective.
- (I7) `sp4-fd-projective-multiplier-is-finite`, route
  `sp4-fd-projective-multiplier-finiteness-proof`, Steps 0 and 3:
  `H_2(Gamma; Z) = Z<h> + F` with `F` finite, and `ev(e) = d . h^*` with an
  integer `d != 0`. That route writes `w` for the class called `e` here.
- (I8) `deligne-covers-of-sp2g-z-have-finite-residual-2z`: for `n >= 3`,
  `Res_fin(Gamma_n) = <z^2>`. This is display (DR2), as stated by Stover,
  arXiv:2407.07680, Thm 1.5.

Standard facts, used without re-reading a source:

- Mayer--Vietoris sequences for amalgams and HNN extensions.
- The transfer: for `j : B_0 -> B` of finite index, `j_* o tr = [B : B_0]`
  on `H_*(B; M)`.
- The Lyndon--Hochschild--Serre (LHS) spectral sequence.
- A central `g in L` induces the identity on `H_*(L; V)` through the pair
  `(c_g = id, v -> g v)` (Brown, *Cohomology of Groups*, III.8).
- Virtually free groups have `H_k(-; Q) = 0` for `k >= 2`.
- Finitely generated linear groups are residually finite (Malcev). Subgroups
  of residually finite groups are residually finite. Residually finite
  groups are sofic, hence hyperlinear.

## 1. General lemmas (any group Q)

**Lemma 1.1 (consequence monotonicity).** Let `u, w in Q * <t>` with
`w in <<u>>`. Then `deg_t w = k . deg_t u` for some integer `k`, and
`K_2(Q, w) <= K_2(Q, u)`.

*Proof.* `deg_t : Q * <t> -> Z` is a homomorphism. Write
`w = prod_i g_i u^{e_i} g_i^{-1}` with `e_i = ±1`. Then
`deg_t w = (sum e_i) deg_t u`. Since `<<w>> <= <<u>>`, there is a quotient map
`r : A_w -> A_u` with `q_u = r o q_w`. So `q_{u*} = r_* o q_{w*}` and
`ker q_{w*} <= ker q_{u*}`. ∎

In particular, if `w` is nonsingular then so is `u`.

**Corollary 1.2.** Let `w in <<u>>` be nonsingular.

- (a) `K_2(Q, u^k) <= K_2(Q, u)` for `k != 0`. More generally, if `w` kills a
  class `y`, then so does every `u` with `w in <<u>>`. Detection by a
  multiplier also passes up: if `ev(beta)(K_2(Q, w)) != 0`, then
  `ev(beta)(K_2(Q, u)) != 0`.
- (b) If `(K(Q,1) v S^1) cup_u e^2` is aspherical, then `K_2(Q, v) = 0` for
  every nonsingular `v in <<u>>`.
- (c) Suppose the coefficients of `u` lie in a torsion-free subgroup and the
  reduced `t`-shape of `u` is amenable. Then `K_2(Q, v) = 0` for every
  nonsingular `v in <<u>>`. This covers every proper power `u^k`, `|k| >= 2`,
  and every product of conjugates of `u^{±1}` with nonzero exponent sum,
  whatever their coefficients and shapes.

*Proof.* (a) is Lemma 1.1. (b) and (c) follow from Lemma 1.1 with (I3) and
(I4) applied to `u`. ∎

Caveat on (c): a *proper-power shape* (the `t`-shape of `w` is a proper power)
is not the same as `w` being a proper power of an element. Corollary 1.2(c)
prunes only the genuine consequences of a pruned `u`.

**Lemma 1.3 (host bound).** Let `phi : Q -> L` be a homomorphism. Suppose
`w_phi(l) = 1` for some `l in L`. Then `K_2(Q, w) <= ker(phi_* : H_2(Q) -> H_2(L))`.
In particular, if `w` has a solution in `Q` itself, then `K_2(Q, w) = 0`.

*Proof.* The homomorphism `Q * <t> -> L`, `q -> phi(q)`, `t -> l`, kills `w`.
It therefore factors as `s o (Q * <t> -> A_w)`, and `s o q = phi`. So
`phi_* = s_* o q_*` and `ker q_* <= ker phi_*`. For the last clause take
`L = Q` and `phi = id`. ∎

Note: if `w in <<u>>` and `u_phi(l) = 1`, then `w_phi(l) = 1`. So Lemma 1.3
for `u` gives nothing beyond Lemma 1.3 for `w`.

**Lemma 1.4 (rationally injective free constructions).** Let `C <= Q` with
`H_2(C; Q) = 0`. Suppose `P = Q *_C D` is an amalgam, or `P` is an HNN
extension of `Q` along two embeddings of `C`. Then
`H_2(Q; Q) -> H_2(P; Q)` is injective. The same holds for any finite iterate
of such constructions and for a directed union of them.

*Proof.* The amalgam Mayer--Vietoris sequence
`H_2(C;Q) -> H_2(Q;Q) + H_2(D;Q) -> H_2(P;Q)` has zero first term.
The HNN sequence `H_2(C;Q) -> H_2(Q;Q) -> H_2(P;Q)` also has zero first term.
Composites of injections are injective. `H_2(-; Q)` commutes with directed
colimits, and a class that dies in the colimit dies at a finite stage. ∎

Example: root adjunctions `Q *_{c = s^k} <s>` (`C = <c>` cyclic, so
`H_2(C; Q) = 0`).

## 2. The shape of a witness

A *witness* is a nonsingular `w in Gamma * <t>` with
`alpha_H(K_2(Gamma, w)) != 0`. Write `K_2 = K_2(Gamma, w)`.

**Lemma 2.1.** For `y in H_2(Gamma; Z)`, `alpha_H(y) = <e, y> mod 3`. Also
`alpha_H(F) = 0`, and `alpha_H != 0` if and only if `3` does not divide `d`.

*Proof.* The class of `Gamma~/<z^3>` is the image of `e` under `Z -> Z/3`, so
naturality of `ev` in the coefficients gives the formula. Since `F` is finite
and `Z` is torsion-free, `<e, F> = 0`. Finally `alpha_H(h) = d mod 3`. ∎

*Remark.* `alpha != 0`, because `Gamma_3` splitting would make it residually
finite, contradicting (I8). The kernel of
`ev : H^2(Gamma; Z/3) -> Hom(H_2, Z/3)` is `Ext(H_1(Gamma; Z), Z/3)`. If
`H_1(Sp_4(Z); Z) = Z/2`, this kernel is zero, so `alpha_H != 0` and `3` does
not divide `d`. That value of `H_1` is standard but was not re-checked here,
and nothing below uses it. The target presupposes `alpha_H != 0`.

**Theorem 2.2 (witness shape).** Let `w` be a witness. Then:

- (i) `3` does not divide `d`.
- (ii) `K_2` has rank one, and `<e, K_2> = d m Z` with `m >= 1` and `3` not
  dividing `m`.
- (iii) `H_2(A_w; Q) = 0` and `H_2(A_w; Z)` is finite.
- (iv) `<e, K_2> <= 2Z`. With (ii), `d m = ±2 mod 6`.

*Proof.*

(i) Lemma 2.1.

(ii) Pick `y in K_2` with `alpha_H(y) != 0`. Then `<e, y> != 0`, so `y` has a
nonzero `Z<h>`-component and `K_2 <= Z<h> + F` has rank one.
`ev(e)(K_2) <= d Z` is a nonzero subgroup, so it equals `d m Z` for some
`m >= 1`. It is not contained in `3Z`, so `3` divides neither `d` nor `m`.

(iii) By (I1), `q_*` is surjective, and so is `q_* (x) Q`. Its kernel
contains `K_2 (x) Q`, which is nonzero in `H_2(Gamma; Q) = Q`. So
`H_2(A_w; Q) = 0`. `H_2(A_w; Z) = (Z + F)/K_2` is a finitely generated group
of rank zero, hence finite.

(iv) Take `n = 4` in (I8): `Res_fin(Gamma_4) = <z^2>`, which does not contain
`z`.

1. **A finite quotient.** Some homomorphism `Phi : Gamma_4 -> E` onto a finite
   group has `Phi(z) != 1`. Since `z^2 in Res_fin`, `Phi(z)` has order exactly
   `2`. So `Phi` factors through `Gamma_2 = Gamma_4/<z^2>`, giving
   `Phi- : Gamma_2 -> E`.
2. **A morphism of extensions.** `c = Phi-(z)` is central of order `2`. Put
   `E- = E/<c>` and let `phi : Gamma -> E-` be the induced map. Then
   `(Z/2 -> Gamma_2 -> Gamma) -> (<c> -> E -> E-)` is a morphism of central
   extensions that is an isomorphism on kernels. Hence
   `e_2 = phi^*[E]` in `H^2(Gamma; Z/2)`.
3. **A projective representation.** Let `V = Ind_{<c>}^{E} sgn`. Since `c` is
   central, `c` acts on `V` as `-1`. So `E -> U(V)` induces
   `pi : E- -> PU(V)`. The pullback of `U(V) -> PU(V)` along `pi` has class
   `iota_*[E]`, where `iota : Z/2 -> U(1)` is `{±1}`.
4. **Evaluation.** The multiplier of `pi o phi : Gamma -> PU(V)` is
   `iota_* e_2`, and `ev(iota_* e_2)(y) = iota(<e, y> mod 2)`. By (I2) it
   vanishes on `K_2`. So `<e, y>` is even for every `y in K_2`.

Finally, `d m` is even and not divisible by `3`, so `d m = ±2 mod 6`. ∎

*Dependency flag for (iv).* (iv) consumes the inclusion
`Res_fin(Gamma_4) <= <z^2>`, i.e. that `z` survives in some finite quotient.
That is part of (DR2) as stated in the source and recorded in (I8), but earlier
graph uses of (I8) consumed only the other inclusion. It is equivalent to
residual finiteness of the metaplectic double cover `Gamma_2`, which is
classical (theta multiplier) but not re-verified here. Nothing in Sections 3
or 4 uses (iv).

*Alternative derivation of (iv).* The landed claim
`schur-kernel-lies-in-hyperlinear-radical`, applied to `E = Gamma_4`, gives
`ev(e_4)(K_2) <= Rad_hyp(Gamma_4)`. Finite groups are hyperlinear, so
`Rad_hyp(Gamma_4) <= Res_fin(Gamma_4) = <z^2>`, and again `<e, K_2> <= 2Z`.
This consumes the same inclusion of (DR2).

## 3. Packet pruning

Call a subgroup `B <= Gamma` **Maslov-carrying** if
`<e, iota_* H_2(B; Z)> != 0`, where `iota : B -> Gamma`.

Because `ev(e) (x) Q : H_2(Gamma; Q) = Q -> Q` is an isomorphism (`d != 0`),
this holds exactly when `iota_* : H_2(B; Q) -> H_2(Gamma; Q)` is nonzero. It
also holds exactly when the restriction `iota^* e` pairs nontrivially with
`H_2(B; Z)`.

Call `w` **pruned** if `<e, K_2(Gamma, w)> = 0`. A pruned `w` is not a
witness. Its Schur kernel lies in `F`, and every `ev(e_n)` vanishes on it.

**Lemma 3.1 (packet lemma).** Let `w in Gamma * <t>` be nonsingular, and let
`B <= Gamma` contain its coefficients. Then `K_2(Gamma, w) <= iota_* H_2(B; Z)`.
If `B` is not Maslov-carrying, then `w` is pruned.

*Proof.* `B` is a subgroup of the finitely generated linear group `Gamma`, so
it is residually finite, hence hyperlinear. By (I6),
`B -> (B * <t>)/<<w>>` is injective. By (I5),
`K_2(Gamma, w) = iota_* K_2(B, w) <= iota_* H_2(B; Z)`. ∎

**Lemma 3.2 (virtual packets).** If some finite-index `B_0 <= B` is not
Maslov-carrying, then `B` is not Maslov-carrying.

*Proof.* Let `j : B_0 -> B` be the inclusion and `x in H_2(B; Q)`. Then
`[B : B_0] iota_* x = iota_* j_* tr(x) = (iota o j)_* tr(x) = 0`. Since
`Q` has characteristic zero, `iota_* x = 0`. ∎

### 3.3 Rational lines and hyperplanes: the Klingen parabolic

Use the basis `(e1, e2, f1, f2)` of `Z^4` with `omega(e_i, f_j) = delta_ij`
and `omega(e_i, e_j) = omega(f_i, f_j) = 0`. Put
`P_K = Stab_Gamma(Q e1)`.

**Proposition 3.3.** `H_2(P_K; Q) = 0`. Every stabilizer in `Gamma` of a
rational line, or of a rational 3-dimensional subspace, is
`Gamma`-conjugate to `P_K`. So a `B_0` that preserves such a subspace is not
Maslov-carrying.

*Proof.*

**Step 1: structure of `P_K`.**

- If `g in P_K` then `g e1 = lambda e1` with `lambda = ±1`, because `g` is
  integral with integral inverse.
- `g` preserves `e1^perp = span(e1, e2, f2)`. It induces
  `A in Sp(Z e2 + Z f2) = SL_2(Z)` on `e1^perp / Z e1`.
- This gives a surjection `P_K -> L = {±1} x SL_2(Z)`. It is split by
  `m(lambda, A)`, which is `lambda` on `span(e1, f1)` and `A` on
  `span(e2, f2)`. This map is block-diagonal on an orthogonal splitting,
  hence symplectic.
- The kernel `N` consists of the maps `n(a, b, c)`:
  `e1 -> e1`, `e2 -> e2 + a e1`, `f2 -> f2 + b e1`,
  `f1 -> f1 + c e1 + b e2 - a f2`. The coefficients of `e2` and `f2` in the
  image of `f1` are forced by `omega(g e2, g f1) = 0` and
  `omega(g f2, g f1) = 0`.

The products are as follows (checked exactly in E3, Section 7):

- `n(a,b,c) n(a',b',c') = n(a+a', b+b', c+c' + a b' - a' b)`.
- `[n(1,0,0), n(0,1,0)] = n(0,0,2)`.
- `m(1,-I) n(a,b,c) m(1,-I)^{-1} = n(-a,-b,c)`.

So `N` is an integral Heisenberg group with center `C = {n(0,0,c)} = Z` and
`N/C = Z^2`. `P_K = N x| L`.

**Step 2: `H_*(N; Q)` as an `L`-module.**

Use the LHS spectral sequence of `1 -> C -> N -> N/C -> 1`. It is central, so
`E^2_{p,q} = H_p(Z^2; Q) (x) H_q(Z; Q)` with `q in {0, 1}`.

- The differential `d^2 : E^2_{2,0} = Q -> E^2_{0,1} = Q` is onto, hence an
  isomorphism. By the five-term exact sequence
  `H_2(N/C) -> H_1(C) -> H_1(N) -> H_1(N/C) -> 0`, its image is the kernel of
  `C (x) Q -> H_1(N; Q)`. That kernel is all of `C (x) Q`, because
  `C cap [N, N] = 2C` has finite index in `C`.
- `E^2_{3,0} = 0`.
- So `H_2(N; Q) = E^inf_{1,1} = H_1(N/C; Q) (x) H_1(C; Q)`, which is `Q^2`.
- Also `H_1(N; Q) = H_1(N/C; Q)`.

These identifications are natural for automorphisms of `N` preserving `C`,
hence `L`-equivariant. The central element `m(1,-I) in L` acts by `-1` on
`N/C` and by `+1` on `C`. So it acts by `-1` on `H_1(N; Q)` and on
`H_2(N; Q)`.

Cross-check (Poincare duality on the 3-dimensional nilmanifold): the
automorphism has degree `(-1)(-1)(+1) = +1` and acts by `-1` on `H^1`, so it
acts by `-1` on `H_2`. The Lie-algebra computation gives the same answer:
`H^2` of the Heisenberg algebra is spanned by `X^* ^ Z^*` and `Y^* ^ Z^*`,
both of weight `-1`.

**Step 3: the extension `1 -> N -> P_K -> L -> 1`.**

Here `E^2_{p,q} = H_p(L; H_q(N; Q))`.

- For `q = 1, 2`: the central `m(1,-I)` induces the identity on
  `H_p(L; V)` (Brown III.8) but acts on `V = H_q(N; Q)` as `-1`. So `2` kills
  `H_p(L; V)`, and `H_p(L; V) = 0`.
- For `q = 0`: `L` is virtually free (it contains the free group `Gamma(3)`
  of finite index), so `H_2(L; Q) = 0`.
- Hence `E^2_{2,0} = E^2_{1,1} = E^2_{0,2} = 0`, and `H_2(P_K; Q) = 0`.

**Step 4: conjugacy.**

- **Lines.** Let `l` be a rational line and `v` a primitive vector of
  `l cap Z^4`. The functional `omega(v, -)` is primitive, because `omega` is
  unimodular, so `omega(v, u) = 1` for some `u in Z^4`. Then
  `H = Z v + Z u` is a unimodular hyperbolic plane and `Z^4 = H + H^perp`,
  via `x -> omega(x,u) v - omega(x,v) u`. `H^perp` is unimodular of rank 2 and
  has a symplectic basis `(v', u')`. The matrix of `(v, v', u, u')` lies in
  `Gamma` and sends `e1 -> v`. So `Stab_Gamma(l)` is conjugate to `P_K`.
- **3-spaces.** A rational 3-space `U` has the same stabilizer as the rational
  line `U^perp`.
- **Consequence.** A `B_0` preserving such a subspace lies in a conjugate of
  `P_K`. So `iota_*` factors through `H_2(P_K; Q) = 0`. ∎

### 3.4 Winding-zero Lie subgroups

For a connected Lie group `S` with an injective immersive homomorphism
`i : S -> G`, the **winding** of `S` is `i_* : pi_1(S) -> pi_1(G) = Z`.

**Proposition 3.4.** Suppose `i_* = 0`. Then:

- (a) `p^{-1}(i(S)) -> i(S)` has a homomorphic section.
- (b) Conjugating `S` by any `g in G` preserves the winding.
- (c) Every `B_0 <= Gamma` contained in `g i(S) g^{-1}` is not
  Maslov-carrying.

*Proof.*

(a) Since `S` is connected and locally path-connected and `i_* = 0`, the
lifting criterion gives a continuous `s : S -> G~` with `p o s = i` and
`s(1) = 1`. The map `(x, y) -> s(xy) s(y)^{-1} s(x)^{-1}` is continuous from
the connected space `S x S` into the discrete `ker p`, and equals `1` at
`(1, 1)`. So it is constantly `1`, and `s` is a homomorphism.

(b) Conjugation `c_g` is homotopic to the identity, because `G` is connected.

(c) By (a) and (b) we may take `B_0 <= i(S)`. Then `s o i^{-1}` restricted to
`B_0` is a homomorphism `B_0 -> p^{-1}(B_0) <= Gamma~` splitting `p`. So
`iota^* e = 0` in `H^2(B_0; Z)`, and `<e, iota_* H_2(B_0)> = 0`. ∎

**Examples 3.5.** Windings are computed through `U(2)`-valued loops and
`det_C`, and cross-checked numerically in E2.

- (i) **Siegel parabolic.** `P_S = Stab_G(L_0)` with
  `L_0 = span(e1, e2)`, so `P_S = GL_2(R) x| Sym_2(R)`.
  - Its identity component retracts onto
    `{diag(R, R) : R in SO(2)}`.
  - Under `[[X, -Y], [Y, X]] <-> X + iY`, this is `SO(2) <= U(2)` with
    `det_C = 1`. So the winding is zero.
  - `G` acts transitively on real Lagrangians, and `P_S^0` has index 2 in
    `P_S`.
  - With Lemma 3.2: **any `B_0` preserving a real Lagrangian subspace is not
    Maslov-carrying.** This covers `Gamma cap P_S = GL_2(Z) x| Sym_2(Z)`.
- (ii) **`SL_2(C)`.** It acts on `C^2 = R^4` preserving the real alternating
  form `Im det[x y]`. `pi_1(SL_2(C)) = 0`, so the winding is zero. As a real
  representation `C^2` is irreducible, since the commutant is `C`. So this
  group preserves **no** real subspace, and (i) does not cover it.
- (iii) **Bianchi groups.** Let `O_d` be the integers of `Q(sqrt(-d))`, with
  `Z`-basis `(1, omega)` and `omega^2 = t omega - n`.
  - Put `beta_d = Im det / Im omega` on `O_d^2`. So `beta_d(x, y)` is the
    `omega`-coefficient of `det[x y] in O_d`. It is integral, alternating
    and `SL_2(O_d)`-invariant.
  - In the `Z`-basis `e1 = (1,0)`, `e2 = (omega,0)`, `e3 = (0,1)`,
    `e4 = (0,omega)`, the nonzero Gram entries (up to antisymmetry) are
    `beta(e1,e4) = beta(e2,e3) = 1` and `beta(e2,e4) = t`. The determinant is
    `1`.
  - `(e1, e2 - t e1, e4, e3)` is a symplectic `Z`-basis. This was checked
    exactly for `d in {1,2,3,7,11,15,19}` in E1, and holds in general by the
    displayed Gram entries.
  - Conjugating by this basis embeds `SL_2(O_d)` in `Gamma`, inside a
    `G`-conjugate of `SL_2(C)`.
  - By Proposition 3.4, **every `B_0` virtually inside such a Bianchi packet
    is not Maslov-carrying**. A finite-index subgroup of `SL_2(O_d)` is a
    lattice in `SL_2(C)`, hence Zariski dense there (Borel density, standard,
    not re-read). So it preserves no real subspace, and (P2), (P2') and (P3)
    below do not apply to it. By transfer, (P1) applies to a packet `B`
    exactly when `H_2(B; Q) = 0`. That was not checked for these packets, and
    Proposition 3.4 does not need it.
- (iv) **Diagonal copies and quaternion groups.**
  - `SL_2(R)` acting diagonally on `(R^2, omega) + (R^2, -omega)` has winding
    `1 + (-1) = 0`. With `omega + omega` the winding is `2`. The compatible
    complex structure for `-omega` is `-J`, so the rotation loop has
    `det_C = e^{-i theta}` there.
  - Let `D` be an indefinite quaternion algebra over `Q`, and let `mu in D`
    satisfy `trd mu = 0` and `nrd mu != 0`. Then `B_mu(x, y) = trd(xbar y mu)`
    is alternating (`B_mu(x, x) = nrd(x) trd(mu) = 0`), nondegenerate, and
    left-`D^1`-invariant.
  - Over `R`, `D = M_2(R)`. Write `xbar = J^T x^T J`. Then
    `B_mu = sum_{ij} s_{ji} omega(x_i, y_j)` on columns, with
    `s = mu J^T` symmetric and `det s = nrd mu`.
  - Diagonalizing `s` orthogonally, which commutes with the left action, gives
    `B_mu = lambda_1 omega + lambda_2 omega`. The winding is
    `sign(lambda_1) + sign(lambda_2)`: `0` if `nrd mu < 0` and `±2` if
    `nrd mu > 0`. E2 matches: `mu` hyperbolic gives `0`, elliptic gives `-2`.
  - When `nrd mu < 0`, `s` has an isotropic vector `v`. The column space
    `R^2 (x) v` is then a `D^1(R)`-invariant real Lagrangian, so (i) already
    covers these packets.
  - The rational embedding of an order `O^1` into a `Gamma`-commensurable
    group is only sketched: choose a rational symplectic basis for `B_mu`.
    Nothing below depends on it.

### 3.6 Rational symplectic planes

**Proposition 3.6.** Let `W <= Q^4` be a rational 2-plane with `omega|_W`
nondegenerate, and let `B_0 <= Gamma` preserve `W`. Then `B_0` is not
Maslov-carrying.

*Proof.*

**Setup.** `W^perp` is rational and nondegenerate, and `B_0` preserves it.
Put `S_1 = Sp(W_R)` and `S_2 = Sp(W^perp_R)`, both `SL_2(R)`, and
`iota_0 : S_1 x S_2 -> G`.

**Each factor.** Symplectic planes are `G`-conjugate by Witt's theorem. The
standard block `Sp(span(e1, f1))` has winding `±1`: its rotation loop is
`diag(e^{i theta}, 1)` in `U(2)` (numerically `1` in E2). So
`S~_i := p^{-1}(S_i)` is connected, and `S~_i -> S_i` is the universal cover
with kernel `<z>`.

**The factors commute.** The commutator map `S~_1 x S~_2 -> G~` is continuous
with values in `p^{-1}(1) = <z>`, and equals `1` at `(1, 1)`. So it is
constantly `1`, and `mu : S~_1 x S~_2 -> G~`, `(a, b) -> ab`, is a
homomorphism covering `iota_0`.

**The class.** On kernels `mu` is the sum map `Z^2 -> Z`. So `mu` is a morphism
from the product extension to `G~`, along `sum`. Hence
`iota_0^* e = pr_1^* eps_1 + pr_2^* eps_2` in `H^2((S_1 x S_2)^delta; Z)`,
where `eps_i` is the class of `S~_i`.

**Evaluation.** Restrict to `B_0`. For `y in H_2(B_0; Z)`,
`<e, iota_* y> = <eps_1, pr_{1*} y> + <eps_2, pr_{2*} y>`. Now `pr_1(B_0)`
preserves the rank-2 lattice `W cap Z^4` with determinant one, so it lies in
`SL(W cap Z^4) = SL_2(Z)`. It is therefore virtually free, and `pr_{1*} y`
is torsion. Since `Z` is torsion-free, `<eps_1, pr_{1*} y> = 0`. The same
argument applies to `pr_2`. ∎

Example: for free groups `F_a, F_b` of finite index in `SL_2(Z)`, the
packet `F_a x F_b <= SL_2(Z) x SL_2(Z) <= Gamma` has
`H_2(-; Q) = H_1(F_a; Q) (x) H_1(F_b; Q) = Q^(a b) != 0` by Kunneth, yet it
is not Maslov-carrying. So (P2) with Proposition 3.6 is not implied by (P1).

### 3.7 Assembly

**Theorem 3.7.** Let `w in Gamma * <t>` be nonsingular. Then `w` is pruned if
some `B <= Gamma` containing the coefficients of `w` has a finite-index
subgroup `B_0` satisfying one of:

- (P1) `H_2(B_0; Q) = 0`: for example `B_0` free, or virtually free.
- (P2) `B_0` preserves a proper nonzero rational subspace:
  - of dimension 1 or 3, by Proposition 3.3;
  - of dimension 2 and Lagrangian, by Example 3.5(i);
  - of dimension 2 and symplectic, by Proposition 3.6.

  An alternating form on a 2-plane has rank 0 or 2, so this list is complete.
- (P2') `B_0` preserves a real subspace `X` whose rational hull `X^Q` is
  proper. `X^Q` is the smallest rational subspace containing `X`. Since
  `b X^Q = (bX)^Q` for `b in GL_4(Q)`, `B_0` preserves `X^Q`, and (P2)
  applies.
- (P3) `B_0` preserves a real Lagrangian subspace: Example 3.5(i).
- (P4) `B_0` lies in a `G`-conjugate of a winding-zero connected Lie
  subgroup: Proposition 3.4. Examples are `SL_2(C)` for `Im det` forms, hence
  Bianchi packets.

*Proof.* In each case `B_0` is not Maslov-carrying. By Lemma 3.2, neither is
`B`. By Lemma 3.1, `w` is pruned. ∎

**Corollary 3.7'.** Let `w` be a witness and `B <= Gamma` any subgroup
containing its coefficients. Then:

- `B` is Maslov-carrying, and in fact `<e, iota_* K_2(B, w)> ⊄ 3Z`.
- No finite-index subgroup of `B` preserves a proper rational subspace (strong
  `Q`-irreducibility).
- No finite-index subgroup of `B` preserves a real Lagrangian, or a real
  subspace with proper rational hull.
- No finite-index subgroup of `B` lies in a conjugate of a winding-zero
  connected Lie subgroup.
- By `amenable-coefficients-have-zero-schur-kernel`, `B` is also non-amenable.

**Remark 3.7'' (overlap with parallel work).** At the time of writing, an
in-flight node by another agent (`deligne-multiplier-trivial-on-sl2xsl2-and-parabolics`,
not in the landed graph) states that `alpha` restricts to a circle coboundary
on `SL_2(Z) x SL_2(Z)`, on `P_S(Z)` and on `P_K(Z)`, so `alpha_H` vanishes on
the images of their second homology. Via Lemma 3.1 that prunes the same
standard packets mod 3. The results here were obtained independently, by
different arguments. They differ in three ways:

- they give the integral pairing `<e, -> = 0`, hence all Deligne covers
  `Gamma_n` at once;
- they cover the real Lagrangians and the rational symplectic planes whose
  lattices are not unimodular, which are not `Gamma`-conjugate to the
  standard subgroups;
- they add the winding-zero packets of Proposition 3.4.

**Remark 3.8 (mod-3 variant).** Suppose `S` has winding in `3Z` and
`[B : B_0]` is prime to 3. The same argument then lifts `B_0` to
`G~/<z^3>`, so `alpha|_{B_0} = 0`. A transfer with index prime to 3 then
gives `alpha_H(iota_* H_2(B)) = 0`. Every winding computed here is
`0, ±1` or `±2`, so this variant prunes nothing new in these examples.

## 4. Hosts: a rational variant of the real-symplectic pruning

**Theorem 4.1.** Let `w in Gamma * <t>` be nonsingular and `phi : Gamma -> L`
a homomorphism. Suppose `w_phi` has a solution in `L`, and
`phi_* (x) Q : H_2(Gamma; Q) -> H_2(L; Q)` is nonzero. Equivalently,
`phi^* : H^2(L; Q) -> H^2(Gamma; Q)` is nonzero. Then `K_2(Gamma, w) <= F`,
so `w` is pruned: `<e, K_2> = 0`, and every `ev(e_n)` vanishes on `K_2`.

*Proof.* By Lemma 1.3, `K_2 <= ker phi_*`. Since `H_2(Gamma; Q) = Q`,
`phi_* (x) Q` is injective. If `y in ker phi_*` had a nonzero `Z<h>`-component,
then `y (x) 1 != 0` would lie in the kernel of `phi_* (x) Q`. So
`ker phi_* <= F`. ∎

**Proposition 4.2 (hosts).** The hypothesis `phi_* (x) Q != 0` holds in the
following cases.

- (H1) `L <= Sp_{2g}(R)`, `g >= 2`, containing the block image of `Gamma`,
  with `phi` the block embedding.
  - The block inclusion `Sp_4(R) -> Sp_{2g}(R)` is an isomorphism on
    `pi_1 = Z` (`U(2) -> U(g)`, `det_C`). So the universal cover of
    `Sp_{2g}(R)` pulls back to `G~`, compatibly with the kernels.
  - Let `e_L` be the pullback class on `L`. Then `phi^* e_L = e`, and
    `<e_L, phi_* h> = d != 0`.
- (H2) `L` is obtained from `Gamma` by finitely many amalgams or HNN
  extensions along subgroups with `H_2(-; Q) = 0`, or is a directed union of
  such groups, with `phi` the inclusion (Lemma 1.4). Examples are iterated
  root adjunctions `Gamma *_{c = s^k} <s>`.
- (H3) Composites: `L` is obtained by (H2)-type constructions over a group
  `L_1` of type (H1). The class `phi_* h != 0` in `H_2(L_1; Q)` survives, by
  Lemma 1.4.

*Relation to `real-symplectic-solutions-kill-no-deligne-schur-class`.*

- For (H1) hosts, the pruned set equals the set pruned by (RS3) of that node,
  because a solution in `L` is a solution in `Sp_{2g}(R)`. Theorem 4.1 gives
  `K_2 <= F` rather than only `alpha_H(K_2) = 0`. That is no real gain: (RS1)
  applied with `H^ = ` the universal cover (kernel `Z`, pulling back to
  `Gamma~`) already gives `<e, K_2> = 0`, which is equivalent to `K_2 <= F`.
- For root adjunctions `L = Gamma *_{c = s^k} <s>`, `Gamma~` itself extends to
  `L`. The preimage `P` of `<c>` in `Gamma~` is abelian, generated by `z` and
  a lift `c~` with `c~^m = z^j` if `c` has order `m` (no relation if `c` has
  infinite order). Put `Q_s = <z, s~ | z central, s~^{km} = z^j>` (no
  relation in the infinite-order case). Then `c~ -> s~^k` embeds `P` in
  `Q_s`, and `Gamma~ *_P Q_s` is a central extension of `L` by `<z>`
  restricting to `Gamma~`. So (RS1) with kernel `Z` gives the same conclusion
  as Theorem 4.1 for these hosts. For general (H2) hosts, `Gamma~` need not
  extend.
- Any central extension of a host by `Z` pulling back to `Gamma~` forces
  `phi_* h` to have infinite order, since `<e_L, phi_* h> = d != 0`. So
  Theorem 4.1 contains (RS1) with kernel `Z`, and needs only a rational class.
  (RS1) with kernel `Z/3` does not need `phi_* (x) Q != 0`, so it is not
  obviously comparable. The new content of Section 4 is modest.

## 5. Witness checklist (necessary conditions)

A witness `w in Sp_4(Z) * <t>` must satisfy all of the following.

- (W1) `deg_t w != 0` and `3` does not divide `d` (Theorem 2.2(i)).
- (W2) `K_2` has rank one, and `<e, K_2> = d m Z` with `d m = ±2 mod 6`
  (Theorem 2.2(ii), (iv); (iv) carries the dependency flag of Section 2).
- (W3) `H_2(A_w; Q) = 0`, and `H_2(A_w; Z)` is finite (Theorem 2.2(iii)).
- (W4) Every nonsingular `u` with `w in <<u>>` is again a witness. No such `u`
  is aspherical, and no such `u` has torsion-free coefficients with an
  amenable reduced shape (Corollary 1.2).
- (W5) `w` has no solution in any host of Proposition 4.2, and more generally
  in any `L` with `phi^* : H^2(L; Q) -> H^2(Gamma; Q)` nonzero (Theorem 4.1).
- (W6) Every coefficient-containing `B <= Gamma` is non-amenable and
  Maslov-carrying. Every finite-index subgroup of `B` satisfies all of:
  - it preserves no proper rational subspace;
  - it preserves no real Lagrangian;
  - it preserves no real subspace with proper rational hull;
  - it lies in no conjugate of a winding-zero connected Lie subgroup, such as
    Siegel `P_S^0`, `SL_2(C)` (Bianchi), the diagonal `SL_2(R)` in
    `omega + (-omega)`, or `D^1(R)` with `nrd mu < 0`;
  - its rational second homology is nonzero (Corollary 3.7').

## 6. What is not proved, and open edges

- **No witness and no refutation.** The target remains OPEN.
- **Totally irrational real subspaces.**
  - A finite-index `B_0` might preserve a real line, or a real symplectic
    plane, whose rational hull is all of `Q^4`.
  - The real Klingen parabolic contains the block `SO(2)` and has winding 1.
  - The product `SL_2(R) x SL_2(R)` of a real splitting has winding
    `(±1, ±1)` on its factors.
  - Neither is pruned here. The Hilbert modular packets `SL_2(O_K)`, `K` real
    quadratic, act on `O_K^2` preserving the trace form
    `tr_{K/Q} det[x y]`. After a rational change of basis a finite-index
    subgroup lies in `Gamma`, and by the argument of Proposition 3.6 it has
    `iota^* e = eps_1 ± eps_2` over the two real places. The projections are
    dense in `SL_2(R)`, so the torsion argument of Proposition 3.6 is not
    available. These packets are expected to be Maslov-carrying, but this is
    not proved here.
- **Nonzero-winding Lie subgroups.**
  - The principal `SL_2` (`Sym^3`) has winding `-2` in E2, and
    `D^1(R)` with `nrd mu > 0` has winding `±2`.
  - No classification of winding-zero subgroups is attempted.
  - Zariski density of a witness packet is **not** forced by these results.
- **Finite-index packets.** If the coefficients generate a finite-index
  subgroup of `Gamma`, every packet criterion is vacuous. That is where the
  search must go, together with thin Zariski-dense packets of nonzero rational
  `H_2`.
- **(iv) of Theorem 2.2** rests on the flagged direction of (DR2).

## 7. Computations

Directory: `experiments/sp4-schur-deligne-packet-pruning-2026-09-16/`.
Files: `verify.py` (python3, numpy, sympy) and `output.txt` (full run output,
ending `ALL PASS`).

- **E1 (exact, sympy).** For `d in {1,2,3,7,11,15,19}`:
  - the Bianchi Gram matrix of `beta_d` is integral, alternating, with
    determinant `1`;
  - the generators `U1`, `Uw` and `S` of `SL_2(O_d)` act by integer
    determinant-one matrices preserving `beta_d`;
  - `(e1, e2 - t e1, e4, e3)` is symplectic.
- **E2 (numerical).** Winding numbers of loops in `Sp_4(R)`, from the polar
  decomposition `X + iY` of the unitary part, `det_C`, and unwrapping over
  `N = 2000` samples. Results:

  | loop | winding |
  | --- | --- |
  | standard block `SL_2` | 1 |
  | Klingen Levi | 1 |
  | diagonal `omega + omega` | 2 |
  | diagonal `omega + (-omega)` | 0 |
  | Siegel Levi | 0 |
  | Siegel non-compact loop | 0 |
  | principal `Sym^3` | -2 |
  | `SL_2(C)` torus | 0 |
  | quaternion `mu` elliptic | -2 |
  | quaternion `mu` hyperbolic | 0 |

  These are cross-checks. The proofs above do not depend on them.
- **E3 (exact).** The Klingen radical Lie algebra has dimension 3 and center of
  dimension 1. `m(1,-I)` acts by `-1` on `n/center` and `+1` on the center.
  The matrices `n(a,b,c)` are symplectic, the product law is as in Step 1,
  `[n(1,0,0), n(0,1,0)] = n(0,0,2)`, and
  `m(1,-I) n(a,b,c) m(1,-I)^{-1} = n(-a,-b,c)`.

## 8. Sources

Consulted 2026-09-16 via arXiv abstract pages:

- M. Stover, *Residual finiteness and discrete subgroups of Lie groups*,
  arXiv:2407.07680 (v1 2024-07-10, v2 2025-01-24). Thm 1.5 (Deligne) is
  quoted in the graph route `sp4-fd-projective-multiplier-finiteness-proof`.
  The theorem text was not re-read here.
- R. Ji, C. Ogle, B. Ramsey, *Relative Amenability and Relative Soficity*,
  arXiv:1807.07600. Withdrawn (v4 2019-01-10, "Error in proof of
  Theorem 3.15"). Not used.
- L. Funar, W. Pitsch, *Finite quotients of symplectic groups vs mapping
  class groups*, arXiv:2004.04129 (v2 2021-09-09), North-Western European
  J. Math. 8 (2022) 111--166. Background on finite quotients of `Sp_2g(Z)`
  and its central extensions; not used in a proof.
- A. A. Klyachko, M. A. Mikheenko, V. A. Roman'kov, *Equations over solvable
  groups*, arXiv:2303.13240 (v3 2023-10-19). Background; not used.
- M. A. Mikheenko, *On p-nonsingular systems of equations over solvable
  groups*, arXiv:2309.09096 (v3 2024-01-23). Background; not used.
- M. A. Mikheenko, *Infinite systems of equations in abelian and nilpotent
  groups*, arXiv:2410.20729 (v3 2025-07-01). Background; not used.
- M. Nitsche, A. Thom, *Universal solvability of group equations*,
  arXiv:1811.07737 (v2 2021-09-23). Already pinned in
  `kervaire-laudenbach-holds-for-hyperlinear`.
- A. A. Klyachko, *The Kervaire--Laudenbach conjecture and presentations of
  simple groups*, arXiv:math/0409146 (2004), Algebra and Logic 44 (2005).
  Background; not used.

None of these sources studies Schur kernels of adjunctions over `Sp_4(Z)`.
No priority is claimed for the elementary lemmas of Section 1. Brown,
*Cohomology of Groups* (GTM 87), is cited for standard facts and was not
re-read.
