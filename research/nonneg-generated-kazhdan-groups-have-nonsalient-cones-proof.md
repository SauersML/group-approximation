---
rg: 2
id: nonneg-generated-kazhdan-groups-have-nonsalient-cones-proof
kind: route
title: Measure each coordinate only on its own open face of K/L, with Vinberg's function of that face, to make every nonnegative element block-unipotent, then kill the unipotent part with the lineality space
target: nonneg-generated-kazhdan-groups-have-nonsalient-cones
requires:
  - kazhdan-volume-rigidity-kills-interior-orthant-subpairs
  - galois-psd-monomial-subpair-has-no-infranormal-trace
  - monomial-origin-level-subpairs-cannot-certify-rank-three-cone
---

Notation is as in [[nonneg-generated-kazhdan-groups-have-nonsalient-cones]].  For `S ⊆ [d]` write
`O_S = R_+^S` and `e_S = Σ_(i∈S) e_i`.  For `g ∈ H` write `ḡ` for the induced map on `V/L`; it preserves `Q`.
`supp x = { i : x_i ≠ 0 }`.

## 0. Faces

`Q` is a pointed closed convex cone.  A face `F` of `Q` is a closed subcone such that `a, b ∈ Q`, `a + b ∈ F`
imply `a, b ∈ F`.  For `y ∈ Q` let `F(y)` be the smallest face containing `y`; then `y ∈ relint F(y)`.  Two
standard facts:

- (F1) if `y = Σ c_s y_s` with `c_s > 0` and `y_s ∈ Q`, then `F(y)` is the smallest face containing every `y_s`;
  in particular `y_s ∈ F(y)` for all `s`, and if every `y_s ∈ relint F` then `y ∈ relint F`;
- (F2) a linear automorphism `A` of `Q` maps faces to faces and `A F(y) = F(A y)`.

For `S ⊆ [d]` put `F_S = F(π e_S)` and let `𝒞 = { F_S : S ⊆ [d] }`, a finite set of faces.  By (F1), `F_S` is
the smallest face containing `π e_s` for all `s ∈ S`, and `π(O_S) ⊆ F_S`.

*Lemma 0.1.*  For a face `F`, `O ∩ π^(-1)(F) = O_(J(F))`.  *Proof.*  If `x ∈ O` with `π x ∈ F`, then
`π x = Σ x_i π e_i` with `π e_i ∈ Q`, so by the face property `π e_i ∈ F` whenever `x_i > 0`. ∎

## 1. Nonnegative elements permute 𝒞

*Lemma 1.1.*  For `g ∈ H_+` and `S ⊆ [d]`, `ḡ F_S = F_(supp(g e_S))`.  *Proof.*  `g e_S ∈ O` has support
`T = supp(g e_S)`, so `g e_S = Σ_(t∈T) c_t e_t` with `c_t > 0`.  By (F2) and (F1),
`ḡ F_S = F(ḡ π e_S) = F(π g e_S) = F(Σ c_t π e_t) = F_T`. ∎

So `ḡ` maps `𝒞` into `𝒞`, injectively (it is a bijection on faces).  `𝒞` is finite, so `ḡ` permutes `𝒞`, and so
does `ḡ^(-1)`.  If `H_+` generates `H`, then `H` acts on `𝒞` by permutations.  Let `H_1` be the kernel: a normal
subgroup of finite index, whose elements fix every `F ∈ 𝒞`.  Each `F ∈ 𝒞` spans a subspace `W_F ⊆ V/L`
preserved by `H_1`, and

```text
χ_F : H_1 → R_(>0)^× ,   h ↦ |det(h̄ |_(W_F))|
```

is a homomorphism.  If `H` is character-free, every `χ_F` is trivial.

## 2. The carrier partition and block triangularity

Assume `L ∩ O = 0`, so `π e_i ≠ 0` for all `i`.  The **carrier** of `i` is `F_i = F_({i}) ∈ 𝒞`.  For
`F ∈ 𝒞` put `A_F = { i : F_i = F } = { i : π e_i ∈ relint F }`.  The nonempty `A_F` partition `[d]`, and
`J(F) = ⋃_(F' ⊆ F) A_(F')`, the union over carriers `F' ∈ 𝒞` contained in `F`.

*Lemma 2.1.*  Let `g ∈ H_1 ∩ H_+`.  Then `supp(g e_i) ⊆ J(F_i)` for every `i`.  Consequently, for every
carrier `F`, `g` preserves `R^(J(F))` and `R^(J(F) \ A_F)`.  *Proof.*  `π g e_i = ḡ π e_i ∈ ḡ F_i = F_i`, and
`g e_i ∈ O`, so Lemma 0.1 gives `supp(g e_i) ⊆ J(F_i)`.  If `i ∈ J(F)`, then `F_i ⊆ F`, so
`J(F_i) ⊆ J(F)`.  If `i ∈ J(F) \ A_F`, then `F_i` is a proper face of `F`, so `F_i ⊆ ∂F` and
`J(F_i) ∩ A_F = ∅`. ∎

Order the carriers by a linear extension of inclusion and list the indices class by class.  Lemma 2.1 says
that `g ∈ H_1 ∩ H_+` is block upper triangular, with blocks indexed by carriers:

```text
g e_i = b_i + g_F e_i   for i ∈ A_F ,   with b_i ∈ O_(J(F) \ A_F),  g_F e_i ∈ O_(A_F) .
```

Here `g_F` is the `A_F × A_F` diagonal block: a nonnegative integer matrix.  Since `det g = ± 1` is the product of
the integer determinants `det g_F`, each `g_F ∈ GL(Z^(A_F))`, and `g_F` maps `O_(A_F)` into itself.

## 3. The diagonal blocks are permutations

Fix a carrier `F`, `n = dim W_F ≥ 1`.  `F` is a pointed closed cone with nonempty interior `relint F` in
`W_F`.  Let `φ_F(y) = ∫_(F*) e^(-<ξ, y>) dξ` be Vinberg's characteristic function of `F` in `W_F`, with `F*`
the dual cone in `W_F^*`.  It is finite, positive and continuous on `relint F`, homogeneous of degree `-n`, and:

- (Φ1) `φ_F(A y) = |det A|^(-1) φ_F(y)` for every linear automorphism `A` of `F`;
- (Φ2) `φ_F(y + c) ≤ φ_F(y)` for `y ∈ relint F`, `c ∈ F`, because `<ξ, c> ≥ 0` for `ξ ∈ F*`.

Let `g ∈ H_1 ∩ H_+` and assume `χ_F(g) = 1`.  For `y ∈ O_(A_F) \ 0`, `π y ∈ relint F` by (F1), since every
`π e_i`, `i ∈ A_F`, lies in `relint F`.  Put `f(y) = φ_F(π y)` and `w(y) = exp(-f(y)^(-1/n))`, and `w(0) = 0`.

*Monotonicity.*  For `y ∈ O_(A_F)`, Lemma 2.1 gives `g y = b + g_F y` with `b ∈ O_(J(F) \ A_F)`, so
`π b ∈ F`.  By (Φ1) with `χ_F(g) = 1`, then (Φ2):

```text
f(y) = φ_F(ḡ π y) = φ_F(π g y) = φ_F(π g_F y + π b) ≤ φ_F(π g_F y) = f(g_F y) .
```

`t ↦ exp(-t^(-1/n))` is increasing on `(0, ∞)`, so `w(g_F y) ≥ w(y)`.

*Finite mass.*  `f^(-1/n)` is positive, continuous and homogeneous of degree `1` on `O_(A_F) \ 0`, so it is
at least `c Σ y_i` for some `c > 0`, by compactness of the simplex.  So `μ = w dy` has `μ(O_(A_F)) < ∞`, and
`w > 0` on `O_(A_F) \ 0`.

*Conclusion.*  `|det g_F| = 1`, so

```text
μ(O_(A_F)) ≥ μ(g_F O_(A_F)) = ∫_(O_(A_F)) w(g_F y) dy ≥ μ(O_(A_F)) .
```

Equality holds, so `μ(O_(A_F) \ g_F O_(A_F)) = 0`.  `g_F O_(A_F)` is a closed cone.  If it were a proper subset,
its complement in `O_(A_F)` would be a nonempty relatively open set, which meets the dense open set
`int O_(A_F)` in a nonempty open set of positive `μ`-mass.  So `g_F O_(A_F) = O_(A_F)`.  A linear automorphism
of an orthant permutes its extreme rays, `g_F e_i = c_i e_(σ i)` with `c_i ∈ Z_(>0)`, and `∏ c_i = |det g_F| = 1`.
So `g_F` is a permutation matrix.

*Remark.*  This is (V1) of [[kazhdan-volume-rigidity-kills-interior-orthant-subpairs]] run on one graded piece.
There the whole orthant was weighed with `φ_Q`, and coordinates with `π e_i ∈ ∂Q` made the mass infinite.  Here a
coordinate is weighed only by the function of its own carrier face, where it is interior.  The cross term
`π b` is harmless, because (Φ2) turns it into an inequality in the right direction.

## 4. The unipotent part and (W1)

*Lemma 4.1.*  Assume `L ∩ O = 0`.  If `u ∈ H` and `N = u - 1` is nilpotent with `N ≥ 0` entrywise, then `u = 1`.
*Proof.*  Suppose `N ≠ 0`.  Pick `i` and `m ≥ 1` with `N^m e_i ≠ 0 = N^(m+1) e_i`.  Put `x = N^(m-1) e_i ≥ 0` and
`v = N x ∈ O \ 0`.  Then `N^2 x = 0`, so `u^(-n) x = (1 + N)^(-n) x = x - n v` for `n ≥ 1`.  Now
`u^(-n) x ∈ H · O ⊆ K`, so `-v = lim (x - n v)/n ∈ K`.  Also `v ∈ O ⊆ K`.  So `v ∈ L ∩ O = 0`, a
contradiction. ∎

*Lemma 4.2.*  A nonnegative `g ∈ GL_d(Z)` of finite order is a permutation matrix.  *Proof.*  `g^(-1)` is a
power of `g`, hence nonnegative.  A nonnegative matrix with nonnegative inverse is monomial: row `i` of `g^(-1)`
against column `j` of `g` gives `0` for `i ≠ j`, a sum of nonnegative terms, which forces disjoint supports.
Integral monomial matrices with integral inverse have entries `± 1`, here `1`. ∎

*Proof of (W1).*  Let `g ∈ H_+` and let `N = [H : H_1]`.  Then `g^N ∈ H_1 ∩ H_+`.  `H_1` has finite index in
`H`, so it is character-free, and `χ_F(g^N) = 1` for every carrier `F`.  By §3, every diagonal block of `g^N`
is a permutation matrix.  Let `M` be the lcm of their orders.  `u = g^(NM)` is block upper triangular,
nonnegative, with identity diagonal blocks, so `u - 1` is nilpotent and `u - 1 ≥ 0`.  By Lemma 4.1, `u = 1`.  So `g` has finite
order, and by Lemma 4.2 it is a permutation matrix.  `H` is generated by permutation matrices, so `H` is finite. ∎

## 5. (W2): the recursion through L ∩ O

Let `H` be character-free, generated by `H_+`, and infinite.  We find a nonempty `M` with `R^M ⊆ K0`.

By (V3) of [[kazhdan-volume-rigidity-kills-interior-orthant-subpairs]] (§4 of its proof), `L ∩ O = O_J`,
`H` preserves `R^J`, and in the block form `g = [[a, b], [0, c]]` the pieces `H_J = { a }` and `H' = { c }` are
generated by their nonnegative elements (the blocks of `H_+`), and the quotient piece has `L'' ∩ O' = 0`.  Both
pieces are quotients of `H`, so they are character-free.

- If `J = ∅`, then `L ∩ O = 0` and (W1) makes `H` finite.  So `J ≠ ∅`.
- By (W1), the quotient piece `H'` is finite.
- If `H_J` were finite too, a finite-index `H_2 ≤ H` would act trivially on both pieces, so `g ↦ b` would embed
  `H_2` in the free abelian group `Hom(Z^(J^c), Z^J) ≅ Z^r`.  Then `H_2` is free abelian of finite rank.  If it
  were nontrivial it would map onto `Z`, hence onto `2^Z ≤ R_(>0)^×`, against character-freeness of the
  finite-index subgroup `H_2`.  So `H_2 = 1` and `H` would be finite.  So `H_J` is infinite.

Now repeat with `H_J` acting on `Z^J`, with its own cone `K_J = closure of cone(H_J · O_J)` and lineality
`L_J`.  `H_J` is character-free, generated by nonnegative matrices, and infinite.  If `L_J ∩ O_J = O_(J_2)` with
`J_2 ⊊ J`, the same three steps apply in dimension `|J| < d`.  The dimension drops at each step, so the recursion
stops at a coordinate subspace `R^M`, `M ≠ ∅`, preserved by `H` (each step's subspace is preserved by the
previous piece, hence by `H`), on which `H` acts through an infinite piece `H_M` with `L_M ∩ O_M = O_M`.

Then `± O_M ⊆ K_M`, so the closed convex cone `K_M` spans and contains `-K_M ⊇ O_M`, whence
`K_M ⊇ O_M - O_M = R^M`.  A convex cone whose closure is `R^M` has nonempty interior and equals the interior of
its closure, so `cone(H_M · O_M) = R^M`.  Since `H` acts on `R^M` through `H_M`,

```text
K0 = cone(H · O) ⊇ cone(H · O_M) = cone(H_M · O_M) = R^M .
```

So `K0` contains a line.  Contrapositively, a salient `K0` forces `H` finite. ∎

## 6. (W3)

By (M2) of [[monomial-origin-level-subpairs-cannot-certify-rank-three-cone]], a line in `K0` gives
`psi(C) = F`, whose centraliser in the centreless `F` is trivial.  If `K0` is salient, (N1) of
[[galois-psd-monomial-subpair-has-no-infranormal-trace]] says `C` is infranormal in `B_(H,k)` only if `H_+`
generates `H`.  A Kun-Thom certificate needs `B` Kazhdan, so its quotient `H` is Kazhdan, hence character-free,
and (W2) makes `H` finite.  Then (M4) makes `C` profinitely closed, so an infranormal `C` is normal, and the
certificate fails.  So no `B_(H,k)` certifies nonsoficity of `T_3`, for any `H ≤ SL_d(Z)`, `k ≥ 1`, `q`, `d`. ∎

## 7. Where each hypothesis is used

- Character-freeness: in §3 (`χ_F(g^N) = 1` on each carrier face) and in the abelian step of §5.  The example
  `[[3,4],[2,3]]` (§6 of the volume node) shows the first use cannot be dropped; `[[1,1],[0,1]]` shows the
  second cannot.
- Nonnegative generation: to make `H` act on the finite set `𝒞`, so that `H_1` has finite index and is
  character-free.  For a single nonnegative `g` in a group not generated by `H_+`, the stabiliser of a face
  need not have finite index, and §3 needs `χ_F(g^N) = 1` from elsewhere.
- `L ∩ O = 0`: only in Lemma 4.1 and to make carriers defined; §5 reduces to it.
