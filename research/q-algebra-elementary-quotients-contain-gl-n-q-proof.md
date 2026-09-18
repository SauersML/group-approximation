---
rg: 2
id: q-algebra-elementary-quotients-contain-gl-n-q-proof
kind: route
title: Scalar centralizers, the block embedding and block elementary matrices
target: q-algebra-elementary-quotients-contain-gl-n-q
requires: []
---

Write `E_ij` for the matrix units and `e_ij(r) = I + r E_ij`. Commutators are
`[x,y] = x y x^-1 y^-1`. For distinct `i, l, j` the standard identity is
`[e_il(a), e_lj(b)] = e_ij(ab)`.

**1. `Q ⊆ Z(R)`.** Integers are central. If `b != 0` is an integer and `x ∈ R`,
then `x b = b x`. Multiplying by `b^-1` on both sides gives `b^-1 x = x b^-1`.
So `a/b = a b^-1` is central.

**2. Centralizer.** Let `g ∈ GL_N(R)` commute with every `e_ij(r)`, `i != j`.
Then `g (r E_ij) = (r E_ij) g` for all `r`.
- With `r = 1`: `g E_ij` has column `j` equal to column `i` of `g` and zeros
  elsewhere. `E_ij g` has row `i` equal to row `j` of `g` and zeros elsewhere.
  Comparing entries gives `g_ki = 0` for `k != i`, `g_jl = 0` for `l != j`, and
  `g_ii = g_jj`. Letting `(i,j)` range over all ordered pairs (`N >= 2`) shows
  `g = dI`.
- With general `r`: `d r = r d`, so `d ∈ Z(R)`. Since `g` is invertible,
  `d x = 1` for the diagonal entry `x` of `g^-1`, so `d ∈ Z(R)^x`.

Conversely `dI`, `d ∈ Z(R)^x`, commutes with every matrix. The centre of
`E_N(R)` is the part of `E_N(R)` inside this centralizer.

**3. PSL_N(Q).** Over the field `Q`, `SL_N(Q) = E_N(Q)`. The injective unital
map `Q -> R` induces an injective homomorphism `ι: GL_N(Q) -> GL_N(R)`, with
`ι(E_N(Q)) ⊆ E_N(R)`.
- If `ι(g) ∈ Z(E_N(R))` then `ι(g) = dI` by part 2. So `g` is a scalar matrix
  of `SL_N(Q)`, i.e. `g ∈ Z(SL_N(Q))`.
- Conversely `λI ∈ SL_N(Q)` maps to `λI` with `λ` central in `R` (part 1), which
  lies in `E_N(R)` and is central there.

So the kernel of `SL_N(Q) -> PE_N(R)` is exactly `Z(SL_N(Q))`.

**4. GL_n(Q).** `β(g) = diag(g, det(g)^-1, I_(N-n-1))` is a homomorphism
`GL_n(Q) -> SL_N(Q)`, because the determinant is multiplicative and `Q` is
commutative. It is injective. If `β(g)` is a scalar `λI`, then the last diagonal
entry (present since `N >= n+2`) gives `λ = 1`, so `g = I`. So `β(GL_n(Q))`
meets `Z(SL_N(Q))` trivially. Composing with part 3 gives the embedding.

**5. Matrix rings.** Index `{1..Nk}` by pairs (block `I`, position `a`).
- `⊆`: for blocks `I != J` and `A ∈ M_k(R)`, `e_IJ(A)` is the product of the
  `e_((I,a),(J,b))(A_ab)`. These commute, since `E_((I,a),(J,b)) E_((I,a'),(J,b')) = 0`
  when `J != I`.
- `⊇`: `e_uv(r)` with `u`, `v` in different blocks is `e_IJ(r E_ab)`. If `u != v`
  lie in one block, pick `w` in another block (`N >= 2`). Then
  `e_uv(r) = [e_uw(r), e_wv(1)]`, and both factors are block elementary.

A unital ring isomorphism `φ: R -> M_2(R)` induces `GL_N(R) ≅ GL_N(M_2(R)) = GL_(2N)(R)`.
It carries `E_N(R)` onto `E_N(M_2(R)) = E_(2N)(R)` and centres to centres. So
`PE_N(R) ≅ PE_(2N)(R)`, and by induction `PE_N(R) ≅ PE_(2^j N)(R)`. Given `n`,
choose `j` with `2^j N >= n+2` and apply part 4 to `PE_(2^j N)(R)`. ∎
