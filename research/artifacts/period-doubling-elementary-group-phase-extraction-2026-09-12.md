# The period-doubling subshift algebra is its own matrix ring

Lane `ex-nh-fresh`, 2026-09-12. Supports `period-doubling-subshift-algebra-is-its-own-matrix-ring`
and Section 3 of `nh-fresh-route-map-2026-09-12.md`. Complete written proof, unreviewed.

## 0. Setup

- `z(n) = nu_2(n) mod 2` for `n != 0`, and `z(0) = 0`. `X` is the orbit closure of `z` in
  `{0,1}^Z`, with shift `(Tx)(i) = x(i+1)`. `X` is the period-doubling Toeplitz subshift, which is
  minimal and infinite.
- `A = LC(X,F_2) ⋊_T Z`, the algebraic crossed product: finite sums `sum_n f_n u^n` with
  `u f u^(-1) = f o T^(-1)`, so `u chi_Y u^(-1) = chi_(TY)` for clopen `Y`.
- This is the ring of `kazhdan-groups-without-fd-reps-violate-two-root-identity` and an instance of
  `minimal-subshift-algebra-is-simple-lef-ring`.

## 1. Odometer phases

**Lemma 1.** For `x in X` and `j >= 1` there is a unique `a = a_j(x) in Z/2^j` with

```text
x(i) = nu_2(a + i) mod 2      whenever  a + i != 0 mod 2^j.                    (P1)
```

The map `a_j` is locally constant, and `a_j(Tx) = a_j(x) + 1`.

*Proof.*
1. *Orbit points.* For `x = T^m z`, `x(i) = z(m+i)`. If `m + i != 0 mod 2^j` then
   `nu_2(m+i) < j` is determined by `m + i mod 2^j`, so `a = m mod 2^j` satisfies (P1).
2. *Existence.* For fixed `a`, (P1) is a conjunction of coordinate conditions, so the set of `x`
   satisfying it is closed. If `T^(m_k) z -> x`, pass to a subsequence with `m_k mod 2^j` constant;
   the limit satisfies (P1) for that residue.
3. *Reduction.* If `b` satisfies (P1) at level `j+1`, then `b mod 2^j` satisfies (P1) at level `j`:
   when `b + i != 0 mod 2^j`, also `b + i != 0 mod 2^(j+1)` and `nu_2(b+i) < j` depends only on
   `b + i mod 2^j`.
4. *Uniqueness.* Suppose `a != a'` both satisfy (P1) at level `j`, and put `t = nu_2(a' - a) < j`.
   - *Case `t <= j - 2`.* Write `a' - a = 2^t d` with `d` odd, and pick `i` with
     `a + i = 2^t c mod 2^j`, where `c` is odd and `c + d = 2 mod 4`. Then `nu_2(a+i) = t` and
     `nu_2(a'+i) = t + 1 <= j - 1`, so (P1) forces `x(i) = t` and `x(i) = t + 1 mod 2`.
   - *Case `t = j - 1`.* (P1) for `a'` forces `x(i) = (j-1) mod 2` on the class
     `C = {i : a + i = 0 mod 2^j}`, since there `a' + i = 2^(j-1) mod 2^j`. By step 2 there are
     residues `b` at level `j+1` and `c` at level `j+2` satisfying (P1), and by step 3 we may take
     `c = b mod 2^(j+1)`. Also `b mod 2^j` is `a` or `a'`, by the first case applied to it and to
     each of `a, a'`; by symmetry say `b = a mod 2^j`. (P1) for `b` forces `x(i) = j mod 2` on
     `{i : b + i = 2^j mod 2^(j+1)}`, and (P1) for `c` forces `x(i) = (j+1) mod 2` on
     `{i : c + i = 2^(j+1) mod 2^(j+2)}`. Both sets lie in `C` and are nonempty, so `x` takes both
     parities on `C`, a contradiction.
5. *Clopen.* The `2^j` sets `{x : a_j(x) = a}` are closed, disjoint and cover `X`, so each is
   clopen. `(Tx)(i) = x(i+1)` gives `a_j(Tx) = a_j(x) + 1`. QED

Put `P_(j,a) = {x : a_j(x) = a}`. These are clopen, `T P_(j,a) = P_(j,a+1)`, and
`P_(j,a) = P_(j+1,a) ⊔ P_(j+1,a+2^j)`.

## 2. Matrix units

For `a, b in {0, ..., 2^j - 1}` put `E_ab = chi_(P_(j,a)) u^(a-b)`.

- `E_ab E_cd = chi_(P_a) chi_(T^(a-b) P_c) u^(a-d) = chi_(P_a) chi_(P_(c+a-b)) u^(a-d) = delta_bc E_ad`.
- `sum_a E_aa = 1`.
- `E^(j)_ab = E^(j+1)_ab + E^(j+1)_(a+2^j, b+2^j)`.

So `M_(2^j)(F_2)` sits unitally in `A`, compatibly in `j`, and `A ≅ M_(2^j)(E_00 A E_00)`.

## 3. The corner

Let `e = chi_(P_(1,0))`. Since `T^n P_(1,0)` equals `P_(1,0)` for even `n` and is disjoint from it
for odd `n`,

```text
e (f u^n) e = f chi_(P_(1,0)) chi_(T^n P_(1,0)) u^n,
```

which vanishes for odd `n`. So `eAe = { sum_m f_m u^(2m) : f_m in LC(P_(1,0), F_2) }`. This is the
algebraic crossed product `LC(P_(1,0),F_2) ⋊_(T^2) Z`, with `u^2 e` as the implementing unit.

## 4. Decimation conjugacy

**Lemma 2.** `D : P_(1,0) -> {0,1}^Z`, `D(x)(i) = 1 + x(2i) mod 2`, is a homeomorphism onto `X`
with `D o T^2 = T o D`.

*Proof.*
1. On `P_(1,0)`, (P1) with `j = 1`, `a = 0` makes every odd coordinate `0`. So `x` is determined by
   its even coordinates, and `D` is injective. It is continuous, and `D(T^2 x)(i) = 1 + x(2i+2) =
   D(x)(i+1)`.
2. *Orbit points.* For even `m`, `T^m z in P_(1,0)` and
   `D(T^m z)(i) = 1 + nu_2(m + 2i) = nu_2(m/2 + i) mod 2` when `m/2 + i != 0`, while
   `D(T^m z)(-m/2) = 1 + z(0) = 1`. So `D(T^m z) = T^(m/2) z'`, where `z'` is `z` with `z'(0) = 1`.
3. *`z'` lies in `X`.* For odd `k`, the window of `T^(2^k) z` of radius `< 2^k` equals that of `z`
   off the centre, and its centre is `nu_2(2^k) = k mod 2 = 1`. So `T^(2^k) z -> z'` along odd `k`.
4. The even-index orbit points are dense in `P_(1,0)` (it is clopen, and the orbit of `z` is dense in
   `X`). By 2 and 3, `D` maps them into `X`, so `D(P_(1,0)) ⊆ X`. The image is closed,
   `T`-invariant and contains `z'`, so by minimality it is `X`.
5. A continuous bijection of compact Hausdorff spaces is a homeomorphism. QED

## 5. Conclusion

**Theorem.** `A ≅ M_2(A)` as unital rings, hence `A ≅ M_(2^j)(A)` for every `j`, and

```text
EL_3(A) ≅ EL_(3·2^j)(A)      for every j >= 0.
```

*Proof.*
1. Lemma 2 gives `LC(P_(1,0),F_2) ⋊_(T^2) Z ≅ LC(X,F_2) ⋊_T Z` by `f -> f o D^(-1)`, `u^2 e -> u`.
   With Section 3, `eAe ≅ A`.
2. Section 2 with `j = 1` gives `A ≅ M_2(eAe) ≅ M_2(A)`. Iterate.
3. `EL_3(M_2(R)) = EL_6(R)` for any ring `R`. The block elementary matrices lie in `EL_6(R)`.
   Conversely `e_ij(r)` with `i, j` in different blocks is block elementary, and for `i != j` in one
   block `e_ij(r) = [e_ik(r), e_kj(1)]` with `k` in another block. Induct on `j`. QED

## 6. Calibration remark (commentary, not part of the claim)

- `S = EL_3(A)/Z` is the simple Kazhdan LEF group of `simple-kazhdan-lef-group-from-minimal-subshift`
  (review PASS recorded in its Part 1 artifact). By the Theorem it has the same matrix
  self-similarity as the binary Leavitt unit group, `Q ≅ GL_n(L_(F_2)(1,2))` for every `n`.
- `S` is not co-Hopfian: `g -> ι(g)`, acting by `g` on `(eA)^3` through `eAe ≅ A` and by the identity
  on `((1-e)A)^3`, is an injective endomorphism with proper image.
- It has no inner corner compression. If `w A ≅ w' A` for idempotents `w' <= w` with `w - w' != 0`,
  there are `p in w'Aw`, `p' in wAw'` with `p p' = w'` and `p' p = w`. The exact local models of
  `minimal-subshift-algebra-is-simple-lef-ring` are injective and multiplicative on a finite set
  containing these elements, so they send `w, w'` to idempotent matrices of equal rank with
  `w - w'` sent to a nonzero idempotent, a contradiction.
- In `Q` the prefix codes give module isomorphisms `L ≅ L ⊕ L`, hence inner compressors of corner
  Kazhdan subgroups and a nontrivial rigid defect. So matrix self-similarity, non-co-Hopfian
  corner embeddings and the UHF core `∪_j SL_(3·2^j)(F_2)` are all present in a sofic simple
  Kazhdan group. A nonhyperlinearity argument for `Q` through the rigid defect must use the inner
  compression itself.
