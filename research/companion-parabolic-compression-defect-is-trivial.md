---
rg: 2
id: companion-parabolic-compression-defect-is-trivial
kind: claim
title: The Laurent companion automorphism traps every compression defect in the central tail
distinct_from:
  torsion-free-lef-kazhdan-non-rf-seed: That constructs the one-row characteristic-zero parabolic seed; this tests the multi-row companion refinement and proves that its natural compressed Kazhdan subgroup has trivial ambient defect.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: That is the positive target requiring the defect to fill the kernel; this is a scoped no-go for the most direct companion/parabolic attempt at that target.
  finite-outer-order-mapping-torus-is-virtually-product: That excludes periodic outer actions abstractly; the companion action here has infinite order, and the obstruction instead comes from an exact centralizer and determinant calculation.
  mapping-torus-mf-radical-lies-in-finite-residual: That universally rules out every automorphism of the seed by its proper finite residual; this explicitly constructs the tempting companion automorphism, closes its central-relator orbit, and proves the sharper statement that its natural Kazhdan compression defect is literally trivial.
artifacts:
  - research/torsion-free-lef-kazhdan-non-rf-seed.md
---

**ESTABLISHED (scoped no-go).**  Put `R=Z[t,t^(-1)]`, `S=Z[t]`, and let
`H_m(R)` be the block parabolic

```text
       [ I_m  U  c ]
       [  0   h  v ],        h in EL_3(R),
       [  0   0  1 ]
```

with `U in Mat_(m x 3)(R)`, `v in R^3`, and `c in R^m`.  Its centre is
`C(R)={c in R^m}`.  Set

```text
J_m = H_m(R)/C(S^m).                                  (CP1)
```

For `P in GL_m(S)` and `q=t^d`, `d>0`, conjugation by

```text
D=diag(qP,I_3,q)
```

induces an honest automorphism `phi=phi_(P,q)` of `J_m`, given on block
coordinates by

```text
U |-> qPU,       h |-> h,       v |-> q^(-1)v,
c mod S^m |-> Pc mod S^m.                              (CP2)
```

Let `A_m(S)` be the image in `J_m` of the upper affine subgroup with
`h in EL_3(S)`, `U in Mat_(m x 3)(S)`, and `v=c=0`.  It is Kazhdan, and

```text
phi(A_m(S)) properSubset A_m(S),                       (CP3)
```

because the `U`-module is carried onto `q Mat_(m x 3)(S)`.

Nevertheless this compression produces no Kazhdan compression defect.  More
precisely, let `K` be any `phi`-invariant finite-index subgroup of `J_m` and
put `L=K intersect A_m(S)`.  In the mapping torus

```text
G=K semidirect_phi Z
```

one has

```text
C_G(L) = K intersect Z(J_m).                           (CP4)
```

Consequently, for **every** `KazhdanCompressionCore` in `G` whose source
image is `L` (with any compressor in `G` and any permitted centralizing root),

```text
defectSet = {1},             defectNormal = 1.          (CP5)
```

Consistently with `mapping-torus-mf-radical-lies-in-finite-residual`, there is
also a broader obstruction that does not depend on choosing this
natural `L`.  The quotient by the whole surviving central tail has a faithful
finite-dimensional representation over `Q(t)`, equivariant for `phi`; hence
it extends to a finite-dimensional representation of `G`.  Whole-defect
finite-dimensional sterility gives, for **every** compression core `B` in
`G`,

```text
B.defectNormal <= K intersect (C(R)/C(S^m)) properSubset K.  (CP5')
```

Thus no alternative Kazhdan subgroup or centralizing root inside this same
companion mapping torus can repair defect saturation.  For the natural
affine subgroup the sharper calculation `(CP4)` improves containment in the
central tail to literal triviality `(CP5)`.

Thus the companion/parabolic construction cannot satisfy
`defectNormal=K`, even though it supplies an honest infinite-order
automorphism and a strictly compressed Kazhdan subgroup.  The failure is not
a finite-presentation issue and cannot be repaired by taking the torsion-free
characteristic finite-index subgroup used in the seed construction.

The smallest companion is still useful for presentation bookkeeping.  For

```text
             [ t  -1 ]
P =          [ 1   0 ]  in SL_2(S),                    (CP6)
```

both `P` and `P^(-1)` have polynomial entries and

```text
P+P^(-1)=t I_2.
```

Hence `S^2` is cyclic as a `Z[P,P^(-1)]`-module: `e_2=-P^(-1)e_1` and
`t e_1=(P+P^(-1))e_1`.  In any finite presentation of the unquotiented
mapping torus, the entire central quotient by `C(S^2)` would therefore be
imposed by the single relation `c(e_1)=1`.  This closes the infinite-central-
relator subproblem, but `(CP4)--(CP5)` show that it does not address the
decisive defect-saturation problem.

DERIVATION
companion-parabolic-compression-defect-is-trivial-proof
