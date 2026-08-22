---
rg: 2
id: atlas-a8-index-91-to-496-l5-classification-proof
kind: route
title: Remove U4(3) and classify the two L5(2) parabolic complement classes
target: atlas-a8-index-91-to-496-reaches-standard-l5
requires: []
artifacts:
  - experiments/atlas_a8_agl4_complement_classes.py
---

Filter the complete finite-simple order table by `20160 | |S|`.  From index
90 through 506 the successive entries are

```text
A10          90
U4(3)       162
L5(2)       496
M23         506.                                    (SIL3)
```

The maximal-subgroup table of `U4(3)` excludes the first interior candidate.
The only maximal subgroup order divisible by `20160` is `|L3(4)|=20160`.
If an `A8` lay there, equality of orders would identify it with `L3(4)`, but
these two simple groups are nonisomorphic.  Thus `U4(3)` contains no `A8`;
there is no ambient group in `(SIL1)`, and equality 496 forces `(SIL2)`.

The maximal subgroups of `L5(2)` are two classes each of

```text
2^4:L4(2),       2^6:(S3 x L3(2)),
```

and one `31:5`.  Only the first type has order divisible by `20160`.  Hence
any `H ~= A8` lies in a maximal parabolic `P=V:L4(2)`, with `|V|=16`.
Simplicity gives `H intersect V=1`; order equality in the quotient shows that
`H` is a complement to `V`.

The exact GAP complement calculation in the attached certificate proves

```text
number of P-conjugacy classes of complements to V = 1,                (SIL4)
affine orbit profile of the complement             = 1+15.            (SIL5)
```

The two dual parabolic classes share a standard Levi after choosing a direct
sum of a line and complementary hyperplane.  By `(SIL4)`, every `A8` in
either parabolic is conjugate in `L5(2)` to that block-diagonal Levi.

Let `H` denote the standard Levi.  Its centralizer in `L5(2)` is trivial: on
the restricted five-dimensional module `V_4 directSum 1`, Schur's lemma over
`F2`, together with the absence of fixed vectors and covectors in `V_4`,
leaves only the identity.  A normalizer element inducing the outer graph
automorphism would identify `V_4` with `V_4^*`.  That is impossible, since it
would give a nonzero bilinear form invariant under the full `GL_4(2)`; the
elementary transvections force every coefficient of such a form to vanish.
Thus `N_(L5(2))(H)=H`.

The ambient inverse-transpose graph automorphism exchanges the natural and
dual labelings while preserving the subgroup class.  Hence, after fixing one
marked chart, ordered pairs split into same and opposite relative graph
parity.  The existing inner-conjugator screen covers exactly the former.  Its
failure to cover the latter is a genuine labeling issue, not an omitted
subgroup conjugacy class.  This completes the claim.
