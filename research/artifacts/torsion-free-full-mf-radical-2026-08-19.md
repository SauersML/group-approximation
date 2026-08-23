# Torsion-free full MF radical via Fournier--Facio and Hull--Osin

Date: 2026-08-19.

## Statement

There is a two-generated finitely presented torsion-free property-(T)
acylindrically hyperbolic group `Q` such that

```text
Res_MF(Q) = Q.
```

Equivalently, every homomorphism from `Q` to the unitary group of every norm
matrix corona is trivial.  Every nontrivial quotient `L` of `Q` again has
`Res_MF(L)=L`, hence is non-MF.

The operator-algebraic part is kernel-checked in
`GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean`.  The external boundary
is the acylindrical-small-cancellation existence step.

## 1. Fournier--Facio compression source

`fournier-facio-torsion-free-skeleton` records a finitely presented torsion-free
property-(T) group carrying the one-sided compression configuration and an
embedded finitely presented nonabelian simple torsion-free subgroup `S`.
The compression defect contains `S`.  The algebraic saturation is formalized as

```text
FournierFacioDefectData.simpleSubgroup_le_defectNormal.
```

It takes the preimage of the defect in the simple subgroup.  That preimage is
normal and contains a nontrivial commutator, so simplicity forces it to be the
whole simple subgroup.

## 2. Route the defect onto the quotient

Let `N=<<S>>`.  The established claim
`defect-normally-generates-torsion-free-quotient` and the source audit in
`notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md` verify the following
Hull--Osin route.

* `N` is an infinite normal subgroup of the torsion-free acylindrically
  hyperbolic source and supplies a suitable subgroup for Hull's machinery.
* Apply Hull's Theorem 7.1 to a suitable two-generator subgroup inside `N`,
  using a finite generating set of the source as the prescribed elements and
  protecting a fixed nontrivial element of `S`.
* The resulting quotient `q:G->>Q` is torsion-free and acylindrically
  hyperbolic, preserves the protected element, is two-generated and finitely
  presented, and satisfies

  ```text
  Q = q(N) = <<q(S)>>^Q.
  ```

* Property (T) passes to `Q` through the second common-quotient map from the
  torsion-free hyperbolic property-`(T)` factor `H`; it is not attributed to
  the HNN source `E`.

The repository's 2026-08-15 adversarial audit records this routing statement as
`CONFIRMED`; the small-cancellation theorem itself is intentionally kept outside
the Lean trust boundary.

## 3. Full residual

The image of the compression defect is normal and contains `q(S)`.  Since
`q(S)` normally generates `Q`,

```text
q(defectNormal) = Q.
```

This is the conclusion represented in the Lean routing interfaces by
`mapped_defectNormal_eq_top`.

Apply the normal-Kazhdan compression obstruction to the mapped core with
`K=Q`.  The subgroup is normal, has property (T), and lies in the mapped defect
because that defect is all of `Q`.  Therefore every norm-corona homomorphism
kills every element of `Q`:

```text
Res_MF(Q) = Q.
```

The protected element makes `Q` nontrivial, so `Q` is not MF.

## 4. Quotient heredity

If `p:Q->>L` is any quotient, functoriality plus surjectivity gives

```text
Res_MF(Q)=Q  ==>  Res_MF(L)=L.
```

This is kernel-checked as `coronaMFResidual_eq_top_of_surjective`.  Hence every
nontrivial quotient of `Q` is again non-MF and every homomorphism from such a
quotient to an MF group is trivial.

## Trust boundary

* **Kernel-checked:** simple-factor defect saturation; mapped-defect algebra;
  normal-Kazhdan MF obstruction; full-residual functoriality; quotient
  consequences.
* **Source-audited, not formalized:** Hull/Osin production of the concrete
  quotient with torsion-freeness, finite presentation, two generation,
  acylindrical hyperbolicity, survival and normal generation.

Cairn closes the existence claim at this paper-level boundary; it does not
pretend Mathlib contains acylindrically hyperbolic small cancellation.

## 5. Reader-facing proof of the normal-Kazhdan obstruction

This section records the analytic argument independently of the Lean
implementation.  It is the part of the construction which replaces the
central involution in the older proof.

Let `C` be a Kazhdan compression core in a countable group `E`: write
`L=iota(Gamma)`, let `tLt^(-1)<=L`, and let `c` centralize `L`.  Its defect is

```text
D=normalClosure_E({[tct^(-1),iota(gamma)]:gamma in Gamma}).
```

Suppose `U_n:E->U(d_n)` is an operator-norm asymptotic representation.  On
the Hilbert spaces `K_n=L^2(M_(d_n),tr_(d_n))`, the operators
`Ad(U_n(g))` give an exact representation in a norm ultraproduct.  Property
`(T)` isolates the `L`-fixed space by a spectral projection `P` belonging to
that norm ultraproduct.  If `V=Ad(U(t))`, then

```text
ran(P)=Fix(L) <= Fix(tLt^(-1))=ran(VPV^*).
```

The norm ultraproduct of the finite-dimensional `B(K_n)` is Dedekind finite:
if
`v^*v=1`, polar correction of coordinate lifts makes `v` a class of
unitaries, hence `vv^*=1`.  Therefore equivalent comparable projections are
equal, and

```text
P=VPV^*.
```

Consequently conjugation by `U_n(t)` transports every Hilbert--Schmidt
asymptotic `L`-centralizer back into the `L`-centralizers.  Applying this to
`U_n(c)` shows

```text
||U_n([tct^(-1),iota(gamma)])-1||_2 -> 0
```

for every `gamma`.  The set of group elements with this property is a normal
subgroup (operator-norm multiplicativity controls products, inverses and
conjugates), so every element of `D` is Hilbert--Schmidt invisible.

Now let `K triangleleft E` be nontrivial, Kazhdan, and contained in `D`.
Assume a norm-corona homomorphism `Theta:E->U(Q_d)` has nontrivial image of
`K`.  Work in the countable image group and choose coordinate unitary lifts.
In a norm ultraproduct, let `P_K` be the projection onto the fixed vectors of
the image of `K` and put `q=1-P_K`.  Nontriviality of that image gives
`q!=0`.  Normality of `K` makes `q` commute with the entire image group.

Lift `q` to nonzero coordinate projections `q_n`, pass to a diagonal
subsequence, compress every lift to `q_n C^(d_n)`, and polar-correct.  This
produces an operator-norm asymptotic representation `W_n` on dimensions
`r_n=rank(q_n)`.  The trace is now normalized on the corner itself; no lower
bound on `r_n/d_n` is needed.  There are no `K`-fixed vectors on the corner,
so a Kazhdan set `S` with constant `kappa` gives one fixed `s_0 in S` and

```text
liminf_n ||W_n(s_0)-1||_(2,r_n)^2 >= kappa^2/|S| > 0.
```

Choose `k_0 in K` mapping to `s_0`.  Since `K<=D`, the defect-invisibility
statement applied to the composite asymptotic representation of `E` says

```text
||W_n(s_0)-1||_(2,r_n) -> 0,
```

a contradiction.  Thus every norm-corona homomorphism kills `K`.  This proof
uses neither torsion nor a central mark: the self-normalized corner is the
non-fixed Kazhdan corner of a normal subgroup.

## 6. Why saturation gives the full residual

In the Fournier--Facio source, choose `1!=c in J` and put
`d=t_1ct_1^(-1) in S<=Gamma`.  The defect generated by `[d,gamma]` is exactly
`<<S>>`: containment in `<<S>>` is immediate, while `d` is noncentral in the
nonabelian simple group `S`, so one nontrivial commutator lies in `D cap S`;
simplicity gives `S<=D`.

The audited Hull--Osin quotient protects a nontrivial element of `S` and
forces `q(<<S>>)=Q`.  Hence the mapped defect is all of `Q`.  Property `(T)`
passes to the quotient, so the preceding theorem applies with `K=Q` and gives

```text
Res_MF(Q)=Q.
```

If `Q->>L` is surjective, every corona homomorphism out of `L` pulls back to
one out of `Q`; therefore every nontrivial quotient also has full MF
residual.  Likewise any homomorphism from `Q` to an MF group is trivial after
composing with an MF embedding of the target.
