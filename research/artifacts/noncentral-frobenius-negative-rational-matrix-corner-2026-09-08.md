# Full matrix blocks in finite translation augmentation corners

2026-09-08. The full negative spectral corner of a translation
in a finite affine group is a rational matrix algebra. Its unit
is exactly `(1-J)/2`; no additional irreducible-type projection
is selected. More generally, the whole augmentation complement
of the translation subgroup over any finite field gives a full
complex matrix algebra. These blocks admit every desired local
matrix width. The constructions give explicit local matrix units
for the noncentral augmentation-corner approach to `B_loop`.
They do not supply the cross-context identities of that BCS.

The existing affine-Frobenius local-storage nodes use the full
nontrivial-character block of an odd prime translation group.
The construction here instead uses characteristic two and the
complete negative projection of one noncentral involution.

## 1. The finite group and rational Fourier basis

Fix `n>=1`, let `k=F_(2^n)`, put `Q=2^n`, and let

```text
F=k_add semidirect k^times.
```

Write `t_v` for translation by `v in k` and `m_s` for
multiplication by `s in k^times`. Thus

```text
t_v t_w=t_(v+w),
m_s m_r=m_(sr),
m_s t_v m_s^(-1)=t_(sv).
```

Let `Tr:k->F_2` be the field trace, and set

```text
J=t_1,
q=(1-J)/2,
chi_a(v)=(-1)^Tr(av),
p_a=(1/Q) sum_(v in k) chi_a(v) t_v        (a in k).
```

All coefficients are rational. The trace pairing is nondegenerate:
the trace polynomial is nonzero of degree `2^(n-1)<2^n`, so
`Tr` is a nonzero linear functional; multiplication by nonzero
`a` is bijective. Character orthogonality consequently gives

```text
p_a^*=p_a,
p_a p_b=delta_(a,b) p_a,
sum_(a in k) p_a=1,
t_v p_a=chi_a(v) p_a.                                (1)
```

For a direct orthogonality check, the sum of a nontrivial
character is zero: translating the summation variable by a point
where the character equals minus one negates that sum.

Conjugation by a multiplier acts by

```text
m_s p_b m_s^(-1)=p_(b/s).                            (2)
```

Let

```text
Omega={a in k:Tr(a)=1},
d=|Omega|=Q/2.
```

Every element of `Omega` is nonzero. Equation (1) gives

```text
q=sum_(a in Omega) p_a.                              (3)
```

## 2. Explicit matrix units and the whole corner

For `a,b in Omega`, define

```text
E_ab=p_a m_(b/a) p_b=p_a m_(b/a).                    (4)
```

The second equality follows from (2). The same relation shows

```text
E_ab E_cd=delta_(b,c) E_ad,
E_ab^*=E_ba,
sum_(a in Omega) E_aa=q.                             (5)
```

For example, when `b=c`, the multiplier in the product is
`(b/a)(d/b)=d/a`; when `b!=c`, the intervening Fourier
projections are orthogonal.

These units span the entire corner. Indeed,

```text
{p_a m_s : a in k, s in k^times}
```

is a rational basis of `Q[F]`: for each fixed multiplier coset,
the Fourier transform (1) is invertible on the translation basis.
Left multiplication by `q` retains precisely `a in Omega`.
Right multiplication by `q` further retains precisely `as in
Omega`, by (2). Every surviving basis element is exactly
`E_(a,as)` from (4). They remain linearly independent, since
they are distinct members of that rational basis. Therefore

```text
q Q[F] q ~= M_d(Q),
q C[F] q ~= M_d(C),                 d=2^(n-1),         (6)
```

as unital star algebras, with unit `q`. No smaller central
idempotent or extra finite-subgroup type has been imposed.

The canonical group trace satisfies

```text
tau_F(q)=1/2,
tau_F(E_ab)=delta_(a,b)/Q.
```

Thus the normalized corner trace `2 tau_F` is the normalized
matrix trace in (6).

For `n=2`, the affine group on `F_4` has order twelve and is
`A_4`; `J` is a double transposition. Formula (6) gives its
full negative corner as `M_2(Q)`. The formula includes `n=1`,
where the group is `C_2` and the corner is one-dimensional.

## 3. Noncentrality and the exact transporter restriction

For an affine element `g=t_v m_s`,

```text
g J g^(-1)=t_s.                                     (7)
```

For `n>=2`, there is `s!=1`, so `J` is noncentral in `F`.
Equation (7) also proves

```text
{g in F:g q g^(-1)=q}=C_F(J)=k_add.                  (8)
```

The equivalence between preserving `q` and centralizing `J`
uses the exact formula `J=1-2q`, not a representation choice.
For these corner-preserving group elements,

```text
q t_v q=sum_(a in Omega) chi_a(v) E_aa.               (9)
```

They supply diagonal character phases only. Thus an arbitrary
unitary matrix in (6) is not automatically the compression of a
literal group element which transports this same corner.

More precisely, for any unitary `g` in a finite-dimensional
C-star algebra, `qgq` is a unitary of the `q` corner if and only
if `gq=qg`. To prove the nontrivial direction, the two unitary
identities for `qgq` give
`qg^*(1-q)gq=0` and `qg(1-q)g^*q=0`; positivity gives both
off-corner blocks zero. Applied to the group elements here,
(8)--(9) classify every literal corner unitary.

## 4. Proper literal partial isometries

Noncentrality does allow proper literal partial isometries.
For `s in k^times`, put

```text
w_s=q m_s q,
q_s=(1-t_s)/2.
```

All the `q_s` lie in the commutative translation algebra.
Using (7),

```text
w_s w_s^*=q q_s,
w_s^* w_s=q q_(1/s).                                (10)
```

Both are projections, so `w_s` is a partial isometry in the
corner. If `s!=1`, the two linear functionals
`a -> Tr(a)` and `a -> Tr(as)` are independent over `F_2`.
Consequently exactly `Q/4` values of `a` have both values one.
For `n>=2` and `s!=1`, each projection in (10) therefore has
matrix rank `d/2`, strictly between zero and `d`.

This distinguishes the construction from a central-sign packet:
when `q` is central in the entire packet, every `qgq=qg`
is a corner unitary. Here a multiplier moving `J` gives an
exact nonzero transport between two proper subprojections. It
still does not implement an arbitrary matrix change of basis
on the whole corner.

## 5. Exact local storage and the remaining global gate

Any rational matrix projection, partial isometry, or finite PVM
in `M_d(Q)` has the explicit finite-support realization

```text
(A_ab) |-> sum_(a,b in Omega) A_ab E_ab
```

in `q Q[F] q`. Complex matrices likewise give elements of
`q C[F] q`. In particular, partitioning `Omega` into sets
`Omega_1,...,Omega_r` gives an exact local PVM

```text
P_i=sum_(a in Omega_i) p_a,
sum_i P_i=q,
rank(P_i)=|Omega_i|.
```

Any prescribed nonnegative integer ranks summing to `d` occur.
By taking `n` large, every finite context can be stored with
as many nonzero atoms as desired, labelled by allowed local
assignments. This is a local realization only: arbitrary rational
probability weights with denominators not dividing `d` are not
claimed to be exact normalized ranks in this one matrix block.

The corner unit already authenticates the ordinary involution:
in every representation, its image is nonzero exactly when the
image of `J` is not the identity. The established theorem
`agent-leavitt-not-torsion-corner-noce-forces-mf-radical` therefore
applies directly if a countable host containing this packet can
be supplied with a unital map

```text
A(B_loop) -> q C[G] q.
```

No separate selected-type authentication would be required.
However, this artifact has not constructed such a map. If all
generator images remained in the single finite corner (6), they
would give a forbidden finite-dimensional model of `B_loop`.
The shared cross-context images must leave that finite corner,
and their ordinary group-ring identities are still the missing
construction. Equations (8)--(10) describe precisely the literal
transports available from this local packet before that step.

## 6. The full translation augmentation over any finite field

For this section let `k=F_(p^r)` for any prime `p` and
integer `r>=1`, write `N=p^r`, and take

```text
F=k_add semidirect k^times,
E={t_v:v in k},
e_E=(1/N) sum_(v in k) t_v,
Q_E=1-e_E.
```

Here `Q_E` is the complete augmentation complement of `E`.
It is not the projection onto one arbitrarily selected type of
`E`. The subgroup `E` is normal inside this finite packet;
no normality of `E` in an eventual larger host is required
to define this projection.

Fix `zeta=exp(2 pi i/p)` and use the cyclotomic Fourier
projections

```text
f_a=(1/N) sum_(v in k) zeta^(-Tr_(k/Fp)(av)) t_v
                       (a in k).
```

Character orthogonality and multiplier conjugation give

```text
f_a^*=f_a,
f_a f_b=delta_(a,b)f_a,
sum_(a in k)f_a=1,
f_0=e_E,
m_s f_b m_s^(-1)=f_(b/s).
```

These are the same computations as (1)--(2); complex conjugation
in the star operation is accompanied by `t_v^*=t_(-v)`.
Define, for all nonzero `a,b`,

```text
M_ab=f_a m_(b/a) f_b.
```

They satisfy the matrix-unit identities, and their diagonal sum
is now exactly `Q_E`. The basis `f_a m_s` of the full group
algebra survives compression by `Q_E` on both sides precisely
when `a!=0` and `as!=0`. The second condition is automatic
for a nonzero multiplier. Therefore all survivors are indexed
by the pairs of nonzero field elements, without omissions or
extra summands. This proves the full unital star isomorphisms

```text
Q_E Q(zeta)[F] Q_E ~= M_(N-1)(Q(zeta)),
Q_E C[F] Q_E ~= M_(N-1)(C).                          (11)
```

The involution on the cyclotomic field in (11) is complex
conjugation. The displayed units have explicitly finite support
and coefficients in that field. The canonical traces are

```text
tau_F(Q_E)=1-1/N,
tau_F(M_ab)=delta_(a,b)/N,
tau_(Q_E)(M_ab)=delta_(a,b)/(N-1).                    (12)
```

The rational star isomorphism in (6) remains the stronger
coefficient statement for the characteristic-two involution
corner. No rational change to a standard orthonormal matrix
basis is claimed for arbitrary fields in (11).

## 7. Every prescribed local matrix width is available

Given any positive integer `D`, choose a prime `p` not
dividing `D` and put

```text
r=2 phi(D),
N=p^r,
c=(N-1)/D.
```

For `D=1`, use the convention `phi(1)=1`. Euler's theorem,
or the order of `p` in the finite group of units modulo `D`,
shows that `D` divides `N-1`; thus `c` is a positive integer.
The unital star embedding

```text
M_D(C) -> M_(N-1)(C),         A -> A tensor I_c       (13)
```

followed by (11) embeds `M_D(C)` with unit exactly `Q_E`.
For an explicit support formula, enumerate `k^times` by pairs
`(i,l)`, with `1<=i<=D` and `1<=l<=c`, and write the
corresponding field element as `a_(i,l)`. Then

```text
F_ij=sum_(l=1)^c M_(a_(i,l),a_(j,l))
```

satisfies

```text
F_ij F_kt=delta_(j,k) F_it,
F_ij^*=F_ji,
sum_(i=1)^D F_ii=Q_E.                               (14)
```

Thus every fixed finite matrix PVM has an exact algebraic
realization in a full finite-subgroup augmentation corner.
When its entries are algebraic, the resulting coefficients are
algebraic as well. The normalized canonical trace is preserved,
since (13) is a matrix amplification and (12) is the matrix trace.

This arbitrary-width construction uses the complete augmentation
projection of the larger finite subgroup `E`. It does not
assert arbitrary widths for the negative projection of a single
involution; that is a different choice of corner unit.

## 8. Authentication and the precise remaining construction

For every unitary representation `rho` of a group containing
`E`, the finite average `rho(e_E)` is the projection onto
the vectors fixed by `rho(E)`. Consequently

```text
rho(Q_E)=0  if and only if  rho(t_v)=I for every v in k.
```

The same assertion holds for representations into the unitary
group of a C-star algebra, by applying a faithful Hilbert-space
representation of that algebra. It uses neither centrality nor
normality of `E` in the ambient group. Thus `Q_E` is an
authenticated unit for the whole finite translation subgroup.

The subgroup condition and local matrix storage are now explicit.
What has not been supplied is a countable host `G` containing
the finite packet together with one shared finite-support image
for each generator of `A(B_loop)`, satisfying every context
relation and having common unit `Q_E`. A diagram remaining
inside the finite matrix block (11) would be a finite-dimensional
BCS model and is impossible for this source. The arbitrary local
width in (13) removes a local storage restriction; it does not
construct the missing algebraic overlap identities.

## 9. Equal full augmentation units fix the translation subgroup

There is a tradeoff in using the whole translation augmentation.
For finite subgroups `E,E'` of any ambient group, equality of
`1-e_E` and `1-e_(E')` in the ordinary group algebra forces
`E=E'`: the positive coefficient support of the two averages is
exactly the corresponding subgroup. Likewise a literal group
element `g` preserves `1-e_E` by conjugation if and only if
`gEg^-1=E`.

Consequently, if several affine context packets use the same full
augmentation projection as their literal unit, their translation
subgroups coincide. Every such packet normalizes that common
finite subgroup. Adjoining only literal corner-preserving group
transporters also preserves it. The resulting support group
therefore has this subgroup normal; this construction has not
yet used the freedom permitted by the nonnormal endgame.

For negative involution units, equality of `(1-J)/2` only fixes
the common involution `J`. The larger translation subgroups of
different packets need not coincide, and each packet's multiplier
can move `J` as in (7). Thus the two choices of detecting unit
have different transport geometry despite both giving full local
matrix blocks. Neither choice supplies the missing BCS overlap
identities. To exploit a nonnormal full-augmentation subgroup in
the finite-support host, the coefficients must involve group
elements outside its normalizer; merely enlarging the collection
of affine packets with that same literal unit does not do so.
