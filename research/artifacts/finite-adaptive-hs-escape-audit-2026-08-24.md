# Finite adaptive payload-conditioned Hilbert--Schmidt escape audit

Date: 2026-08-24

> **Cairn follow-up.** The finite packing-extension lemma sought in the
> submitted audit is not merely open under its subgroup-embedding hypotheses:
> `canonical-trace-forbids-supercritical-character-packing` refutes it at the
> exact threshold. The canonical group trace gives `K<=2M/beta` for separate
> packing and `K<=2/beta` for simultaneous packing. The strongest local
> payload-conditioned replacement tried after that audit is a central twist
> of the Schur packet flip square. The calculation in
> `twisted-flip-square-shifts-multiplicity-cocycle` shows that this only
> transfers a fixed root-of-unity divisibility condition between allowed and
> forbidden multiplicity spaces, with normalized-HS defect `O(1/m)` under
> amplification. It therefore does not complete the nonhyperlinearity proof;
> a supercritical same-model amplifier or a positive-density capacity coupling
> is still required.

## Outcome

This audit does not construct the missing ordinary-group escape gadget. It
closes the seed correction and trace-growth bookkeeping, and replaces the
adaptive tree by a sharper sufficient target:

```text
finite bad-character packing overgroup
  + exact extension of the prescribed context trace
  => static root contradiction.
```

For a robust shared-variable Boolean contextual system with `M` forbidden
types and matrix soundness constant `beta`, it is enough to give every bad
seed-context character more than `2M/beta` pairwise orthogonal conjugates in
one finite overgroup while preserving the exact tracial restriction. The
simultaneous packing/extension requirement, not the projection arithmetic,
is the remaining open finite-group problem.

Throughout,

```text
||T||_(2,d)^2=(1/d)Tr(T^*T),       tr_d=(1/d)Tr.
```

## 1. Finite Pauli seed and exact tracial model

Adjoin involutions `B,C` to the structural BCS presentation and impose

```text
B^2=C^2=J^2=1,       [B,C]=J,
[J,B]=[J,C]=1,
[B,x_v]=[C,x_v]=1  for every shared variable v.       (A1)
```

The subgroup on `J,B,C` is `D_8`. If `theta` is the perfect contextual
tracial model with `theta(J)=-1`, then

```text
x_v |-> theta(x_v) tensor 1,
J   |-> -1 tensor 1,
B   |-> 1 tensor Z,
C   |-> 1 tensor X                                  (A2)
```

in `M_B bar-tensor M_2(C)` is an exact extension. Every forbidden projection
remains zero.

## 2. Correct the seed before taking the commutant

Small commutators with an arbitrary contextual tuple do not imply
dimension-independent proximity to its joint commutant. The valid order is:

1. exactify the fixed finite `D_8` seed in normalized Hilbert--Schmidt norm;
2. average the contextual matrices over that exact finite action;
3. round the averaged matrices inside the seed commutant.

For an approximate involution `U`, spectral sign rounding gives

```text
||U-sgn(Re U)||_(2,d) <= 2^(-1/2)||U^2-1||_(2,d).     (A3)
```

On the `J=-1` sector, after making `B` an involution, write its eigenspace
dimensions as `r_+,r_-`. For a unitary `C`, block decomposition relative to
`B` gives

```text
|r_+-r_-|/d <= (1/4)||BC+CB||_(2,d)^2.                (A4)
```

The unmatched normalized dimension is therefore `O(E)` and can be reassigned
at `O(sqrt(E))` normalized-HS cost. On the matched part, replace `C` by the
exact off-diagonal involution. This yields an exact `D_8` representation
`rho_D` within `O(sqrt(E))` of the raw seed.

Now use the eight-term conditional expectation

```text
E_D(T)=(1/8) sum_(g in D_8) rho_D(g)T rho_D(g)^*.      (A5)
```

The seed/context commutator defects imply

```text
||x_v-E_D(x_v)||_(2,d) <= K_D sqrt(E).                (A6)
```

Functional calculus makes the averaged variables involutions without leaving
the commutant. The assumed dimension-independent contextual rounding theorem
then applies blockwise in the finite direct sum of matrix algebras
`rho_D(D_8)'`. Its constants survive the normalized-trace weighting.

The resulting exact structural tuple commutes with the exact seed. Hence

```text
Q_-=(1-J)/2,       Q_empty=Q_-(1+B)/2                 (A7)
```

are genuine projections and `Q_empty` reduces the entire rounded contextual
tuple. On `Q_-`, `CBC=-B`, so `C` exchanges the two `B` eigenspaces exactly:

```text
tr_d(Q_empty)=(1/2)tr_d(Q_-).                         (A8)
```

For canonical microstates, the exact model shows `J` is a nonidentity group
element, canonical trace separation gives `tr_d(J)->0`, and therefore

```text
tr_d(Q_-)->1/2,       tr_d(Q_empty)->1/4.              (A9)
```

## 3. Conditional adaptive cascade

Let `Q_sigma<=Q_-` reduce the rounded contextual tuple. Choose a maximal
forbidden type and put

```text
A_sigma=Q_sigma P_i,
D_sigma=U_(sigma,i) A_sigma U_(sigma,i)^*.
```

Robust soundness gives

```text
tr_d(A_sigma)
 >=(beta/M)tr_d(Q_sigma)-(C_B/M)sqrt(E).               (A10)
```

If the missing escape row supplies

```text
tr_d(Q_sigma D_sigma Q_sigma)
 <=(1-eta)tr_d(A_sigma)+C_E sqrt(E),                   (A11)
```

then the reducing hull `Q_(sigma i)` of `Q_sigma join D_sigma` obeys

```text
tr_d(Q_(sigma i))
 >=(1+eta beta/M)tr_d(Q_sigma)
   -(C_E+eta C_B/M)sqrt(E).                            (A12)
```

The only projection facts used are

```text
tr(Q join D)=tr(Q)+tr(D)-tr(Q meet D),
tr(Q meet D)<=tr(QD)=tr(QDQ).                          (A13)
```

Writing `lambda=1+eta beta/M` and `K_0=C_E+eta C_B/M`, after `n` reached
steps,

```text
q_n >= lambda^n q_0
      -K_0 (lambda^n-1)/(lambda-1) sqrt(E).            (A14)
```

The effective fixed depth

```text
N=floor(log(2)/log(1+eta beta/M))+1                    (A15)
```

has `lambda^N>2`. Combining `(A9)` and `(A14)` contradicts `Q_N<=Q_-`.
This verifies the existing adaptive compiler once `(A11)` is provided; it
does not provide `(A11)`.

## 4. Uniform-hole and isotropic-mixing barriers

For `A<=Q<=H`, `D<=H`, and `tr(D)=tr(A)=a`,

```text
tr(QD)=a-tr((H-Q)D) >= a-tr(H-Q).                      (A16)
```

Thus a fixed escape fraction forces a fixed hole:

```text
tr(H-Q) >= eta a-epsilon.                              (A17)
```

Using `(A10)`, every reached carrier would have to satisfy

```text
tr(Q_--Q_sigma)
 >=(eta beta/M)tr(Q_sigma)-O(sqrt(E)).                 (A18)
```

An actuator family that only depolarizes inside `H` cannot do this. If
`h=tr(H), q=tr(Q)` and `a=tr(A)`, exact isotropic averaging has expected
overlap `(q/h)a`. The best generic escape fraction is `1-q/h`. With
`a>=gamma q`, the normalized recurrence is only

```text
x_(n+1)>=x_n+gamma x_n(1-x_n),       x_n=q_n/h,        (A19)
```

which approaches capacity one without forcing an overshoot. Random mixing,
unitary designs, and expanders that use only the three scalar dimensions do
not furnish the required fixed `eta`; successful escape must consume the
forbidden-atom semantics.

## 5. Static character-idempotent packing

For a forbidden type `i=(c,a)`, let

```text
H_i=<J,B,x_v : v in X_c>
```

after structural rounding. It is a finite abelian 2-group. Define

```text
chi_i(J)=-1,       chi_i(B)=1,       chi_i(x_v)=a(v).
```

The corresponding character idempotent is exactly

```text
e_i=Q_-(1+B)/2 P_i=Q_empty P_i.                       (A20)
```

It vanishes in the perfect tracial model. Suppose a finite overgroup
`G_i>=H_i`, with `J` still central, contains elements `g_1,...,g_K` such that

```text
(g_r e_i g_r^(-1))(g_s e_i g_s^(-1))=0  for r!=s.     (A21)
```

In every exact finite-dimensional representation these are equal-trace
orthogonal projections below `Q_-`, so

```text
K tr_d(e_i)<=tr_d(Q_-).                               (A22)
```

For approximate representations, fixed-word telescoping and finite-family
projection orthogonalization add only `O(sqrt(E))`, independent of matrix
dimension.

At the root, soundness and maximality give

```text
tr_d(e_i)
 >=(beta/M)tr_d(Q_empty)-(C_B/M)sqrt(E).               (A23)
```

Using `(A9)`, `(A22)` and `(A23)` contradict canonical microstates whenever

```text
K>2M/beta,
```

so one may take

```text
K=floor(2M/beta)+1.                                   (A24)
```

This static certificate needs no reducing hull and no adaptive iteration.
If the conjugates are also orthogonal across different forbidden types, one
can sum the full soundness inequality before pigeonholing; the sharper
simultaneous threshold is then `K>2/beta`, with no factor `M`.

## 6. Mackey orthogonality and exact extension

For finite subgroups `H,K<=G`, one-dimensional characters `chi,psi`, and
their idempotents, the Mackey intertwining criterion gives

```text
e_chi g e_psi=0                                       (A25)
```

when `chi` and the transported `psi` disagree on
`H intersect gKg^(-1)`. Thus conjugate context subgroups with controlled
intersections can create `(A21)`.

Let `mu_i(psi)=tau(e_psi)` be the exact contextual distribution on
`widehat(H_i)`. For a finite overgroup `G_i`, exact tracial extendability is
the finite convex condition

```text
mu_i in conv{r_lambda : lambda in widehat(G_i)},       (A26)
```

where `r_lambda` is the normalized `H_i`-weight multiplicity distribution of
`lambda|_(H_i)`. Compatible extensions for the finitely many contexts can be
combined over their finite-dimensional traced context images.

That amalgamation proves consistency of the selected tracial model only.
Finite/amenable-edge amalgamation preserves hyperlinearity of a hyperlinear
base, so independent finite-overgroup attachments cannot by themselves be a
new source of canonical-trace failure. If the packing certificate succeeds
in such an amalgam, it simultaneously certifies that the contextual base was
already nonhyperlinear. A genuinely new construction must make the packing
identities coexist with contextual soundness in the combined presentation,
not infer canonical obstruction merely from extension of `mu_i`.

The exact missing lemma is therefore:

> For every bad character `chi_i`, find a finite `G_i>=H_i` with central
> `J`, at least `floor(2M/beta)+1` pairwise orthogonal conjugates of
> `e_(chi_i)`, and a tracial state whose restriction distribution is `mu_i`.

## 7. Finite mechanisms that do not solve the lemma

If `G_i=H_i semidirect L` with `H_i` abelian normal, distinct characters in
`L chi_i` give orthogonal idempotents. But every tracial restriction is
`L`-invariant. Since `mu_i(chi_i)=0`, exact extension forces the entire orbit
`L chi_i` to have zero `mu_i`-mass. Large orbit size alone is not enough.

Seed-only conjugation moves a half-dimensional projection inside the
two-dimensional marked Pauli type, so it yields at most two orthogonal copies.
Adding `m` independent selector bits splits the guaranteed atom mass by
`2^m` while providing at most `2^m` new selector characters; the packing
ratio does not improve. Unconditioned random mixing is ruled out by
`(A16)--(A19)`.

The remaining plausible lane is Mackey-designed finite graphs of groups or a
finite disjunctive representation gadget: allowed context characters must
extend, while the bad character has many pairwise nonintertwining transported
copies. No such general construction is supplied here.

## 8. Quantifier and normalization audit

The presentation and every actuator/conjugator word are fixed before a
matrix model is received. One fixed dimension-independent correction is
performed. Adaptive choices may select only among finitely many words already
encoded in the presentation, and escape is required only on the reached
branch.

Relator energy is a sum of squared normalized-HS defects. Each fixed relator
has defect at most `sqrt(E)`; finitely many Lipschitz corrections and fixed
word telescoping therefore cost `O(sqrt(E))`. Changing a projection on
normalized dimension `alpha` costs order `sqrt(alpha)` in normalized-HS norm,
so no raw-rank substitution is permitted. Conjugation preserves projection
trace exactly after correction. A reducing hull may be much larger than its
generating projection, which is precisely why the static packing route is
strictly cleaner than trying to estimate adaptive hulls from orthogonality
alone.

## Technique references supplied with the audit

- Hadwin--Shulman, *Stability of group relations under small
  Hilbert--Schmidt perturbations*, JFA 275 (2018), arXiv:1706.08405.
- Becker--Lubotzky, *Group stability and Property (T)*, JFA 278 (2020),
  108298.
- Gowers--Hatami, *Inverse and stability theorems for approximate
  representations of finite groups*, arXiv:1510.04085.
- De Chiffre--Glebsky--Lubotzky--Thom, *Stability, cohomology vanishing, and
  non-approximable groups*, Forum Math. Sigma 8 (2020).

These sources support the stability distinctions and finite-group
exactification techniques; none supplies the missing packing--extension
lemma.
