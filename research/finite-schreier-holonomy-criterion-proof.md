---
rg: 2
id: finite-schreier-holonomy-criterion-proof
kind: route
title: Gauge a finite connection along a tree and expose the bent self-loop
target: finite-schreier-holonomy-is-the-lamp-gauge-obstruction
requires:
  - moving-lamp-refinement-cocycle-has-diffuse-fibers
---

## Step 1: tree gauge leaves exactly the fundamental holonomies

Orient one representative of every undirected edge.  For a path, compose
edge transports from right to left, using `c_e^*` or `p_e^*` when the
path traverses an edge backwards.  Thus `C_v,P_v:C^k_o->C^k_v`.

First suppose vertex gauges satisfy

```text
p_e=z_w c_e z_v^*,       e:v->w.                       (FSP1)
```

Multiplying `(FSP1)` along the tree path from `o` to `v` gives

```text
P_v=z_v C_v z_o^*.                                      (FSP2)
```

For a chord `e:v->w`, substitute `(FSP2)` into its target holonomy:

```text
P_w^* p_e P_v
 =z_o C_w^* c_e C_v z_o^*.                             (FSP3)
```

Thus `W=z_o` satisfies `(FSH3)`.

Conversely, fix any `W in U(k)` and define

```text
z_v=P_v W C_v^*.                                       (FSP4)
```

If `e:v->w` is a tree edge oriented along the root path, then
`C_w=c_e C_v` and `P_w=p_e P_v`.  Direct substitution gives

```text
z_w c_e z_v^*=p_e.                                     (FSP5)
```

The backwards orientation follows by taking adjoints.  For an arbitrary
chord,

```text
p_e=P_w Hol_p(e) P_v^*,
z_w c_e z_v^*=P_w W Hol_c(e) W^* P_v^*.                (FSP6)
```

Unitary invariance of normalized Hilbert--Schmidt norm proves `(FSH4)`.
It proves both directions of the criterion and, term by term, the assertions
for maxima and sums.  A disconnected graph is handled independently on each
component.

This argument has no stability loss: all tree edges are made exact, and each
remaining edge error is one fundamental-cycle error rather than a sum over
the length of that cycle.

## Step 2: identify the lamp connection

Fourier transform the regular representation:

```text
ell^2(B) tensor C^k
 =direct_sum_(chi in dual(B)) C^k_chi,
rho(b)|_(C^k_chi)=chi(b)1_k.                            (FSP7)
```

If `U_s` implements the automorphism `alpha_s` of `B`, it maps the
`chi` fiber unitarily onto the `s chi` fiber.  After fixing the displayed
identifications, let `c_(s,chi)` be that block.  Include the inverse
generator with the adjoint block.  These blocks are a unitary connection on
the finite Schreier graph.  A second normalizer family `V_s` similarly
gives `p_(s,chi)`.

Every lamp-commutant unitary and only such a unitary is block diagonal:

```text
Z=direct_sum_chi z_chi.                                 (FSP8)
```

The block of `Z U_s Z^*` from `chi` to `s chi` is

```text
z_(s chi)c_(s,chi)z_chi^*.                              (FSP9)
```

Therefore the simultaneous equations `V_s=Z U_s Z^*` are precisely
`(FSP1)`, and Step 1 applies orbit by orbit.

When the actor multiplication laws are exact, a closed labelled path at
`chi` is an actor word in the stabilizer of `chi), and its connection
product is the corresponding stabilizer action on the multiplicity fiber.
Actor relators identify some graph loops, but they do not force all
stabilizer returns to be trivial.  A spanning tree plus the finitely many
chords records exactly the finite edge system which a simultaneous gauge
must match.

## Step 3: a flat-Walsh normalizer with canonical trace

Identify `B_m` and its dual with `F_2^(2m)).  Put

```text
q_m(x)=sum_(j=1)^m x_(2j-1)x_(2j),
f_m(x)=(-1)^(q_m(x)).
```

For `a=(alpha_1,beta_1,...,alpha_m,beta_m)`, its normalized Walsh
coefficient factors as

```text
2^(-2m) sum_x (-1)^(q_m(x)+a dot x)
 =product_(j=1)^m
   [4^(-1) sum_(u,v in F_2)(-1)^(uv+alpha_j u+beta_j v)].
                                                               (FSP10)
```

For one pair, summing first over `v` leaves the unique value
`u=beta_j`, and the unnormalized sum is
`2(-1)^(alpha_j beta_j)`.  Every factor in `(FSP10)` therefore has
absolute value `1/2`.  This proves `(FSH5)`.

Let `F_m` denote the unitary Fourier transform and, in the original group
basis, set

```text
U_m=F_m^* diag(f_m) F_m.                                (FSP11)
```

It is a selfadjoint involution.  Since the left regular lamp operators are
diagonal after `F_m`, `U_m` commutes with all of them.  Thus `(FSH6)`
is an exact representation of `A times C_2` after the lamp element is
projected to its first `2m` coordinates.

Write `tau_m` for normalized trace.  If a fixed `a in A` is nonzero,
then for all large `m`

```text
tau_m(lambda(a))=0.                                     (FSP12)
```

For every `a`, including zero, `(FSH5)` gives

```text
|tau_m(lambda(a)U_m)|=2^(-m).                           (FSP13)
```

Equations `(FSP12)--(FSP13)` prove convergence to the canonical group trace
on every nonidentity element of `A times C_2`.

## Step 4: neither a commutant gauge nor padding spatializes the model

On one regular `B_m`-orbit, a point permutation commuting with every left
translation must be a right translation.  Indeed, if its underlying
bijection is `sigma`, then

```text
sigma(b+x)=b+sigma(x)
```

for all `b,x`, so `sigma(x)=x+sigma(0)`.  In Fourier coordinates, right
translation by `b` has the linear phase
`x |-> (-1)^(b dot x)`.

The regular commutant is diagonal in the same Fourier coordinates.
Consequently every commutant gauge commutes with
`diag(f_m)` and leaves `U_m` fixed.  The phase `f_m` is not linear:
for example the polarization of its exponent on the first coordinate pair
is nonzero.  Hence no commutant gauge can turn `U_m` into a permutation
which induces the trivial automorphism on `B_m`.

The `b,c` matrix entry of `U_m` in the group basis is

```text
d_m^(-1) sum_x f_m(x)(-1)^(x dot (b-c)).                (FSP14)
```

By `(FSH5)`, every such entry has modulus `d_m^(-1/2)`.  A monomial
matrix selects one entry from each row and column.  Therefore

```text
|tau_m(M^*U_m)|<=d_m^(-1/2),
||U_m-M||_2^2
 =2-2 Re tau_m(M^*U_m)
 >=2-2/sqrt(d_m),                                       (FSP15)
```

which proves `(FSH7)`.

Finally let `R_m` be any unitary of size `r_m` and compare
`U_m direct_sum R_m` with a monomial of size `d_m+r_m`.  Rows from the
first block contribute at most `d_m/sqrt(d_m)=sqrt(d_m)` to the
unnormalized overlap, and rows from the padding contribute at most `r_m`.
Thus

```text
|tau(M^*(U_m direct_sum R_m))|
 <=(sqrt(d_m)+r_m)/(d_m+r_m).                           (FSP16)
```

This proves `(FSH8)`.  Because `U_m` commutes with every lamp subgroup,
all spectral refinement and overlap identities are exact.  Nevertheless a
different actor choice, namely the identity permutation, is available.
Accordingly this is a sharp obstruction to rounding or gauge-spatializing
the supplied normalizer family, not an obstruction to the existence of a
sofic model.
