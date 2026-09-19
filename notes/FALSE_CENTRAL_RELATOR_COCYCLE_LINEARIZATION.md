# Central-relator certificates are finite cocycle linear algebra

Date: 2026-08-11

## 1. Outcome

The finite groups in
`FALSE_CENTRAL_RELATOR_SEPARATION_CRITERION.md` do not have to be synthesized
by multiplication-table search.  After quotienting by the distinguished
cyclic center, every candidate is exactly a normalized `2`-cocycle on a
finite quotient, together with one lift phase for each presentation
generator.

For a presentation with `d` generators and `ell` relators, a fixed finite
quotient `Q` and modulus `m` determine a linear evaluation map

`Ev_(Q,m):Z^2(Q,Z/m) directSum (Z/m)^d`
`          ->(Z/m)^(ell+1)`.                         `(CRC1)`

The first `ell` coordinates are the defining-relator exponents and the last
coordinate is the marked radical-word exponent.  The central-relator
certificate exists over `(Q,m)` exactly when the image of `(CRC1)` contains
a vector whose first coordinates have small circular lifts and whose last
coordinate is macroscopically separated from zero.

Thus one finite stage consists of:

1. modular cocycle linear algebra;
2. projection to an `(ell+1)`-dimensional module; and
3. one fixed-dimensional modular closest-vector or MILP calculation.

No unitary matrices and no enumeration of extension multiplication tables
are required.

## 2. Word holonomy of a normalized cocycle

Let

`P=<s_1,...,s_d | r_1,...,r_ell>`                    `(CRC2)`

and let `w` be the fixed nontrivial word in `Rad_sof(P)`.  Fix a finite
group `Q` and labels

`sigma_i in Q`                                        `(CRC3)`

such that

`r_j(sigma_1,...,sigma_d)=1`,
`w(sigma_1,...,sigma_d)=1`.                           `(CRC4)`

Equivalently, `(CRC3)` defines a finite quotient of `P`; the second
identity is automatic because `w` belongs to the sofic radical.

Let `A=Z/m` and let

`omega:Q times Q->A`                                  `(CRC5)`

be a normalized `2`-cocycle:

`omega(1,x)=omega(x,1)=0`,                            `(CRC6)`

`omega(x,y)+omega(xy,z)`
` =omega(y,z)+omega(x,yz)`.                           `(CRC7)`

It defines the finite central extension

`E_omega=A times Q`,                                  `(CRC8)`

`(a,x)(b,y)=(a+b+omega(x,y),xy)`.                     `(CRC9)`

Write `z=(1,1)`.  Then `<z>` is central of order `m`.  Choose generator
lift phases `t_i in A` and put

`u_i=(t_i,sigma_i)`.                                  `(CRC10)`

For a letter `a=s_i^epsilon`, define its quotient value `q(a)` and central
lift exponent `tau(a)` by

`q(s_i)=sigma_i`, `tau(s_i)=t_i`,                     `(CRC11)`

`q(s_i^(-1))=sigma_i^(-1)`,
`tau(s_i^(-1))=-t_i-omega(sigma_i^(-1),sigma_i)`.     `(CRC12)`

For a word `v=a_1...a_L`, start with `x_0=1` and recursively set

`x_k=x_(k-1)q(a_k)`.                                  `(CRC13)`

If `x_L=1`, evaluation of the lifted word is central:

`v(u_1,...,u_d)=z^(Hol_(omega,t)(v))`,                `(CRC14)`

where

`Hol_(omega,t)(v)`
` =sum_(k=1)^L`
`   (tau(a_k)+omega(x_(k-1),q(a_k))) mod m`.          `(CRC15)`

The right side is linear in the cocycle coordinates and in `t_1,...,t_d`.
The inverse formula `(CRC12)` is linear as well.  Therefore

`Ev_(Q,m)(omega,t)`
` =(Hol(r_1),...,Hol(r_ell),Hol(w))`                  `(CRC16)`

is the homomorphism `(CRC1)`.

## 3. Equivalence with finite central extensions

**Theorem 1 (cocycle linearization).**  Fix `(Q,m,sigma)` satisfying
`(CRC3)--(CRC4)`.  The following data are equivalent:

1. a finite group `E`, a central cyclic subgroup `<z>` of order `m`, an
   identification `E/<z>~=Q`, and generator lifts `u_i` of `sigma_i`; and
2. a normalized cocycle `omega in Z^2(Q,Z/m)` and lift phases
   `t in (Z/m)^d`.

Under this equivalence, the central exponents of every relator and of `w`
are exactly `(CRC16)`.

**Proof.**  Data in item 2 give `(CRC8)--(CRC10)`, and `(CRC15)` computes
all word values.

Conversely, choose a normalized section `s:Q->E`.  There is a unique
function `omega` with

`s(x)s(y)=z^(omega(x,y))s(xy)`.                       `(CRC17)`

Associativity gives `(CRC7)` and normalization gives `(CRC6)`.  Each
chosen lift has a unique expression

`u_i=z^(t_i)s(sigma_i)`.                              `(CRC18)`

The map `(a,x)|->z^a s(x)` identifies `(CRC8)--(CRC9)` with `E`, and word
evaluation gives `(CRC15)`.  End proof.

Changing the section changes `omega` by a coboundary and changes the lift
coordinates compatibly.  The vector `(CRC16)` is unchanged.  A computation
may therefore use raw normalized cocycles, a basis of `H^2`, or any smaller
resolution without changing the output module.

## 4. Exact finite optimization

Put

`H_(Q,m)=im(Ev_(Q,m)) <=(Z/m)^(ell+1)`.               `(CRC19)`

For `a in Z/m`, let

`|a|_m=min_(k in Z)|a-km|`.                           `(CRC20)`

For a fixed separation threshold `0<c<=2`, define

`delta_(Q,m)(c)`
` =min { max_(1<=j<=ell)|b_j|_m/m :`
`          (b_1,...,b_ell,a) in H_(Q,m),`
`          |exp(2 pi i a/m)-1|>=c }`,                `(CRC21)`

with value `+infinity` if the feasible set is empty.

**Corollary 2 (linear central-certificate criterion).**  A sequence of
finite quotients `(Q_n,sigma_n)`, moduli `m_n`, and one constant `c>0`
satisfying

`delta_(Q_n,m_n)(c)->0`                               `(CRC22)`

produces a hyperlinear nonsofic group.

**Proof.**  Choose a minimizing image vector and a preimage under
`Ev_(Q_n,m_n)`.  Theorem 1 builds the exact finite central group and labels.
Equation `(CRC21)` is precisely `(CRS10)--(CRS11)` of the central-relator
criterion.  End proof.

After `H_(Q,m)` is known, `(CRC21)` is very small: its ambient dimension is
the fixed number `ell+1`, independent of `|Q|`.  Lift the preimage of
`H_(Q,m)` to a lattice in `Z^(ell+1)` containing `mZ^(ell+1)`.  Then
`(CRC21)` is an `ell`-coordinate `l_infinity` closest-vector problem with
the last coordinate restricted to a fixed circular arc.  It can be solved
by exact MILP, branch-and-bound, or enumeration in the fixed dimension.

## 5. Sparse cocycle construction

For small groups, `(CRC1)` can be constructed directly.  Use one variable
`omega(x,y)` for each pair in `(Q minus {1})^2`.  Add the sparse equations
`(CRC7)` for triples `(x,y,z)` and append the `d` variables `t_i`.
Equations `(CRC15)--(CRC16)` add only the prefix pairs occurring in the
fixed words `(r_1,...,r_ell,w)`.

For larger quotients, forming all `|Q|^3` cocycle equations is wasteful.
Use one of:

1. a finite free resolution and compute `H^2(Q,Z/m)`;
2. a polycyclic or rewriting-system resolution when available;
3. modular linear algebra prime-power by prime-power followed by CRT; or
4. the relation module of the specific quotient map from the free group.

Only the image `(CRC19)` should be retained.  Distinct cocycles with the
same relator/witness vector are computationally irrelevant.

An exact successful stage should emit:

1. the quotient multiplication or certified presentation of `Q`;
2. the modulus `m`;
3. a sparse cocycle or cohomology-coordinate vector;
4. the generator phases `t_i`;
5. the exact vector `(b_1,...,b_ell,a)`; and
6. verification of `(CRC7)`, `(CRC15)`, and the two bounds in `(CRC21)`.

This is a proof-producing CPU workload.  The expensive operation is the
finite cohomology image, not unitary optimization.

## 6. Immediate search strategy for the radical double

For the explicit Kun--Thom double, natural finite quotients already kill
the marked radical word.  Start with the congruence quotients of the two
vertices after identifying their common normal-closure image.  For each
small prime-power level:

1. compute only the cyclic-primary part of `H^2(Q,Z/m)`;
2. evaluate it on the fixed presentation relators and the marked fold word;
3. compute `H_(Q,m)` rather than storing all cocycles; and
4. solve `(CRC21)` exactly.

The Baumslag--Solitar integral amplifier predicts the promising moduli
`m=p^k`: a successful cocycle should have bounded relator exponents but a
marked exponent of order `p^k`.  Failure can also be certified.  If every
vector in `H_(Q,m)` satisfies a dimension-independent circular inequality

`|a|_m <= C max_j |b_j|_m`,                           `(CRC23)`

then that quotient family cannot realize the central certificate.  A dual
Smith/Farkas certificate for `(CRC23)` is more informative than another
failed matrix optimization.
