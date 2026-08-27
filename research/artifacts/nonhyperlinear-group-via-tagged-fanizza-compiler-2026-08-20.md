# Withdrawn tagged-Fanizza non-hyperlinearity attempt

**Status:** invalid.  This file is retained as an audit artifact, not as a
proof.  The failure is `exact-first-hit-ladder-kills-regular-carrier`.

The proposed recurrence below uses only exact spectral projections, unitary
transport, and tracial first-hit bookkeeping.  It therefore runs unchanged
in the canonical group von Neumann algebra.  At zero relator defect,
`(4.2)` would make the active carrier nondecreasing, charge a fixed positive
fraction of it in every orthogonal first-hit layer, and bound the total exit
trace by one.  Hence the initial carrier has canonical trace zero.  It cannot
simultaneously receive a positive lower bound from a nontrivial group word,
whose regular Hilbert--Schmidt distance from the identity is `sqrt(2)`.

The two-bit tag and context-atom bridge remain useful local placement
theorems.  They do not provide the finite-dimensional-only rank/multiplicity
step required to evade the regular-trace firewall.

## Former claimed theorem (withdrawn)

There is an algorithm which outputs a finite presentation of a group that is
not hyperlinear.

The construction combines the computable BCS signal family of
Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao, a finite
Schur--Clifford predicate compiler, a Thompson-indexed two-bit first-hit tag,
and a reverse Kleene fixed point.  The point which makes the construction
close is that the nonlinear three-atom survivor is never represented by one
group word.  It is an analytic reducing corner cut out by two commuting tag
involutions.

## 1. The source signal

For the recursively enumerable halting set there is a total computable family
of finite BCS systems `B_m`, distinguished involutions `d_m`, and integers
`C_m>0`.  Put `D_m=(1-d_m)/2`.  They satisfy

```text
m halts    => some tracial representation has tau(D_m)>0,        (1.1)
m diverges => every epsilon-perfect strategy has
              phi(D_m)<=C_m epsilon.                             (1.2)
```

Thus the native involution already has the orientation required by the
reverse diagonal: it survives on halting inputs and collapses in near-perfect
strategies on nonhalting inputs.

## 2. The finite presentation `Gamma_m`

The construction below is effective from the finite truth tables of `B_m`.
Only three nonlinear predicate shapes occur, and hence only finitely many
compiler roles occur for fixed `m`.

For every forbidden atom use its fixed gauge-doubled Schur--Clifford packet.
Its corrected relative Pauli words have central commutator `K`.  Central-
product it over `<J,K>` with the six-generator S3 endpoint packet, commuting
the two factors.  If `b` is a nonzero S3 endpoint word, then on
`Q=(1-J)/2` the four
endpoint atoms are

```text
P_(eps,delta)=Q(1+eps K)(1+delta b)/4.                 (2.1)
```

The distinguished exit is `P_(-,-)` and the live part is the sum of the other
three atoms.  All four atoms have the same local spin scale.  On each
forbidden selector atom, the central product makes `K=-1` and the two `b`
halves have equal trace, giving literally one active and one exit copy.  This
covers C13/C14 and C17 atom by atom.  The oriented C18 rank gates additionally
pack its residual multiplicities into the scalar inequalities

```text
2q_n<=q_(n+1)+e_n+delta_n,
e_n<=q_n+zeta_n.                                      (2.2)
```

Place freely amalgamated copies of the complete occurrence group on the
rational-tail orbit `X` of Thompson `V`, sharing only `J`.  Put two commuting
tag involutions `T_(x,1),T_(x,2)` at every site.  There are finitely many
relator prototypes:

```text
u_x J u_x^*=J,
u_x K_x u_x^*=T_(x,1),
u_x b_x u_x^*=T_(x,2),                                (2.3)
[u_x,T_(z,i)]=1                         (z!=x),
[T_(x,i),y_z]=1                         (x!=z),         (2.4)
```

where `y_z` ranges over the shared generators of the occurrence at `z`.
The rational-tail action has one diagonal and one off-diagonal ordered-pair
orbit and finitely generated point stabilizers.  Consequently a base
occurrence, a base tag pair, a base bridge, the finite presentations of the
local groups and `V`, finitely many stabilizer commutators, and one prototype
of every relation in (2.3)--(2.4) form a finite presentation.  Standard
prefix transporters derive the level-`n` relations with polynomial area.

Do this for the computably finite role set and amalgamate only the original
BCS words which are genuinely shared.  No commutator between shared words in
different BCS contexts is introduced.  Linear involution, commutator and
parity constraints are retained directly.  The result is the computable
finite presentation `Gamma_m`; the original `d_m` remains a named generator.

## 3. The tag identity

Choose distinct sites `x_0,x_1,...` of linear address length and put

```text
E_n=(1-T_(x_n,1))(1-T_(x_n,2))/4,
S_n=1-E_n,
C_0=1,                  C_n=product_(j<n)S_j.          (3.1)
```

On the current reducing carrier `R_n=C_nQ`, define

```text
P_exit=R_n(1-K_(x_n))(1-b_(x_n))/4,
P_live=R_n-P_exit.                                     (3.2)
```

Relations (2.3)--(2.4) give the exact identities

```text
u_(x_n)P_exit u_(x_n)^*=C_nQE_n,
u_(x_n)P_live u_(x_n)^*=C_(n+1)Q.                     (3.3)
```

This is the decisive incidence.  The exit and survivor are complementary in
the very tag table that defines the prefix.  Since all earlier tags commute
with the bridge, and all tags at sites distinct from `x_(n+1)` commute with
the shared generators of the next occurrence, `C_(n+1)Q` reduces that next
shared algebra.  Also

```text
C_n=C_(n+1)+C_nE_n,                                   (3.4)
```

so the first-hit projections `C_nE_n` are pairwise orthogonal and their
normalized traces have total at most one.

This avoids two invalid arguments.  A freely returned HNN chart and an
independent pulse do not imply survivor-prefix incidence: the pulse can be
negative on a returned live summand at zero defect.  And no involution word
can represent the nonlinear three-versus-one selector complement in all
tracial representations.  Equation (3.3) needs neither assertion.

## 4. Finite-matrix soundness

Let a matrix tuple for `Gamma_m` have total squared named-relator energy `E`.
At every fixed depth exactify the finite packet and tag tables using flexible
finite-group normalized-HS stability and align their common subgroups.  Word
telescoping, (2.3)--(2.4), and the polynomial prefix normal forms give

```text
transport error at level n <=p_m(n)sqrt(E),            (4.1)
```

where `p_m` is computable and independent of matrix dimension.  The exact
identities (3.3) therefore persist with the same type of error.  The local
rank calculation, the corner-localized BCS gap, and the tagged first-hit
partition give, for every role,

```text
2q_n<=q_(n+1)+e_n+delta_n,
e_n<=q_n+zeta_n,
e_n>=eta q_n-epsilon_n,
sum_(n<N)e_n<=1,                                      (4.2)
```

with rational `eta>0` and

```text
delta_n+zeta_n+epsilon_n<=A_m p_m(n)sqrt(E).           (4.3)
```

The scalar branching/first-hit ledger yields

```text
eta N q_0<=1+K_m(N)sqrt(E).                            (4.4)
```

Choose effective `A,d` with `K_m(N)<=A(1+N)^d` and, for `0<E<1`, take
`N=floor(E^(-1/(4d)))`.  Then

```text
q_0<=A'_m(E^(1/(4d))+E^(1/2-(d-1)/(4d))).             (4.5)
```

The sparse source-cut certificates for the three fixed predicate shapes
bound every base forbidden probability by a finite sum of (4.5) and packet
rounding losses.  Hence there is a computable effective modulus
`omega_m(E)->0` for the total forbidden mass.

It remains to obtain an actual commuting-operator strategy, rather than two
rounded tables which need not commute on the original matrix space.  Round
each original involution once to `B_j`.  Exactify each fixed elementary-
abelian context to commuting involutions `A_(c,j)`.  On
`L^2(M_d,tr_d)`, let Bob act by left multiplication by `B_j` and Alice by
right multiplication by `A_(c,j)`, with vector `1`.  These actions commute
exactly.  The disagreement probability is

```text
(1-Re tr(A_(c,j)B_j))/2=||A_(c,j)-B_j||_2^2/4,        (4.6)
```

and fixed polynomial telescoping controls the forbidden PVM outcomes.
Therefore every matrix tuple produces a commuting strategy `S_E` with

```text
epsilon(S_E)<=omega_m(E),
||U(d_m)-X_(D,m)||_2<=nu_m(E),                         (4.7)
```

for computable effective moduli tending to zero.

## 5. Exact completeness

If `m` halts, start with the marked GNS representation from (1.1), apply the
finite gauge covariantization, and take one countable amplification.  The
context-local packet theorem installs every finite packet while retaining all
original BCS words.  Fold every Thompson occurrence onto the corresponding
base occurrence.  Represent every tag pair by its endpoint pair `(K,b)`, take
all bridges and the Thompson action to be the identity, and use endpoint
centrality on the shared words.  Then (2.3)--(2.4) hold exactly.  Perfectness
makes the forbidden exit atoms vanish, and the action of `d_m` is unchanged.
Thus `Gamma_m` has an exact (possibly properly infinite and nontracial)
representation in which `d_m!=1`.  In particular `d_m` is algebraically
nontrivial.

## 6. Reverse Kleene diagonal

If `m` does not halt, (1.2) and (4.7) give, with `eta=Def(U)`,

```text
||U(d_m)-1||_2
 <=nu_m(eta)+2sqrt(C_m omega_m(eta))=:kappa_m(eta),    (6.1)
```

where `kappa_m(eta)->0` effectively.  Compute a positive rational `delta_m`
with `kappa_m(delta_m)<1`.

Given `m`, enumerate van Kampen consequences of the finite presentation
`Gamma_m` and halt exactly upon finding a proof that `d_m=1`.  Kleene's
recursion theorem supplies an index `m_*` for this program.  It cannot halt:
if it did, the proof would give `d_(m_*)=1`, while exact completeness for the
same halting index gives `d_(m_*)!=1`.  Thus it does not halt, and completeness
of van Kampen enumeration also gives `d_(m_*)!=1`.

If `Gamma_(m_*)` were hyperlinear, canonical-trace microstates would have
relator defect tending to zero and, because `d_(m_*)` is nontrivial,

```text
||U_n(d_(m_*))-1||_2 ->sqrt(2).                        (6.2)
```

For large `n`, (6.1) instead bounds that distance by `1`, a contradiction.
Therefore `Gamma_(m_*)` is not hyperlinear.  Every step producing its finite
presentation is effective.

## Audit boundary

The proof uses no runtime-uniform modulus, no finite-dimensional exact model
on the halting side, no scalar word for a nonlinear selector, and no claim
that unbounded qubit dimension obstructs hyperlinearity.  Its only
finite-dimensional capacity is the normalized-trace first-hit budget (3.4),
and the same tag table supplies the survivor incidence needed to iterate it.
