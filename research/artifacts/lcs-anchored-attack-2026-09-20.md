# Shared Pauli anchors: a constructive attempt and an exact global cheat

Date: 2026-09-20. Target: perfect quantum completeness and constant
soundness for an efficient binary-LCS halting protocol. This bounded
attack does not solve that target. It tests an explicit changed inner
mechanism with **globally shared** controlled gates, rather than merely
reattaching private magic squares to the noiseless TV test.

No local computation, build, exhaustive search, or matrix experiment was
run. All witnesses below are exact symbolic constructions.

## 1. Existing boundaries and why the candidate is different

Read before constructing the candidate:

- `central-character-profiles-affine-under-odd-tensor-products` and its
  proof: arbitrary scalar-port extensions are ternary-tensor closed.
- `magic-square-one-port-is-a-universal-phase-absorber` and
  `row-glued-magic-squares-absorb-noncommuting-ports`: private squares and
  a common commuting row do not authenticate source projections.
- `controlled-pauli-commutator-is-and-times-multiplicity-commutator` and
  `controlled-pauli-commutator-robustly-measures-projection-overlap`:
  literal controlled gates give the desired orthogonality decoder, but
  covariance leaves uncontrolled multiplicity operators.
- `independent-set-synchbcs-private-lcs-lowerings-have-qa-one`: a global
  counterexample already exists for its explicitly private architectures.
- `lcs-pc-zero-noise-coloring-cheat`: the repeated K4 three-colouring
  source has arbitrarily small quantum value, although its noiseless
  TV test is classically perfect.

The primary [Taller--Vidick source](https://arxiv.org/html/2507.22444v2#S4)
was rechecked at Definitions 3.2 and 4.1. Its questions identify endpoint
queries across edge contexts; this is why independently choosing a Pauli
frame in every context is insufficient for the candidate below.

One preliminary observation closes even the full-common-anchor private
variant. Let H be a finite Pauli group, with marked central J and unique
irreducible negative representation sigma. Suppose each context gadget
allows every honest scalar atom, shares H and the visible scalar ports,
and has otherwise private auxiliaries. Odd tensor products of atom
extensions still have J=-I and give the odd-product port signs. Their
restrictions to H are all sigma tensored with a multiplicity space.
After unitary alignment, put all gadgets on one common sigma factor and
separate multiplicity factors. They glue. Thus sharing **all** of a Pauli
anchor, rather than one row, does not suffice in this architecture.
The same argument applies to ports dressed by a fixed H-word: divide
the port word by that shared word before applying scalar tensor closure.

This observation is a consequence of the existing tensor theorem and
unique-negative-sector Pauli classification, not a separately claimed
new theorem here. It motivates actually sharing the gate auxiliaries.

## 2. Explicit globally shared controlled-gate candidate

Start with a finite projection constraint system: contexts consist of
PVMs {p_t}, and designated coarse atoms are sums of specified orthogonal
fine atoms. This includes the vertex and edge contexts of a colouring
projection game. Distinct contexts can have noncommuting projections;
only specified PVM and marginal relations are assumed.

Introduce one anchor X,Z,J, with X,Z,J involutions, J central, and

    [X,Z]=J.                                             (1)

Here [A,B]=ABA^{-1}B^{-1}. The intended sector is J=-I. For **each shared
source atom** t introduce shared involutions U_t,V_t,s_t with

    [U_t,X]=[V_t,Z]=1,
    [U_t,Z]=[X,V_t]=[U_t,V_t]=s_t,                       (2)
    [s_t,X]=[s_t,Z]=[s_t,U_t]=[s_t,V_t]=1.

For each PVM context C impose

    [U_t,U_r]=[V_t,V_r]=1                       (t,r in C),
    [U_t,V_r]=1                                (t!=r in C),
    [s_t,U_r]=[s_t,V_r]=[s_t,s_r]=1             (t,r in C),
    product_(t in C) U_t=X,
    product_(t in C) V_t=Z,
    product_(t in C) s_t=J.                              (3)

For every specified marginal p_a=sum_(t in F) p_t, where F is a subset
of one PVM context, impose the shared identities

    U_a=product_(t in F) U_t,
    V_a=product_(t in F) V_t,
    s_a=product_(t in F) s_t.                             (4)

One may also impose same-type commutation [U_t,U_r]=[V_t,V_r]=1
whenever the source projections are required to commute, and commutation
of s_t with the other atom's gates in that situation. These extra checks
are included in the countermodel below. Arbitrary cross-type commutation
cannot be added merely from [p_t,p_r]=0: overlapping projections do not
make their controlled X and Z gates commute.

**Perfect completeness holds at the operator-presentation stage.** Given
any exact source projection model on K, on C^2 tensor K put

    X=X_Pauli tensor I,        Z=Z_Pauli tensor I,
    U_t=I tensor (1-p_t)+X_Pauli tensor p_t,
    V_t=I tensor (1-p_t)+Z_Pauli tensor p_t,
    s_t=I tensor (1-2p_t),    J=-I.                      (5)

The formulas satisfy (1)--(2) directly. On a context, orthogonality
makes products of the controlled gates equal the gate controlled by the
sum, proving (3)--(4). No global commutation between distinct source
contexts was assumed. A finite-dimensional source stays finite-dimensional.

The proposed soundness decoding is p_t=(1-s_t)/2. If (2) universally
forced the literal forms (5), the overlap identity in the existing
controlled-Pauli node would recover every forbidden overlap. Sharing all
U_t,V_t across contexts and adding (4) is a concrete attempt to enforce
the missing consistency of their multiplicity operators.

This is a finite ordinary-group presentation, not yet an LCS compiler.
No unproved model-preserving group-to-LCS conversion is used below:
soundness already fails for this presentation itself.

## 3. A fifteen-dimensional binary space for the K4 source

Use the K4 three-colouring source from the earlier audit. At vertex i
there are atoms (i,a), a in {0,1,2}. At each unordered edge i<j there
are six atoms (ij,a,b), a!=b, with row and column marginals equal to the
vertex atoms. Introduce a vector space V_0 over F_2 with basis

    Omega, e_(i,0), e_(i,1)               (i=1,2,3,4).

It has dimension nine. Define

    e_(i,2)=Omega+e_(i,0)+e_(i,1).                        (6)

Thus sum_a e_(i,a)=Omega for every vertex. Let P be the 3-by-3
permutation matrix of the cycle a -> a+1 modulo 3. Define a symmetric
bilinear form b_0 by

    b_0(Omega,Omega)=1,
    b_0(Omega,e_(i,a))=1,
    b_0(e_(i,a),e_(i,c))=delta_(a,c),
    b_0(e_(i,a),e_(j,c))=P_(a,c)                 (i<j).  (7)

Symmetry specifies the reversed order. These prescriptions are consistent
with (6): P has all row and column sums one. In particular no symmetry
of the individual 3-by-3 block P is required; its reverse block is P^T.

For edge ij, let E_ij have six formal basis vectors f_(a,b), a!=b,
with diagonal bilinear form

    d_ij(f_(a,b),f_(c,d))
      =delta_((a,b),(c,d)) P_(a,b).                      (8)

Its row sums r_a and column sums c_b span a five-dimensional subspace R.
To see this, a relation among rows and columns has coefficients
alpha_a+beta_b=0 for every a!=b. The six-edge bipartite graph is connected,
so all coefficients agree; the only relation is sum_a r_a=sum_b c_b.
The map

    r_a -> e_(i,a),    c_b -> e_(j,b)                    (9)

is therefore an isomorphism onto the five-dimensional space
H_ij=span{Omega,e_(i,0),e_(i,1),e_(j,0),e_(j,1)}.
It is an isometry: row/row and column/column pairings are Kronecker
deltas, and the row/column pairing is P_(a,b), exactly (7).

Adjoin one basis vector t_ij to V_0 for each of the six edges. Thus

    V=V_0 direct-sum span{t_ij:i<j},  dim(V)=15.         (10)

Map f_(0,1) to t_ij. This defines a linear extension of (9), since
f_(0,1) is not in R: every row and column has even coordinate weight,
whereas f_(0,1) has odd weight. For full explicitness, the other images are

    f_(0,2) -> e_(i,0)+t_ij,
    f_(2,1) -> e_(j,1)+t_ij,
    f_(2,0) -> e_(i,2)+e_(j,1)+t_ij,
    f_(1,0) -> e_(j,0)+e_(i,2)+e_(j,1)+t_ij,
    f_(1,2) -> e_(i,1)+e_(j,0)+e_(i,2)+e_(j,1)+t_ij.    (11)

Extend b_0 symmetrically by

    b(t_ij,t_ij)=b(t_ij,Omega)=1,
    b(t_ij,e_(i,0))=1, b(t_ij,e_(i,1))=0,
    b(t_ij,e_(j,0))=0, b(t_ij,e_(j,1))=1,
    b(t_ij,e_(k,0))=b(t_ij,e_(k,1))=0       (k notin {i,j}),
    b(t_ij,t_kl)=0                         (ij!=kl).    (12)

On H_ij, these are precisely the pairings of f_(0,1) with the row and
column sums in (8). Consequently (9)--(12) is an isometric embedding
of each (E_ij,d_ij) into (V,b). Cross-pairings between different added
directions are unrestricted by the candidate and may be set to zero.

Denote the resulting vector for any vertex or edge atom by v_t. We have

    sum_(t in C) v_t=Omega                    (every context C),
    b(v_t,v_r)=0                             (t!=r in C),
    v_a=sum_(t in F) v_t                     (each marginal),
    b(v,Omega)=b(v,v)                         (every v in V). (13)

For the last identity, both sides are linear functions of v over F_2
because b is symmetric; they agree on the displayed basis by (7),(12).

## 4. Exact finite Pauli representation of all shared equations

On the Hilbert space ell^2(V), of dimension 2^15, set

    X_v |w> = |w+v>,
    Z_v |w> = (-1)^{b(v,w)} |w>.                         (14)

These are involutions satisfying

    X_v X_w=X_(v+w),    Z_v Z_w=Z_(v+w),
    [X_v,Z_w]=(-1)^{b(w,v)} I.                           (15)

No nondegeneracy of b is needed. Define the candidate's generators by

    X=X_Omega, Z=Z_Omega, J=-I,
    U_t=X_(v_t), V_t=Z_(v_t),
    s_t=(-1)^{b(v_t,v_t)} I.                             (16)

Since b(Omega,Omega)=1, (1) holds. Equation (13) gives all three
commutators in (2). Source s_t operators are scalar, so every required
s commutation holds. All U operators mutually commute and all V
operators mutually commute, even across distinct contexts. Orthogonality
in (13) proves the cross-type commutations within a PVM; the vector sums
prove all normalization and shared marginal identities in (3)--(4).
Thus **every** proposed relation holds at zero defect, with one common
anchor and one globally shared pair of gates per source atom.

The decoded source is invalid. At every vertex, (7) gives

    s_(i,0)=s_(i,1)=s_(i,2)=-I,
    (1-s_(i,a))/2=I for all three colours.                (17)

The vertex partition sum is 3I, not I. More precisely, the source edge
atom f_(0,2) has b(v,v)=0 but v=e_(i,0)+t_ij!=0. Hence

    s_(ij,0,2)=I but U_(ij,0,2)=X_v!=I.                 (18)

Its decoded projection is zero while its gate still carries a nontrivial
translation. That inactive atom can carry the global marginal identities.
This is exactly what was omitted by the tempting model that uses only
the three active matching atoms and sets the other gates to identity.
Such a restricted model runs into matching holonomy around triangles;
(18) supplies an explicit global escape from that apparent obstruction.

### Even the full local Boolean commutator table survives

For a subset A of one context, define v_A=sum_(t in A) v_t. By the
diagonal form on that context,

    b(v_A,v_B)=sum_(t in A intersection B) b(v_t,v_t).

Therefore the representation also satisfies

    [U_A,V_B]=s_(A intersection B),
    U_A=product_(t in A) U_t,
    V_A=product_(t in A) V_t,
    s_A=product_(t in A) s_t.                             (19)

These are the local AND-phase identities of the honest controlled
operators. Adding all of them, and identifying the subset gates under
the same marginal rules, still does not eliminate (16). Thus the
failure is not repaired by completing the local Boolean function table.

## 5. Repetition, quantum soundness, and exact remaining mechanism

For u repeated copies, use V^{tensor-u} over F_2 and the tensor-product
bilinear form b^{tensor-u}. Map a product atom (t_1,...,t_u) to
v_(t_1) tensor ... tensor v_(t_u), and use Omega^{tensor-u} as the anchor
vector. Each product context is again orthogonal, its vectors sum to
Omega^{tensor-u}, and every marginal is a sum of its fine atoms.
Moreover b^{tensor-u}(v,Omega^{tensor-u})=b^{tensor-u}(v,v): verify this
on a tensor basis using (13), then use linearity of the diagonal.
The construction (14)--(16) therefore gives a finite representation of
dimension

    2^(15^u)                                             (20)

for every repeated candidate. The dimension is large but finite, which
is enough to refute a dimension-independent soundness claim.

By `lcs-pc-zero-noise-coloring-cheat`, the original K4 game has
unrestricted quantum value at most 11/12, its projected game P has
value at most sqrt(23/24), and omega_q(P^{tensor-u}) tends to zero by
projection-game parallel repetition. Thus (20) supplies exact candidate
models even on arbitrarily low-value source games. It rules out a
generic positive-success source decoder for this changed gate test.

The honest completeness extension (5) is valid. The failed step is its
converse: covariance, normalization, shared marginals, and the full local
commutator table do not force a zero projection to have identity gates.
Algebraically, the construction retains an F_2-valued, parity-weighted
measurement structure; positivity and one-hot support are not recovered.

A successful modification must detect the nontrivial isotropic gates
in (18), or use a readout not given by (1-s_t)/2. Simply adding the
word relation U_t=1 whenever s_t=1 is not a group presentation: it is an
implication conditioned on a spectral sector. Replacing it by a universal
atomwise group gadget returns to the already established tensor no-go.
No claim is made that every globally shared noncommutative mechanism
fails; the present result covers the explicitly displayed equations and
their full local subset table.

## 6. Bounded qutrit/S3 follow-up

One proposed alternative balances three colour ranks using order-three
clock/shift anchors, then tries to make a relative clock r omit its
trivial eigenspace by forcing the standard S3 type. At the level of a
finite group packet H with a selected central character zeta on Z,
this has a direct obstruction. If <r> intersection Z is trivial, the
character zeta on Z and the trivial character on <r> combine on
Z<r>. Inducing that character to H gives a marked finite-dimensional
representation with a nonzero r-fixed subspace. If the intersection is
nontrivial, r has order three and hence belongs to Z; its value is then
one fixed scalar zeta(r), so that sector cannot permit both nontrivial
cube roots. This is an application of the existing finite-character
induction and fixed-phase tensor obstructions, not a new node.

The complementary tensor check reaches the same conclusion for scalar
atom extensions: representations with r-values omega, omega, omega^2
have ternary tensor r-value omega*omega*conj(omega^2)=1 while retaining
the common central character. A finite S3 anchor alone does not supply
the required missing-type selection. This argument is deliberately not
promoted to a theorem about every infinite source-dependent compiler or
about arbitrary non-group-word corner readouts.

## 7. Scope and prior-art check

Repository searches covered shared controlled gates, Pauli splitting,
projection partitions, bilinear source models, anchor/tensor closure,
and magic-square interfaces. The nearest existing results identified
above either leave the shared multiplicity lock open or treat private
auxiliaries. This artifact supplies the actual globally shared candidate
equations and a finite exact countermodel with explicit marginal vectors.
No originality claim is made for Pauli representations of binary
bilinear spaces. The new maintained content is their application to this
specific proposed source decoder and the zero-projection escape (18).

The full hardness target, uniform quantitative gap, and efficient succinct
LCS verifier remain unresolved. No source theorem or repository metadata
is presented as proving them.

Independent review on 2026-09-20: the root checked consistency of (7),
all six edge-vector formulas and their active diagonal entries
(0,1),(1,2),(2,0), the characteristic-vector identity in (13), and the
tensor-power construction. The root also reported a passing sibling
review. No flaw was found. This is recorded mathematical cross-review,
not a formal or computational verification claim.
