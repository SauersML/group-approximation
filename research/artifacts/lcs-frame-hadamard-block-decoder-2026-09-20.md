# A shared Hadamard frame and a nonreducing block decoder

Date: 2026-09-20. This is a bounded constructive attempt toward the
weighted linear-plus-conjugacy HALT-positive source. It produces an exact
candidate, its honest extension, a specific finite countermodel, and a
restricted quantitative decoder identifying the missing frame identity.
It does not produce the source or a new general impossibility theorem.
No local computation, build, or remote job was run.

## 1. Source interface and current primary checks

The current target is `lcs-weighted-conjugacy-halting-gap-source`:
bounded-width weighted involutory linear and conjugacy requirements,
with matrix-energy infimum zero on HALT and a uniform positive lower
bound on NONHALT. The already proved downstream lowering in
`lcs-constructive-compiler-2026-09-20.md` does not supply this source.

The latest version available on the primary arXiv record of
[Culf--Mastel](https://arxiv.org/pdf/2410.21223) was v2 on this date.
Definition 4.11 takes an infimum over finite-dimensional traces;
Theorem 4.14 and Corollary 4.16 include succinct 3-colouring with
perfect-value completeness and a constant gap. This does not assert
finite-dimensional attainment for every YES instance. The v2 correction
does not retain the original blanket claim for all TVF 2-CSPs.
[Culf, Corollary 7.3](https://arxiv.org/html/2603.14746v1#S7)
gives the dimension-independent finite-tracial loss bound
`148(L epsilon)^(1/4)` for quantum constraint-variable strategies.
[Taller--Vidick v2](https://arxiv.org/html/2507.22444v2#S1)
still uses noisy completeness and does not supply the missing perfect
groupification. These statements were read directly, not inferred from
metadata alone.

Repository searches covered the current source node, the controlled-Pauli
gauge and Clifford nodes, the nonabelian matrix-readout node, the previous
shared-anchor K4 artifact, and the proper-corner follow-up. The present
attempt does not require a common reducing corner and does not require
the original word-valued U to equal a controlled operator.

## 2. The concrete shared-frame candidate

Use all the generators and relations (1)--(4) of
`lcs-anchored-attack-2026-09-20.md`: one Pauli anchor X,Z,J; one shared
triple U_t,V_t,s_t of involutions per source atom; commuting normalization
rows on each source PVM; and the shared multiplicative marginal identities.
The marked sector has J=-I. In particular,

    [X,Z]_group=J,
    [U_t,X]=[V_t,Z]=1,
    [U_t,Z]_group=[X,V_t]_group=[U_t,V_t]_group=s_t,

and s_t commutes with the anchor and its own gates. Within each context
the U's commute, the V's commute, every s commutes with every gate,
`[U_t,V_r]=1` for distinct atoms, and

    product U_t=X,  product V_t=Z,  product s_t=J.

Add ONE shared involution H with the ordinary relations

    HXH=Z,       HZH=X,       [H,J]=1,
    H U_t H=V_t,             [H,s_t]=1  for every t.   (1)

All contexts use the same H; this is not a collection of private frames.
The anchor relations also imply `(HX)^4=J`, so the usual finite dihedral
Hadamard packet relations are present. The added requirements are
involutory conjugacies and commutations. The old controlled commutators
can likewise be written as conjugacies with commuting-product auxiliaries.
For fixed-size source contexts this stays within bounded-width
linear-plus-conjugacy syntax. No conversion of an operator sum to a word
is included in that assertion.

Every given exact finite-dimensional source PVM model extends perfectly
on `C^2 tensor K` using

    U_t=I tensor (1-p_t)+X_Pauli tensor p_t,
    V_t=I tensor (1-p_t)+Z_Pauli tensor p_t,
    s_t=I tensor (1-2p_t),
    H=(X_Pauli+Z_Pauli)/sqrt(2) tensor I.             (2)

This uses no commutation between distinct source contexts. Context
orthogonality proves normalization and marginal relations exactly.

## 3. A genuine nonreducing UCP replacement readout

Let `e_-=(I-X)/2` and K=e_-H_total. Anticommutation of X,Z gives
`tr(e_-)=1/2`. Compression

    Phi(A)=e_- A e_- restricted to K                  (3)

is unital completely positive into B(K), and for A>=0 obeys

    tr_K(Phi(A))=2 tr(e_- A)<=2 tr(A).                (4)

Because U_t commutes with X, Phi(U_t) is a self-adjoint involution.
Thus

    q_t=(I_K-Phi(U_t))/2                              (5)

is always a projection. In the honest extension (2), it is exactly p_t.
One could form replacement controlled operators from q_t in a fresh
`M_2 tensor B(K)`; the old U_t need not have controlled form.

This is not a common reducing-corner decoder: e_- does not reduce Z or H.
Nor does Phi send the entire port/anchor family to unitaries; for example
Phi(Z)=0. Consequently fixed-port multiplicative-domain or common-corner
obstructions alone do not decide this candidate.

There is even exact synchronization between the X-minus and Z-minus
versions of this readout. H identifies those two half-dimensional spaces,
and `H U_t H=V_t` identifies their compressed reflections. The remaining
issue is whether (5) satisfies the source partitions and edge constraints.

## 4. One GLOBAL Fourier frame extends the K4 countermodel

Use the explicit fifteen-dimensional binary space (V,b) and vector Omega
from Sections 3--4 of `lcs-anchored-attack-2026-09-20.md`. Its full basis,
pairing table and six edge-vector formulas are written there. The verified
properties needed here are

    sum_(t in C) v_t=Omega,
    b(v_t,v_r)=0  for distinct t,r in a context,
    v_a=sum_(t in F) v_t  for every marginal,
    b(v,Omega)=b(v,v)  for v in V,
    b(Omega,Omega)=1.                                 (6)

At every vertex i, the three vectors e_(i,0),e_(i,1),e_(i,2) sum to
Omega; Omega,e_(i,0),e_(i,1) are independent; and all three vertex
vectors have b(v,v)=1. The edge contexts consist of the six allowed
unequal-colour pairs of the K4 3-colouring source.

The old b need not be nondegenerate, so a Fourier transform on V alone
would not be justified. Instead make the explicit nondegenerate completion

    W=V direct-sum V^*,
    B((v,f),(w,g))=b(v,w)+f(w)+g(v).                  (7)

It has dimension 30. If (v,f) pairs to zero with every (w,g), testing
arbitrary g first gives v=0, then arbitrary w gives f=0. Thus B is
nondegenerate and symmetric, and its restriction to V is the original b.
Embed every source vector and Omega as (v,0).

On l2(W), of dimension `2^30`, define

    T_v |w> = |w+v>,
    M_v |w> = (-1)^(B(v,w)) |w>,
    F |w> = 2^(-15) sum_(y in W) (-1)^(B(w,y)) |y>.  (8)

Character orthogonality and symmetry give

    F^*=F,  F^2=I,  F T_v F=M_v,  F M_v F=T_v.        (9)

Now set

    X=T_Omega, Z=M_Omega, J=-I,
    U_t=T_(v_t), V_t=M_(v_t),
    s_t=(-1)^(b(v_t,v_t)) I,  H=F.                   (10)

Equations (6) prove every old relation exactly, by the same translation
and phase calculation as in the earlier artifact. Equations (9) prove
ALL the new relations (1) with this single global H, and every s_t is
scalar. In particular the common Hadamard packet and its actions across
different edge contexts really do agree. No context-specific conjugations
or implicit basis identifications are used.

These huge matrices are given only by their formulas; none was generated
or stored computationally.

## 5. Exact failure of the replacement PVM readout

Translations are jointly diagonalized by characters lambda in W^*.
The X=-1 sector used in (3) consists of the characters with
`lambda(Omega)=1`, uniformly weighted in normalized trace.
On such a character, the vertex projections in (5) have values

    q_(i,a)=lambda(e_(i,a)) in {0,1}.

Because the three vectors sum to Omega, their bits have odd parity.
Because Omega,e_(i,0),e_(i,1) are independent, the four possible triples

    100, 010, 001, 111                                 (11)

each have normalized trace 1/4 on K. Therefore, at every vertex,

    ||q_(i,0)+q_(i,1)+q_(i,2)-I_K||_(2,tr_K)^2 = 1,
    ||q_(i,a)q_(i,b)||_(2,tr_K)^2 = 1/4  (a!=b).       (12)

Every word relation, including global frame synchronization, has zero
defect, while the proposed replacement measurements have fixed positive
partition and overlap defects. Hence no vanishing-defect estimate for
this decoder can hold. The common frame identifies the two compressed
readouts but does not turn parity into a one-hot partition.

More basically, (10) is an exact finite-dimensional model of the whole
changed candidate on the K4 source, which has no perfect quantum
3-colouring. The earlier K4 audit proves its unrestricted quantum gap.
Thus this particular added-frame presentation cannot have any universal
perfect source decoder, not merely the compression (5). This statement
does not concern other matrix-unit synchronization gadgets.

## 6. A sufficient matrix-linear identity and its overlap estimate

There is a concrete positive local decoder once the actual matrix-algebra
Hadamard, rather than just a group normalizer, synchronizes the gates.
Define on the marked sector

    H_0=(X+Z)/sqrt(2).

It is a self-adjoint unitary because X and Z anticommute. Consider the
additional operator relations

    (X+Z)V_t=U_t(X+Z),
    equivalently V_t=H_0 U_t H_0.                     (13)

These involve operator addition. They are NOT asserted to be ordinary
group relations or to have an available linear-plus-conjugacy lowering.

Assume the old relations in Section 2 are exact. In an X-diagonal Pauli
decomposition write

    U_t=diag(A_t,B_t)=I tensor C_t+X tensor D_t,
    C_t=(A_t+B_t)/2,  D_t=(A_t-B_t)/2.

A_t,B_t are involutions. The relation `[U_t,Z]_group=s_t`, with s_t
commuting with the anchor, implies

    A_t B_t=B_t A_t,
    s_t=I tensor A_t B_t,
    p_t=(I-A_t B_t)/2,
    D_t=A_t p_t.                                      (14)

All A's and B's within one context commute. Indeed same-type commutation
follows from `[U_t,U_r]=1`; commutation of s_t with U_r then supplies the
two cross-type commutations. Hence all C,D,p within a context commute.

For distinct t,r in one context, direct expansion gives the ADDITIVE
commutator identity

    [U_t,H_0 U_r H_0]
       =2XZ tensor A_t A_r p_t p_r.                   (15)

Thus (13) and the additive form `[U_t,V_r]=0` of the already imposed
cross-type commutation force p_t p_r=0.
The parity equation `product s_t=-I` now forces `sum p_t=I`.
The multiplicative s-marginal equations become the desired additive
projection marginals, because the fine atoms are orthogonal. These p_t
therefore give an exact source PVM model, including the allowed-pair edge
PVMs for colouring. No literal controlled form for the old U_t is needed.

The same calculation identifies a dimension-independent error cost for
the missing relation, while keeping the other old relations exact. Put

    delta_r=||(X+Z)V_r-U_r(X+Z)||_2.

Then `||V_r-H_0U_rH_0||_2=delta_r/sqrt(2)`. The cross-type commutation
and the standard commutator Lipschitz bound give from (15)

    ||p_t p_r||_2 <= delta_r/sqrt(2).                 (16)

For a three-atom context the exact parity already restricts the joint
p-spectrum to the four odd patterns. Hence

    sum_t p_t-I=2p_0p_1p_2,
    ||sum_t p_t-I||_2 <= sqrt(2) delta_r              (17)

using any distinct t,r to bound the triple projection. This is a
restricted quantitative lemma, not a claimed estimate with all old
relations simultaneously approximate or a completed source compiler.

## 7. Why the ordinary shared H does not give (13)

Both H and H_0 exchange X and Z. Since H also fixes their sum under
conjugation, they commute. Their product

    R=H_0 H

is an involution commuting with the entire Pauli anchor. Thus it is an
operator on the anchor multiplicity space. The ordinary covariance gives

    V_t=H_0 R U_t R H_0.

Equation (13) is therefore equivalent to `[R,U_t]=0`. There is only one
global multiplicity involution R here, not a separate unknown per atom;
nevertheless its commutation with the shared gates is not supplied by (1).
The Fourier model (10) is an explicit simultaneous escape.

In fact, at a vertex its vector v has b(v,Omega)=1 and v!=Omega.
One computes

    H_0 T_v H_0=T_(v+Omega) M_Omega.

Its Hilbert--Schmidt inner product with M_v is zero, because their
relative word has nonzero translation v+Omega. Thus in (10)

    ||V_t-H_0 U_t H_0||_2^2=2,
    ||(X+Z)V_t-U_t(X+Z)||_2^2=4.                     (18)

This pinpoints the omitted matrix-linear relation at positive fixed
defect. Naming R as though it were the group word H_0 H would silently
use the additive definition of H_0; no such wordization is proved here.

Nor is generic enforcement of (13) a new open promise that can simply be
inserted into a route. The existing odd-tensor obstruction already rules
it out with this model-preserving port interface: take the three honest
scalar solutions of a single three-outcome PVM and tensor one copy of
each, conjugating the third. Every ordinary relation of any completion
extending all three models is retained, but all three s_t become -I.
Equation (13), by the proved decoder, would then require the three
projections p_t=I to be pairwise orthogonal. This is impossible.

The bounded outcome is consequently specific: this common Hadamard
covariance plus nonreducing block extraction fails, and (13) gives one
precise sufficient matrix-linear identity which this ordinary-word,
all-model-preserving interface cannot universally enforce. It
does not exclude different non-word readouts, larger source-specific
matrix-unit systems, or existential rather than all-model completeness.

Independent internal review checked the nondegenerate completion,
the single global Fourier involution, odd-pattern frequencies,
the overlap and partition constants, and squared frame defect four.
No repair was required. The checked scope retains the other relations
exact and does not supply a lowering of the additive frame identity.
