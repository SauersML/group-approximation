---
rg: 2
id: multi-edge-hecke-balance-and-cycle-rigidity-proof
kind: proof
proves:
  - multi-edge-hecke-defects-do-not-cancel-positively
---

# Proof

Let (M,tau) be a finite von Neumann algebra with faithful trace and let Q
be a projection.

## 1. Positive mixtures of complete transports

For each edge i, let U_i be unitary and let
```text
P_(i,1),...,P_(i,m_i)
```
be a PVM summing to Q.  Define
```text
R_(i,v)=Q U_i P_(i,v) U_i^* Q,
D_i=Q U_i(1-Q)U_i^*Q.
```
Then
```text
sum_v R_(i,v)=Q-D_i,                    D_i>=0.           (MHB1)
```
If w_i>0 and sum_i w_i=1, then
```text
sum_i w_i sum_v R_(i,v)=Q
```
holds exactly only if sum_i w_i D_i=0.  Positivity and faithfulness imply
D_i=0 for every i.  By finite rank balance, this is equivalent to
```text
U_i Q U_i^*=Q
```
for every i.  Thus positive averaging never compensates one edge's
off-corner defect with another edge.

## 2. Outcome-gated edges

Now let P_1,...,P_k be orthogonal projections summing to Q and allow a
different unitary U_i for each outcome.  Put
```text
R_i=Q U_i P_i U_i^*Q.
```
The exact trace loss is
```text
tau(P_i)-tau(R_i)
 =||(1-Q)U_iP_i||_2^2>=0.                               (MHB2)
```
If sum_i R_i=Q, summing (MHB2) shows that every term vanishes:
```text
(1-Q)U_iP_i=0                         for every i.        (MHB3)
```
Consequently R_i=U_iP_iU_i^* is a projection in QMQ, and the R_i are
orthogonal.  Complete outcome-wise routing is possible, but no leakage is
being cancelled: each used domain slice has zero leakage.  Only the
unused part of Q under U_i may leave the corner.

The same statement holds for partial-isometry amplitudes W_i with
W_i^*W_i=P_i.  If their compressed final effects sum to Q, then
(1-Q)W_i=0 for every i.  Cross terms may cancel inside the definition of
a combined W_i, but after combination the selected amplitude itself has
zero leakage.

## 3. Compressed cycles

Set
```text
X_i=Q U_i Q in QMQ.
```
Each X_i is a contraction.  Suppose a compressed cycle is exactly
unitary:
```text
X_1 X_2 ... X_k=V,                  V^*V=VV^*=Q.          (MHB4)
```
Writing Y=X_2...X_k gives
```text
Q=VV^*=X_1 YY^*X_1^* <= X_1X_1^* <=Q.
```
Hence X_1X_1^*=Q.  Traciality and X_1^*X_1<=Q imply
X_1^*X_1=Q as well, so X_1 is unitary in QMQ.  Then
X_2...X_k=X_1^*V is unitary, and induction proves that every X_i is
unitary.  For X_i=QU_iQ, unitarity is equivalent to
```text
(1-Q)U_iQ=(1-Q)U_i^*Q=0,
```
hence U_iQU_i^*=Q.  Therefore a sequential cycle of compressed group
unitaries cannot use signed return paths to repair leakage: exact unitary
holonomy forces every edge to reduce Q.

## 4. Complementary S4 edges are finite outcome routers

Use the D_8 packet in S_4:
```text
J=(1 3)(2 4),       a=(1 4)(2 3),       b=Ja=(1 2)(3 4),
Q=(1-J)/2,
P_+=Q(1+a)/2,       P_-=Q(1-a)/2.
```
Let
```text
U_-=(3 4),          U_+=(2 3).
```
Conjugation by U_- swaps J and a and fixes b; conjugation by U_+ swaps J
and b and fixes a.  It follows that
```text
U_- P_- U_-^*=P_-,
U_+ P_+ U_+^*=P_+,                                      (MHB5)

Q U_- Q U_-^*Q=P_-,
Q U_+ Q U_+^*Q=P_+.                                     (MHB6)
```
Thus the full-edge defects are complementary,
```text
D_-=P_+,             D_+=P_-,
```
and certainly do not cancel positively.  Gating the first edge by P_-
and the second by P_+ gives the complete context P_-+P_+=Q with zero
slice leakage, exactly as (MHB3) predicts.  Equivalently,
```text
W=U_+P_+ + U_-P_-
```
is a unitary in the Q corner even though neither ambient U_+ nor U_-
reduces Q.  This is a finite controlled router in C[S_4].

## 5. Coherent interference exists, but already in a finite matrix block

There is genuine amplitude cancellation if additive linear combinations
are allowed.  In M_2(C), take
```text
Z=diag(1,-1),
H=2^(-1/2) [[1,1],[1,-1]],
Q=(I+Z)/2,
U_1=H,                U_2=ZH.
```
Both off-corner vectors (1-Q)U_iQ are nonzero and are negatives of each
other.  Direct multiplication gives
```text
2^(-1/2)(U_1+U_2)Q=Q.                                  (MHB7)
```
The unitaries H and Z generate the finite dihedral group of order 16.
If e is the primitive central idempotent for this faithful
two-dimensional representation, (MHB7) is an exact identity in the
finite matrix block e C[D_16].  Thus coherent cross terms can cancel
before the positive effect is formed, but the smallest such cancellation
is itself a finite-dimensional fusion absorber.  It is not a group-word
cycle and it supplies no infinite-versus-finite trace separation.

Together, the five parts exhaust the elementary multi-edge mechanisms:
positive defects do not cancel; exact compressed cycles force reduction;
outcome gating uses zero-leak slices; and coherent additive interference
is possible but must be coupled to a separate non-finite source
obstruction.
