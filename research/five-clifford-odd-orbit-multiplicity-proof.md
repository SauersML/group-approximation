---
rg: 2
id: five-clifford-odd-orbit-multiplicity-proof
kind: proof
proves:
  - five-clifford-odd-orbit-cancels-phase-not-payload
---

# Proof

## 1. The five-generator packet is the order-32 extraspecial group

Consider
```text
K=<J,X_1,...,X_5 |
  J^2=X_i^2=1, J central, [X_i,X_j]=J (i!=j),
  X_1 X_2 X_3 X_4 X_5=J>.
```
In `K/<J>`, write `x_i` for the image of `X_i`.  The volume
relation gives
```text
x_1+x_2+x_3+x_4+x_5=0.
```
The commutator pairing on the span of `x_1,...,x_4` is the alternating
matrix with zero diagonal and all off-diagonal entries one.  Its kernel is
zero: if `v=(v_1,...,v_4)` and `s=sum_i v_i`, then the `j)-th
coordinate of its product with this matrix is `s+v_j`; all four vanish
only when all `v_j=s), and then `s=4s=0`, hence `v=0`.
Thus the quotient has dimension four and the commutator form is
nondegenerate.

The presentation is consistent: five complex Clifford involutions in
dimension four can be signed so that their product is `-I`; take
`J=-I`.  Hence `|K|=2^(1+4)=32), `Z(K)=<J>`, and `K` is
extraspecial.  Its character theory has sixteen linear representations,
all killing `J`, and one nonlinear representation
```text
rho:K -> U(4),             rho(J)=-I_4.                  (FC1)
```
In particular every representation on which `J=-I` is a multiple of
this unique spin representation.

## 2. A genuine order-five outer mover exists

The assignment
```text
alpha(J)=J,       alpha(X_i)=X_(i+1)       (indices mod 5)
```
preserves the presentation.  It preserves the volume relation because
moving `X_1` across the other four generators contributes `J^4=1`.
Thus `alpha` is an automorphism of order five.  It is outer: every inner
automorphism of a class-two group acts trivially on `K/Z(K)`, while
`alpha` cyclically permutes five distinct nonzero vectors there.

Put
```text
L=K semidirect_alpha C_5=<K,g | g^5=1, gX_i g^-1=X_(i+1)>.
```
Uniqueness of `rho` makes `rho composed with alpha` equivalent to
`rho`.  Choose an implementer `h`; since `h^5` is scalar, rescaling
`h` by a fifth root makes `h^5=I`.  Hence `rho` extends to a
four-dimensional representation `tilde rho` of `L), with
`tilde rho(g)=h`.

Let `pi` be any representation of `L) with `pi(J)=-I`.  After a
unitary identification,
```text
pi(k)=rho(k) tensor I_M              (k in K).
```
The operator `(h^* tensor I)pi(g)` commutes with `rho(K) tensor I), so
Schur's lemma gives
```text
pi(g)=h tensor D,                    D^5=I_M.             (FC2)
```
This is the automorphism-extension multiplicity which a phase-only
calculation omits.

## 3. The odd orbit cancels the Clifford phase, not the payload

Adjoin an involution `V` which centralizes `K), with no relation
between `V` and `g):
```text
widehat L=<L,V | V^2=1, [V,K]=1>.
```
For any involution `A in U(M)` and any `D in U(M)` with `D^5=I),
there is a representation
```text
pi(k)=rho(k) tensor I,
pi(g)=h tensor D,
pi(V)=I_4 tensor A.                                      (FC3)
```
Fix `a in {0,1}` and set `U=X_1^a V`.  Then
```text
pi(g^i U g^-i)
 =rho(X_(i+1))^a tensor D^i A D^-i.
```
Multiplying in cyclic order and using
`X_1 X_2 X_3 X_4 X_5=J` gives the exact identity
```text
pi(J^a) product_(i=0)^4 pi(g^i U g^-i)
 = I_4 tensor N_D(A),                                    (FC4)

N_D(A)=product_(i=0)^4 D^i A D^-i.                       (FC5)
```
Thus the proposed correction `J^a` removes precisely the spin phase.
It does not make the multiplicity norm `N_D(A)` equal to `A`.

This failure occurs in a completely finite exact model.  Take
`M=C^5), let `D` cyclically permute the coordinate basis, and put
```text
A=diag(-1,1,1,1,1).
```
The five conjugates in (FC5) are the five coordinate sign flips, so they
commute and
```text
N_D(A)=-I_5 != A,
||N_D(A)-A||_2=4/sqrt(5)                                (FC6)
```
for normalized Hilbert--Schmidt norm.  Every displayed group relation is
exact.  Therefore neither an approximate-representation estimate nor a
choice of Clifford signs can repair this orbit extractor.

## 4. A finite extension cannot remove the multiplicity uniformly

There is also a dimension obstruction to hiding the problem in a
"unique spin" finite overgroup.  Suppose a finite group `G` contains
`K), keeps `J` central, and its entire `J=-1` block consists of one
irreducible representation of dimension four.  Then
```text
dim_C p_- C[G]=|G|/2=4^2=16.
```
Hence `|G|=32), so `G=K).  Such a group has no outer mover.  Every
proper finite extension either introduces several negative types or
introduces multiplicity in restriction to `K).  Even when one selected
irreducible extension restricts with multiplicity one, arbitrary marked
representations may take direct sums of quotient twists; (FC2) then
recovers a nonscalar `D`.

## 5. What a finer Hecke corner would have to prove

For the cyclic extension, a character projection `q` for `C_5` makes
`D` scalar on its range.  If the payload operator `V` also reduces
`q`, then (FC5) becomes `A^5=A).  But reduction is an additional
global constraint, not a consequence of the Clifford packet.  Without
it, compression is not multiplicative.  For every projection `q` and
operators `x,y`,
```text
(qxq)(qyq)-qxyq=-qx(1-q)yq.                              (FC7)
```
Thus the exact obstruction is the off-corner leakage.  Requiring all
payload and transport words to reduce `q` returns to a matrix-factor
normalizer construction.  A nonnormal Hecke corner can evade the present
countermodel only by deriving a dimension-free estimate on the right
side of (FC7) from its group relators while still leaving the corner
nonreducing.  No phase or fusion identity in the five-Clifford packet
provides such an estimate.
