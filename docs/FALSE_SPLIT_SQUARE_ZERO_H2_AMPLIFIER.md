# Split square-zero groups automatically globalize the clock class into \(H_2\)

## Main observation

Let \(A\) be a finite group and let \(N\) be a finite abelian
\(\mathbb Z[A]\)-module.  Form the split semidirect product

\[
G=N\rtimes A.
\]

The local Baumslag--Solitar amplifier naturally lives in a group
\(H_1(B,I_M)\).  The point of this note is that, once the coefficient module
is installed as an induced summand of \(N\), the split extension forces that
class to survive into the global Schur multiplier \(H_2(G;\mathbb Z)\).

## Survival in the split LHS spectral sequence

The homological Lyndon--Hochschild--Serre spectral sequence is

\[
E^2_{p,q}=H_p(A,H_q(N;\mathbb Z))
\Longrightarrow H_{p+q}(G;\mathbb Z).
\]

Because \(N\) is abelian,

\[
E^2_{1,1}=H_1(A,N).
\]

### Theorem 1 (mixed homology survives)

For the split extension \(G=N\rtimes A\),

\[
E^\infty_{1,1}=E^2_{1,1}=H_1(A,N).
\]

Consequently, the degree-two filtration on \(H_2(G;\mathbb Z)\) has a
subquotient canonically isomorphic to \(H_1(A,N)\).

#### Proof

No differential can leave \(E^r_{1,1}\), because its target would have
negative first index.  The only possible differential entering it is

\[
d_2:E^2_{3,0}=H_3(A;\mathbb Z)
\longrightarrow E^2_{1,1}=H_1(A,N).
\]

The section \(A\to G\) splits the projection \(G\to A\) on homology.
Therefore the entire bottom row

\[
E^2_{p,0}=H_p(A;\mathbb Z)
\]

survives to \(E^\infty\); otherwise the edge copy of \(H_p(A;\mathbb Z)\)
could not be a direct summand of \(H_p(G;\mathbb Z)\).  In particular the
displayed \(d_2\) is zero.  There are no further possible incoming
differentials. \(\square\)

### Corollary 2 (order cannot disappear)

If \(H_1(A,N)\) contains an element of order \(m\), then
\(H_2(G;\mathbb Z)\) contains an element whose order is divisible by \(m\).
Moreover, every character of that cyclic subquotient extends to a character
of \(H_2(G;\mathbb Z)\).

#### Proof

Write the degree-two filtration as

\[
0\subset F_0\subset F_1\subset H_2(G;\mathbb Z),
\qquad
F_1/F_0\cong H_1(A,N).
\]

A lift to \(F_1\) of an element of order \(m\) must have order divisible by
\(m\) (or infinite order).  Since all groups here are finite, the order is
finite.  A character on the cyclic quotient extends first to \(F_1\) and
then to \(H_2(G;\mathbb Z)\), because \(\mathbb T\) is divisible. \(\square\)

## Shapiro installs the local clock class

Let \(B\leq A\) and let \(I\) be a finite \(\mathbb Z[B]\)-module.

### Theorem 3 (induced clock amplifier)

Suppose \(N\) contains an \(A\)-equivariant direct summand

\[
\operatorname{Ind}_B^A I.
\]

Then \(H_2(N\rtimes A;\mathbb Z)\) has a subquotient containing

\[
H_1(B,I).
\]

In particular, if

\[
H_1(B,I)\cong\mathbb Z/m\mathbb Z,
\]

then the Schur multiplier of \(N\rtimes A\) contains an element whose order
is divisible by \(m\).

#### Proof

Additivity of group homology in the coefficient module and Shapiro's lemma
give

\[
H_1(A,N)
\supset
H_1\!\left(A,\operatorname{Ind}_B^A I\right)
\cong H_1(B,I).
\]

Apply Theorem 1 and Corollary 2. \(\square\)

The direct-summand hypothesis can be weakened: it is enough to have maps

\[
\operatorname{Ind}_B^A I\longrightarrow N
\longrightarrow\operatorname{Ind}_B^A I
\]

whose composite induces multiplication by a unit on the relevant
\(p\)-primary class in \(H_1\).

## Application to the exact \(p^k\)-clock

For

\[
B=BS(1,p+1)
\]

acting on the augmentation module \(I_M\) of one \(c\)-cycle of length
\(M\), the proved integral calculation is

\[
H_1(B,I_M)
\cong
\mathbb Z/
\frac{(p+1)^M-1}{p}\mathbb Z.
\]

When \(M=p^k\), its \(p\)-primary part has exact order \(p^k\).  Therefore:

This calculation is for the infinite Baumslag--Solitar group.  It does **not**
by itself satisfy the hypotheses of Theorem 3, because a subgroup of the
finite ambient group \(A_k\) must be finite.  One needs the following finite
descent statement.

### Required lemma (finite metacyclic descent)

There must exist:

- a finite quotient \(B\twoheadrightarrow B_k\) through which the action on
  a finite coefficient quotient \(J_k\) of \(I_{p^k}\) factors; and
- a class
  \[
  \bar\kappa_k\in H_1(B_k,J_k)
  \]
  whose image under inflation/coefficient comparison is the clock class and
  whose order is exactly \(p^k\).

The explicit matrices suggest the metacyclic quotient

\[
B_k=
\langle \bar h,\bar c\mid
\bar h^{p^{k+1}}=1,
\bar c^{p^k}=1,
\bar c\bar h\bar c^{-1}=\bar h^{p+1}
\rangle,
\]

because \(p+1\) has order \(p^k\) modulo \(p^{k+1}\) for odd \(p\).
But factoring the clock representation through \(B_k\) is weaker than
proving that the integral homology generator descends with its exact order.
That homological assertion remains to be checked.

### Corollary 4 (global \(p^k\) curvature from an induced module)

Assume the finite metacyclic descent lemma above.  If the finite square-zero
tangent module \(N_k\) contains an \(A_k\)-equivariant direct summand

\[
\operatorname{Ind}_{B_k}^{A_k}J_k,
\]

then

\[
H_2(N_k\rtimes A_k;\mathbb Z)
\]

has elements of order divisible by \(p^k\).

Under these two explicit hypotheses, this supplies the unbounded Schur
exponent proved necessary for the central FALSE route.

## An explicit finite group family

The integral lattice in the preceding application has an exact finite
reduction; no conditional embedding into an unspecified finite module is
needed for the local curvature statement.

Fix an odd prime `p`, put `q=1+p`, and for `k>=1` set

\[
M=p^k,
\qquad n=p^{k+1}.
\]

Let

\[
B_k=
\langle h,c\mid h^n=c^M=1,\;chc^{-1}=h^q\rangle
\cong C_n\rtimes_q C_M.                              \tag{1}
\]

This is well defined because `q` has exact order `M` modulo `n`.
Let `X_M=B_k/<h>`, and let

\[
J_k=\operatorname{Aug}_{\mathbb Z/n}(X_M)
\cong I_M/nI_M.                                      \tag{2}
\]

Thus `J_k` is a finite abelian `B_k`-module, `h` acts trivially, and
`c` acts by the cyclic shift `S`.

### Theorem 5 (finite clock curvature)

The group `H_1(B_k,J_k)` contains a subgroup isomorphic to
`C_(p^k)`.  Consequently the explicit finite split group

\[
G_k=J_k\rtimes B_k                                   \tag{3}
\]

satisfies

\[
p^k\mid \exp H_2(G_k;\mathbb Z).                    \tag{4}
\]

#### Proof

Use the split extension

\[
1\to C_n\to B_k\to C_M\to1.                         \tag{5}
\]

Since `C_n` acts trivially on `J_k` and `nJ_k=0`,

\[
H_1(C_n,J_k)\cong J_k.                               \tag{6}
\]

The `C_M`-action on `(6)` combines the cyclic shift on `J_k` with
conjugation by `q` on `C_n`.  Up to reversing the cyclic orientation and
multiplying by a unit, the coinvariant operator is `S-q`.  Hence

\[
E^2_{0,1}\cong\operatorname{coker}(S-q:J_k\to J_k). \tag{7}
\]

The only differential which could enter `(7)` comes from the bottom row.
It vanishes because `(5)` is split: the section makes the bottom-row copy of
`H_*(C_M;Z)` a direct homological summand.  Therefore `(7)` embeds
as the bottom filtration subgroup of `H_1(B_k,J_k)`.

On the integral augmentation lattice, the `p`-primary component of

\[
\operatorname{coker}(S-q:I_M\to I_M)
\]

is cyclic of order `p^k`, by the Smith calculation

\[
v_p\!\left(\frac{q^M-1}{q-1}\right)=k.               \tag{8}
\]

Reducing the matrix modulo `n=p^(k+1)` tensors its cokernel with
`Z/n`; prime-to-`p` components disappear and the cyclic
`p^k`-component survives unchanged.  Thus `(7)` is `C_(p^k)`.

Finally apply Theorem 1 to the split extension

\[
1\to J_k\to G_k\to B_k\to1.
\]

Its degree-two filtration has a subquotient containing
`H_1(B_k,J_k)`, so a lift of the order-`p^k` element has order divisible
by `p^k`.  This proves `(4)`.  QED

The family `(3)` closes the local finite-curvature existence question.  It
does not yet identify `G_k` as a quotient of the full Kun--Thom vertex or
show that the corresponding character vanishes on the positive edge group.
Those are precisely the relative globalization gates below.

## Relative compatibility with the positive edge group

For the symmetric double, global curvature alone is not enough.  Its
restriction to the positive subgroup must be split, or at least have
asymptotically negligible relator phases.

The induced-module formulation makes this a module-support statement.  Let
\(A_+\leq A\) be the positive external subgroup and \(N_+\leq N\) its tangent
module.  If the clock summand admits a homological decoder

\[
H_1(A_+,N_+)\longrightarrow H_1(B,I_M)
\]

whose image misses the clock generator, while the global Shapiro map hits
that generator, then a character detecting the global \(p^k\)-class can be
chosen to vanish on the positive restriction.

Equivalently, the remaining relative check is that the clock generator is
nonzero in the quotient

\[
 H_1(A,N)\big/
\operatorname{im}\bigl(H_1(A_+,N_+)\to H_1(A,N)\bigr).
\]

This is a finite abelian module statement.

## Exact remaining bridge

The finite-module construction should now be audited for the following three
items, rather than for simultaneous matrices:

1. finite descent of the integral clock generator to an exact-order class in
   \(H_1(B_k,J_k)\);
2. an \(A_k\)-equivariant induced-module inclusion (or unit-split map)
   \[
   \operatorname{Ind}_{B_k}^{A_k}J_k\longrightarrow N_k;
   \]
3. nontriviality of the clock generator in the relative quotient
   \[
   H_1(A_k,N_k)/\operatorname{im}H_1(A_{+,k},N_{+,k}).
   \]

If all three hold with exact \(p^k\) order, the local clock class is already a
global relative Schur-multiplier class.  The only remaining step is the finite
central gauge/relator ratio, not external covariance.
