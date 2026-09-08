# Prime cyclic cancellation lifts

Date: 2026-09-07. This is a complete proof of a conditional criterion,
not a proof of Kaplansky's Direct Finiteness Conjecture. It extends the
repository's characteristic-two cancellation arguments to every prime.
The final universal existence assertion remains unproved.

## 1. Coefficient occurrences and cancellation blocks

Let p be prime and BA=1 in F_p[G]. Replace a coefficient c!=0 by c
copies of its group label, using the integer 1<=c<=p-1. Thus

\[
B=\sum_{i=0}^{m-1}[t_i],\qquad A=\sum_{j=0}^{n-1}[s_j].
\]

These are lists of occurrences, not necessarily sets. In particular,
two occurrences of the same group label have independent lifting variables.
There is no relation identifying their coefficient variables.

The number of product cells with label g is congruent to 1 modulo p
if g=1 and to 0 otherwise. Choose one cell labelled 1 as the pivot,
reindex it as (0,0), and partition the other cells, separately in each
product fiber, into p-element blocks. Order the cells in each block as
c_0,...,c_(p-1), where c_a=(i_a,j_a). This construction uses only the
forward equality and proves the existence of such blocks. For arbitrary
presented groups it supplies no algorithm for deciding product equality.

## 2. The central cyclic criterion

Form the finitely presented group H with generators X_i,Y_j,J and
relations

\[
J^p=1,\quad J\text{ central},\quad X_0=Y_0=1,
\qquad X_{i_a}Y_{j_a}=J^a X_{i_0}Y_{j_0}
\]

for every block and every a=1,...,p-1. The subscript 0 on a block cell
means its local base; it must not be confused with the distinguished pivot.
Assume J!=1 in H. Since p is prime, J has order exactly p.

Choose a primitive complex p-th root zeta. Put O=Z[zeta] and

\[
R=O[H]/([J]-\zeta),\qquad
e=\frac1p\sum_{a=0}^{p-1}\zeta^{-a}[J]^a\in\mathbb C[H].
\]

The element e is a nonzero central idempotent and e[J]=zeta e. Choose
one representative h of each coset of <J>. As an O-module, O[H] is
the direct sum of the blocks spanned by [h],[Jh],...,[J^(p-1)h].
The quotient relation replaces [J^a h] by zeta^a[h], with no further
additive relation: on each block it is evaluation of
O[T]/(T^p-1) at T=zeta. Thus R is free over O on the chosen representatives.

The map R -> e C[H] e sending [h] to e[h] and O to Oe is injective:
the representative images have disjoint group supports, and their
coefficients lie in the faithfully embedded subring O of C. It is unital
when the target corner has identity e. Hence the ordinary group ring R[G],
whose G-labels commute with its coefficients, embeds in e C[H x G] e.

The classical characteristic-zero direct-finiteness theorem applies to
C[H x G] and its corner. For clarity, a corner of a directly finite
unital ring is directly finite: xy=e in eSe gives
(x+1-e)(y+1-e)=1, whose reverse yields yx=e. Therefore R[G] is directly
finite. No approximation hypothesis on H or G has been used.

Let x_i,y_j denote the images of the generators in R, and set

\[
\widetilde B=\sum_i x_i[t_i],\qquad
\widetilde A=\sum_j y_j[s_j].
\]

For each block all external group products agree, while its coefficient
sum is

\[
\sum_{a=0}^{p-1}x_{i_a}y_{j_a}
=\left(\sum_{a=0}^{p-1}\zeta^a\right)x_{i_0}y_{j_0}=0.
\]

The pivot contributes x_0y_0[t_0s_0]=1. Consequently B_tilde A_tilde=1,
and direct finiteness gives A_tilde B_tilde=1. Evaluation zeta->1 and
every element of H->1 defines a ring map R -> F_p: the cyclotomic
relation evaluates to p=0, and [J]-zeta evaluates to zero. Reducing the
reverse identity gives AB=1. This proves the criterion.

## 3. Exact identities among the relators

Let F be free on the X_i,Y_j other than X_0,Y_0. For every labelled
nonbase block cell e=(block,a), put

\[
r_e=X_{i_a}Y_{j_a}(X_{i_0}Y_{j_0})^{-1},\qquad \ell_e=a,
\]

and let N be their normal closure. The criterion has an exact alternative:
J collapses in H if and only if some identity in F of the form

\[
\prod_{b=1}^q w_b r_{e_b}^{\epsilon_b}w_b^{-1}=1,
\qquad\epsilon_b\in\{1,-1\},
\]

has total label sum_b epsilon_b ell_(e_b) nonzero modulo p.

One direction follows by substituting r_e=J^(ell_e). Such an identity
makes a nonzero power of J equal to one, forcing J=1 since p is prime.
For the converse suppose all such identities have total label zero. For
n in N define phi(n) as the label sum of any expression as a product of
conjugated relators or their inverses. Concatenating two expressions, one
inverted, proves that phi is well-defined. It is a homomorphism N -> F_p
and is invariant under conjugation by F. If there are any blocks, one of
their labels is 1, so phi is onto. Its kernel K is normal in F, and F/K
is a central extension of F/N by N/K=C_p. The image of each r_e is the
ell_e-th power of a single nonidentity central element. This realizes all
the relations of H with J nonidentity. With no blocks, J is an independent
central C_p factor, so it also survives.

If the displayed unsigned presentation is aspherical, its relation module
N/[N,N] is free over Z[F/N] on the displayed relators. Indeed the
contractible universal cover of its two-complex has zero first and second
homology, so the boundaries of its lifted two-cells identify their free
module with the first homology of its one-skeleton, namely N/[N,N].
Assigning each free basis element its label modulo p and taking the
augmentation on coefficients gives phi. This proves the asphericity
corollary for this presentation, not for other presentations of the group.

## 4. A finite scalar criterion over every prime

In the free abelian occurrence lattice Z^(m+n), define

\[
v_e=e_{i_a}+f_{j_a}-e_{i_0}-f_{j_0},\qquad
V=(v_e)_e,\qquad \ell=(\ell_e)_e.
\]

The rule chi(Vu)=zeta^(ell dot u) defines a character on L=im(V)
if and only if ell dot u=0 modulo p for every integral u with Vu=0.
The **full integral kernel** is required; independently clearing the
denominators of a rational basis can miss elements of that lattice.

Suppose the criterion holds. In Smith coordinates write
L=direct-sum_(i=1)^r d_i Z b_i, with positive d_i dividing d_(i+1).
If chi(d_i b_i)=zeta^(c_i), write d_i=p^(h_i)o_i with p not dividing
o_i. For c_i!=0, choose an integer b such that b o_i=c_i modulo p
and assign b_i the value exp(2 pi i b/p^(h_i+1)). Its d_i-th power
is zeta^(c_i), as required. For c_i=0 assign value 1, and assign 1 to
the remaining ambient basis elements. These choices extend chi to a
character on Z^(m+n) with values in roots of unity of p-power order.

Write the resulting row and column values as alpha_i,beta_j. Their
products in a block are zeta^a times the base product. Normalize by
dividing all alpha_i by alpha_0 and all beta_j by beta_0; all block
relations remain true, and the pivot product becomes 1. These phases
give a representation of H retaining J. Equivalently, they lift BA=1
directly to Z[zeta_(p^N)][G] and reverse there by characteristic-zero
direct finiteness. The map zeta_(p^N)->1 to F_p is valid because
Phi_(p^N)(1)=p.

In exponents the scalar condition is exactly

\[
V^Tq=p^{N-1}\ell\pmod {p^N}.                         \tag{1}
\]

Conversely, pairing (1) with any integral u in ker(V) gives
p^(N-1) ell dot u=0 modulo p^N, and hence ell dot u=0 modulo p.
This proves equivalence with existence of such a finite phase vector.

For r>0 the construction allows N<=1+v_p(d_r). Every column v_e has
Euclidean norm at most 2, even if two cells share a row or column.
Hadamard's inequality bounds every nonzero r-by-r minor by 2^r, while
d_1...d_r is the gcd of those minors. Thus p^(v_p(d_r))<=2^r, and
one may take

\[
N\le 1+\left\lfloor\log_p(2^r)\right\rfloor.
\]

Separate row and column sums vanish in each column, so r<=m+n-2.
The empty-block case needs no phase calculation. These statements give a
finite decision procedure for the scalar subclass, not a procedure for
deciding whether J survives in an arbitrary finitely presented H.

## 5. An explicit characteristic-three example requiring ninth roots

Let G=C_3 with generator g. Over F_3[G] put

\[
B=2+g+2g^2,\qquad A=1+g.
\]

Their product is 4+3g+3g^2=1 in F_3[G]. Use row occurrences
(1,1,g,g^2,g^2), column occurrences (1,g), and pivot (0,0).
Order the three remaining blocks as follows; positions in each row of
the table receive labels 0,1,2 in that order.

| Common group product | Cell with label 0 | Cell with label 1 | Cell with label 2 |
| --- | --- | --- | --- |
| 1 | (4,1) | (3,1) | (1,0) |
| g | (0,1) | (2,0) | (1,1) |
| g^2 | (3,0) | (2,1) | (4,0) |

Let z be a primitive ninth root. The row phase exponents modulo 9 are
(0,6,4,2,8) and the column exponents are (0,1). In the three blocks
the product exponents are respectively (0,3,6), (1,4,7), (2,5,8).
All therefore satisfy (1) with p=3,N=2. With w=z^3, the lifted factors
are

\[
\widetilde B=(1+z^6)+z^4g+(z^2+z^8)g^2,
\qquad \widetilde A=1+zg.
\]

Their product has coefficients 2+w+w^2=1 at 1, z(1+w+w^2)=0 at g,
and z^2(1+w+w^2)=0 at g^2. This verifies the lift directly in
Z[z]/(z^6+z^3+1)[C_3]. Reduction z->1 recovers the specified A,B.

Cube roots cannot realize these same ordered blocks. Normalize the pivot
row and column exponents to zero. Let the other row exponents be x_1,...,x_4
and the second column exponent be y, all modulo 3. The block relations imply

\[
x_1=2,\quad x_2=y+1,\quad x_2+y=1+x_3,\quad
x_4=2+x_3,\quad x_1=2+x_4+y.
\]

The first four give x_3=2y and x_4=2y+2. Substitution in the last gives
2=4+3y modulo 3, a contradiction. Thus no order-three phase solution
exists, whereas the displayed order-nine solution works. This conclusion
concerns this ordering and partition; it asserts nothing about all other
partitions of the same two-sided inverse.

`experiments/kaplansky_prime_cancellation.py` checks the cell partition,
group products, phase differences, and both lifted products by exact
polynomial reduction modulo z^6+z^3+1. It also exhausts all 3^5 normalized
cube-root assignments. The committed JSON records the complete fixed
input and outputs. Reproduce it with:

```sh
python3 experiments/kaplansky_prime_cancellation.py \
  --output research/artifacts/kaplansky-prime-cancellation-c3.json
python3 experiments/kaplansky_prime_cancellation.py \
  --verify research/artifacts/kaplansky-prime-cancellation-c3.json
```

This replay verifies one fixed finite example. The general criterion is
proved above in prose; it has not been formalized in Lean.

## 6. Scope and sources

The starting point is the existing Cairn criterion
`central-sign-survival-forces-reverse-cancellation` and its scalar version
`cyclotomic-liftable-cancellation-pairs-have-no-inverse-defect`. At p=2,
the present construction reduces to those statements. The deliberate
change for odd primes is to retain coefficient occurrences and replace
pairs by ordered p-element blocks with labels, rather than identifying
repeated group labels as if all coefficients were one.

[Mineyev, *The topology and geometry of units and zero-divisors: origami*,
Sections 2.2 and 3.6](https://www.mineyev.web.illinois.edu/art/top-geom-uzd-origami.pdf)
gives the earlier signature method for binary cancellation. The present
proof follows that characteristic-zero lifting idea. The literature search
and independent derivation here establish no claim of historical novelty.
The characteristic-zero theorem used in Section 2 is also recorded as
[Bradford--Fournier-Facio, Theorem 3.4](https://link.springer.com/article/10.1007/s00209-024-03589-3).

For a full positive result by this method one would still need to show
that every BA=1 over every F_p[G] has some permitted choice retaining J,
or handle all choices where J collapses by a different argument. Neither
statement is proved here. Even the characteristic-two repository example
in `central-sign-survival-forces-reverse-cancellation` shows that an
individual matching may collapse J while its inverse is two-sided. Thus
collapse is a necessary test for a counterexample, never sufficient evidence
for one. The known global prime-field reduction makes the unsolved scope
precise; it does not fill it.
