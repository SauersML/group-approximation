---
rg: 2
id: congruence-twist-padding-stable-countermodel-proof
kind: route
title: Twist projective congruence fibers by the Klein representation and bound every monomial carrier
target: congruence-twist-survives-flexible-moving-padding
requires:
  - moving-tail-fixed-traces-keep-quantum-fibers
  - property-t-does-not-kill-boolean-fiber-holonomy
---

## 1. The two congruence factors

Let

~~~text
H=PSL_3(F_2) congruent_to PSL_2(F_7),       |H|=168.     (CTP8)
~~~

Its complex character table has two conjugate irreducible characters of
degree three.  Fix either corresponding unitary representation
`rho:H->U(3)`.  The group `H` is simple.  Every proper subgroup has
index at least seven: an action of smaller degree would be faithful by
simplicity, but `168` divides none of `1!,...,6!`.  Consequently every
orbit of `H` on projective lines in `C^3` has size at least seven.

Let `p` be a sufficiently large prime with

~~~text
p congruent 3 mod 7.                                     (CTP9)
~~~

There are infinitely many such primes by Dirichlet's theorem.  Put

~~~text
G_p=PSL_3(F_p),        N_p=p^2+p+1.                     (CTP10)
~~~

As in the projective-space countermodel, the permutation representation on
`P^2(F_p)` is

~~~text
1 direct_sum xi_p,             dim(xi_p)=N_p-1=p(p+1),  (CTP11)
~~~

with `xi_p` irreducible.

Reduction modulo `2p` is onto
`SL_3(F_2) times SL_3(F_p)`; this follows from Chinese remaindering and
generation of `SL_3` over a finite quotient of `Z` by elementary
matrices.  After taking the projective quotient in the second factor, the
image is `H times G_p`.  Define

~~~text
sigma_p=xi_p tensor rho.                                 (CTP12)
~~~

It is irreducible as an external tensor product, and its inflation to
`Gamma=SL_3(Z)` has dimension `d_p=3(N_p-1)`.

For every fixed nonidentity `g in Gamma`, the projective fixed-point
calculation (MTP5) gives

~~~text
|tr(xi_p(g))|<=1/p
~~~

for all sufficiently large `p`.  Since every normalized character of a
unitary representation has modulus at most one,

~~~text
|tr(sigma_p(g))|
 =|tr(xi_p(g)) tr(rho(g))|
 <=1/p.                                                  (CTP13)
~~~

This proves (CTP2).

## 2. A small-index lemma for the product quotient

We need one standard consequence of Dickson's maximal-subgroup
classification for `PSL_3(F_p)`.

**Small-index lemma.**  For all sufficiently large primes `p`, a proper
subgroup of `G_p` of index less than `7N_p` is contained in a projective
point or line stabilizer.

Indeed the parabolics have index `N_p`.  For prime field there are no
proper subfield subgroups.  The other maximal-subgroup families are the
split-torus and Singer normalizers, the conic stabilizer of order at most a
constant times `p^3`, and bounded exceptional groups.  Since
`|G_p|` has order `p^8`, all these nonparabolic indices have order at
least `p^5`, and hence exceed `7N_p` for large `p`.  This is exactly
the required portion of the Dickson list.

A parabolic has order

~~~text
p^3 (p-1)^2 (p+1)/gcd(3,p-1).                           (CTP14)
~~~

Under (CTP9), none of `p,p-1,p+1` is divisible by seven.  Hence no
parabolic, and no subgroup of a parabolic, has a quotient isomorphic to
`H`.

We now prove that every orbit of `G_p times H` on a projective line in

~~~text
V_p=V_(xi_p) tensor V_rho
~~~

has size at least `7N_p`.  Let `P` be a line stabilizer and let
`A<=G_p`, `B<=H` be its two projections.  Goursat's lemma supplies
normal subgroups `A_0 normal A`, `B_0 normal B` and a common quotient
`Q`, with

~~~text
[G_p times H:P]=[G_p:A][H:B]|Q|.                        (CTP15)
~~~

If `B<H`, then `A<G_p` as well.  Otherwise simplicity and the order
difference force `Q=1`, so `P=G_p times B); the line would then be
invariant under `G_p`, impossible because its action is a sum of three
copies of the nontrivial irreducible `xi_p`.  Therefore

~~~text
[G_p times H:P] >=N_p times 7.                           (CTP16)
~~~

Suppose instead that `B=H`.  Again `A<G_p`.  The common quotient cannot
be trivial, since then `P=A times H` and the line would be invariant under
`H`, while its restriction is a sum of copies of the nontrivial
irreducible `rho`.  Simplicity of `H` gives `Q=H`, so `A` surjects
onto `H`.  If `[G_p:A]<7N_p`, the small-index lemma would put `A`
inside a parabolic, contradicting (CTP14).  Thus (CTP16) holds in this case
as well.

## 3. From projective orbits to monomial carriers

A transitive monomial representation of `Gamma` has the form

~~~text
Ind_L^Gamma(chi)                                         (CTP17)
~~~

for a finite-index subgroup `L` and a one-dimensional character `chi`.
If it contains `sigma_p`, Frobenius reciprocity gives a nonzero vector
line in `V_p` on which `L` acts by `chi`.  Hence `L` is contained in
the projective stabilizer of that line.  Section 2 gives

~~~text
[Gamma:L]>=7N_p.                                         (CTP18)
~~~

Every monomial representation is a direct sum of the transitive line-orbit
representations (CTP17).  Therefore any monomial representation containing
`sigma_p` has total dimension at least `7N_p`.  Since

~~~text
2d_p=6(N_p-1)<7N_p,                                      (CTP19)
~~~

this proves (CTP3).

## 4. Property (T) with arbitrary padding below one fiber

Let `alpha` be any exact representation of dimension `q<=d_p`, put

~~~text
tilde_sigma=sigma_p direct_sum alpha,       n=d_p+q,
~~~

and let `mu` be an exact monomial representation of dimension `n`.
By (CTP18)--(CTP19), `mu` cannot contain `sigma_p`.

On the normalized Hilbert--Schmidt space of maps from
`tilde_sigma` to `mu`, let

~~~text
T_g(A)=mu(g) A tilde_sigma(g)^*.                         (CTP20)
~~~

Every invariant intertwiner vanishes on the `sigma_p` summand.  If
`P_inv` is the orthogonal projection onto invariant vectors and `Z` is
unitary, then

~~~text
||P_inv Z||_2^2<=q/n,
||Z-P_inv Z||_2>=sqrt(d_p/n).                            (CTP21)
~~~

Apply the Kazhdan inequality to `Z-P_inv Z`.  The invariant part has zero
displacement, so

~~~text
max_(s in S)||mu(s)Z-Z tilde_sigma(s)||_2
 >=kappa sqrt(d_p/(d_p+q)).                              (CTP22)
~~~

Unitary multiplication converts (CTP22) to (CTP4).

## 5. Boolean windows, full-corner trace, and global padding

Put `m_p=p` and take the regular Boolean PVM on
`Y_p={-1,+1}^(m_p)`.  Place one copy of `sigma_p` on every atom and let
`Gamma` act trivially on the labels.  This gives exact representations on

~~~text
D_p=2^(m_p)d_p                                          (CTP23)
~~~

dimensions.  Equation (CTP13) and the regular Boolean moments prove
canonical trace convergence for every fixed lamp--actor word.

Let `e_p` be the sum of the atoms with last coordinate `+1`.  Its trace
is `1/2`.  The selected coordinate moves to infinity, so conditioning on
it does not change any fixed Boolean moment.  Thus the normalized
`e_p`-corner also has the canonical pointwise trace.

Now add arbitrary exact padding representations atom by atom.  Write
`q_y` for the added dimension at atom `y` and assume

~~~text
Q_p=sum_y q_y=o(D_p).                                    (CTP24)
~~~

Extend the Boolean label of each padding space by its atom.  An atom is
called bad if `q_y>d_p`.  The number of bad atoms is at most
`Q_p/d_p=o(2^(m_p))`.

On every good atom, (CTP22) applies.  If `delta_(s,y)` is the normalized
fiber error for a gauge and an exact monomial target, then

~~~text
sum_(s in S) delta_(s,y)^2
 >=kappa^2 d_p/(d_p+q_y).                               (CTP25)
~~~

Multiply (CTP25) by the padded atom dimension `d_p+q_y` and sum over the
good atoms in the moving half-corner.  After division by the total padded
corner dimension, (CTP24) gives

~~~text
sum_(s in S)||error_s||_(2,e_p)^2 >=kappa^2-o(1).        (CTP26)
~~~

The largest summand is at least
`kappa^2/|S|-o(1)`, proving (CTP7).  Arbitrary
`o(D_p)` padding changes the corner density and every normalized fixed-word
trace by only `o(1)`, so the full-corner and canonical-trace assertions
survive.

Finally,

~~~text
m_p=log_2(D_p)-log_2(d_p)
   =log_2(D_p)-O(log log D_p),                           (CTP27)
~~~

because `d_p` is quadratic in `p=m_p`.  This is the claimed logarithmic
moving-window scale.

The construction is deliberately not the pinned Kun--Thom action:
`Gamma` fixes every lamp label.  It proves that no theorem using only
fixed-window Boolean exactification, canonical pointwise mixed traces,
property `(T)`, positive-density corner normalization, and sublinear
padding can control the moving fiber.  A successful Kun--Thom theorem must
use additional geometry of its nontrivial coset action.
