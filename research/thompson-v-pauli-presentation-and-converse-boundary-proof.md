---
rg: 2
id: thompson-v-pauli-presentation-and-converse-boundary-proof
kind: route
title: Use the rational-point stabilizer and the unique off-diagonal orbit to present the Thompson Pauli tape
target: thompson-rational-orbit-shared-center-pauli-host-is-fp
requires:
  - shared-center-pauli-fp-and-spin-divisibility-proof
  - shared-center-extraspecial-wreath-sector-and-normalizer-proof
  - property-t-does-not-kill-boolean-fiber-holonomy
---

# The Thompson rational-orbit Pauli presentation

## 1. Published actor inputs

Let `o` be a rational point of the binary Cantor set and let `X=V.o`.

Three published facts are used.

1. Thompson's `V` is finitely presented; in fact it is of type
   `F_infinity`.
2. `V` acts highly transitively on each of its Cantor-set orbits.  In
   particular its action on the countable infinite set `X` is
   two-transitive.
3. Belk--Hyde--Matucci, Theorem 1, prove that the stabilizer of every finite
   nonempty set of rational points is of type `F_infinity`.  For the
   singleton `{o}` this says

   ~~~text
   H=Stab_V(o) is finitely generated.                         (1)
   ~~~

Two-transitivity says that `H` is transitive on `X minus {o}`.  Therefore
the diagonal action of `V` on `X times X` has exactly two orbits, diagonal
and off-diagonal, and

~~~text
H backslash V/H={H,HtH}                                    (2)
~~~

for any `t` with `to!=o`.

## 2. The finite presentation

Fix `V=<S|R>`, and choose a finite list `T` of words in `S` generating
`H`.  Let `P` be the group presented by (TVP2).

There is an evident surjection

~~~text
P -> E_X semidirect V                                      (3)
~~~

sending `A,B` to the root site pair and fixing `S,J`.  We construct its
inverse.

For `g in V` and `u in {A,B}` define in `P`

~~~text
u_(gH)=g u g^(-1).                                         (4)
~~~

The definition is independent of the representative.  Indeed the relators
for `T` say that `A` and `B` commute with every generator of `H`, hence
with all of `H`.

Conjugating `[A,B]=J` gives the same-site relation at every coset.  It
remains to check a pair of distinct cosets.  If `gH!=kH`, equation (2)
gives

~~~text
g^(-1)k=h_1 t h_2,             h_1,h_2 in H.              (5)
~~~

For `u,v in {A,B}`, conjugate the desired commutator by `g^(-1)`.  The
`h_2` term disappears because `h_2` fixes `v`.  Since `h_1` fixes `u`,
the remaining word is a conjugate by `h_1` of the prototype

~~~text
[u,t v t^(-1)],                                            (6)
~~~

which is a relator of `P`.  Thus all four cross-site commutators hold.
The centrality and actor invariance of `J` follow from the finitely many
relators involving `S,A,B,J`.

Equations (4)--(6) therefore define the infinite Pauli base and its
`V`-action inside `P`.  They give a map

~~~text
E_X semidirect V -> P                                      (7)
~~~

inverse to (3).  Hence `P` is exactly `Pi_V`, proving finite
presentability and the displayed presentation.

## 3. The common sign is nontrivial

Put one copy of `C^2` at each site of `X`.  On the incomplete tensor
product with reference vector `e_0`, let `A_x` and `B_x` be the two Pauli
involutions on tensor leg `x` and let `J=-I`.  Different tensor legs
commute, while on one leg

~~~text
[A_x,B_x]=-I.                                              (8)
~~~

Every permutation of `X` is implemented by tensor-leg permutation and
fixes the reference tensor.  Hence the action of `V` is implemented and
(8) extends to a unitary representation of `Pi_V`.  In particular
`J!=1` in the finitely presented group.

## 4. Every finite-dimensional representation kills the sign

Let `rho:Pi_V->U(d)` be exact and let `K_-` be the negative spectral
subspace of the central involution `rho(J)`.  It is invariant.

Choose any `m` distinct sites.  On `K_-` their `m` Pauli pairs generate

~~~text
M_2(C) tensor ... tensor M_2(C)=M_(2^m)(C).               (9)
~~~

Every finite-dimensional module of this full matrix algebra has dimension
a multiple of `2^m`.  Thus

~~~text
2^m divides dim(K_-)                                      (10)
~~~

for every `m`.  Since `X` is infinite, `m` is arbitrary, so
`dim(K_-)=0`.  This proves `rho(J)=I`.

## 5. What the second Pauli generator does and does not buy

Fix a finite site window `F` of size `m` in a matrix model, round its fixed
finite Pauli group, and restrict to the negative sign sector.  The packet is

~~~text
M_(2^m)(C) tensor I_r.                                    (11)
~~~

Naming both Pauli generators at every site removes the local inner gauge:
an exact actor arrow that permutes `F` has the form

~~~text
P_beta tensor W,                    W in U(r).             (12)
~~~

Thus the two-generator packet is stronger than a Boolean masa on a fixed
window.  But `W` is completely arbitrary, and a positive-density canonical
corner has

~~~text
r approximately D/(2^(m+1)).                              (13)
~~~

Every fixed `m` leaves `r->infinity`.  Extracting one finite action chart
would require compatible choices of (12) over a moving family of windows,
or `m` at least of logarithmic matrix scale.  Pointwise hyperlinear
convergence supplies neither.

This is why the packet does not currently prove the converse (TVP4).

- The subgroup generated by the `A_x` and `V` is the ordinary Boolean
  generalized wreath product.  Hyperlinearity of `Pi_V` only implies
  hyperlinearity of this subgroup, not soficity of its set action.
- The shared-center group is not an ordinary generalized wreath product:
  disjoint finite packets intersect in `<J>`.
- Quotienting by `J` returns two commuting Boolean lamp coordinates, but
  hyperlinearity and soficity are not known to pass through the quotient in
  the direction needed for a converse.
- At matrix level, gluing the two complementary Pauli coordinates over all
  sites is exactly a simultaneous commuting-action/common-chart problem.
  Fixed-window spatialization (12) does not solve that gluing problem.

## 6. Published Connes-embedding boundary

Gao--Kunnawalkam Elayavalli--Patchell, Theorem 3.8, prove the forward
statement

~~~text
H hyperlinear + (H action X) sofic + M Connes embeddable
=> M^(tensor X) crossed_product H Connes embeddable.       (14)
~~~

The negative central corner of the canonical Pauli representation is the
case `M=M_2(C)`, whose infinite tensor closure is the hyperfinite
`II_1` factor.  Thus a sofic Thompson set action would give the expected
Connes-embeddable negative corner.

The converse is not in that theorem.  Their Question 4.2 asks whether
countably many commuting sofic actions have a sofic direct-sum action, and
Question 4.4 asks whether soficity of a generalized wreath product forces
soficity of the underlying set action.  Equations (11)--(13) show the
noncommutative Pauli analogue of the same common-chart seam.  A proof of
(TVP4) would be a new strengthening of those converses, not an application
of (14).

For the transitive action here there is an additional useful warning.
The action is faithful and `V` is simple.  The coset-action theorem of the
same paper says that soficity of `V action V/H` produces a normal
`N<=H` with `V/N` sofic.  Simplicity forces `N=1`.  Hence proving this
specific set action sofic would already prove `V` sofic.

## Sources

- J. Belk, J. Hyde and F. Matucci, *Stabilizers in Higman--Thompson
  groups*, arXiv:2104.05572, Theorem 1.
- A. Le Boudec and N. Matte Bon, *Confined subgroups and high
  transitivity*, Annales Henri Lebesgue 5 (2022), 491--522,
  DOI 10.5802/ahl.128; see also their statement that `V` acts highly
  transitively on its Cantor-set orbits.
- D. Gao, S. Kunnawalkam Elayavalli and G. Patchell, *Soficity for group
  actions on sets and applications*, Research in the Mathematical Sciences
  12 (2025), article 48, Theorem 3.8 and Questions 4.2, 4.4,
  DOI 10.1007/s40687-025-00526-6.
