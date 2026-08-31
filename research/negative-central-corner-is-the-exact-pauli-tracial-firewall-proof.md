---
rg: 2
id: negative-central-corner-is-the-exact-pauli-tracial-firewall-proof
kind: route
title: Identify the negative central group-algebra corner with the Pauli Bernoulli crossed product
target: full-shared-pauli-rows-have-an-exact-finite-tracial-model
requires:
  - shared-center-extraspecial-wreath-sector-and-normalizer-proof
  - kun-thom-diagonal-pauli-common-chart-obstruction
---

# The negative central corner is an exact tracial firewall

## 1. The negative central projection has trace one half

The element `J` is a nonidentity central involution of `Pi_X`.  In the
canonical group trace `tau`,

~~~text
tau(J)=0.
~~~

Therefore

~~~text
p_-=(1-J)/2
~~~

is a central projection with `tau(p_-)=1/2`.  The corner
`M_-=p_-L(Pi_X)p_-` is a finite von Neumann algebra with normalized trace

~~~text
tau_-(z)=2 tau(z).                                       (1)
~~~

Its unit is `p_-`.  Since `Jp_-=-p_-`, the central sign is exactly minus
the corner unit.

For a group element `u in Pi_X` write `u_- =p_- lambda(u)`.  Centrality of
`p_-` gives

~~~text
u_- u_-^*=u_-^*u_-=p_-,
~~~

so `u_-` is a unitary of the corner.  Cornering an exact group
representation preserves every multiplication, commutator, covariance, and
actor relation.  Applied to the Pauli generators, this proves (FTC1), and

~~~text
norm_(2,tau_-)(Jp_- - p_-)=norm_(2,tau_-)(-2p_-)=2       (2)
~~~

proves (FTC2).

## 2. Every finite site window is a full matrix factor

Let `E subset X` have `m` elements and let `N_E` be generated in `M_-` by
the pairs `A_x,B_x` for `x in E`.  On the negative corner the relations are

~~~text
A_x B_x=-B_x A_x,
A_x^2=B_x^2=1,
different sites commute.                                 (3)
~~~

The universal complex `*`-algebra for one pair in (3) is `M_2(C)`.  Tensor
independence of different sites gives a surjective unital map

~~~text
tensor_(x in E) M_2(C) -> N_E.                           (4)
~~~

The source is the simple algebra `M_(2^m)(C)`, so the unital map is
injective.  Hence

~~~text
N_E isomorphic to M_(2^m)(C).                            (5)
~~~

The normalized corner trace restricts to the unique normalized matrix trace
on (5).  If `E subset F`, the inclusion `N_E subset N_F` is the standard
tensor inclusion `z -> z tensor 1`.

Taking the increasing union over finite windows and then weak closure gives

~~~text
N={A_x,B_x:x in X}'' isomorphic to tensor_(x in X) M_2(C). (6)
~~~

For countably infinite `X` this is the hyperfinite `II_1` factor `R`.

## 3. The actor gives the Bernoulli crossed product

The cornered actor unitaries satisfy

~~~text
g_- A_x g_-^*=A_(gx),
g_- B_x g_-^*=B_(gx).                                   (7)
~~~

Thus they normalize `N` and implement the tensor-leg action.  The group
normal form in `P_X semidirect G` says that the algebraic span of

~~~text
N_E g_-                (E finite, g in G)
~~~

is weakly dense in `M_-`.  Distinct actor Fourier coefficients are
orthogonal for the canonical trace, exactly as in the reduced crossed
product.  Therefore the map from the algebraic crossed product induced by
(7) extends to a trace-preserving isomorphism

~~~text
M_- isomorphic to R crossed_product G.                   (8)
~~~

If an actor element fixes every site, it acts trivially on `R` but remains
as its group Fourier unitary in (8); this is why the action kernel is not
silently quotiented out.

## 4. Why universal SOS collapse is impossible

A noncommutative sum-of-squares identity in the universal presentation,
together with tracial Cauchy--Schwarz estimates, is valid under every
`*`-representation into every finite tracial von Neumann algebra.  The
corner model above has zero defect in every actor, stabilizer, double-coset,
and Pauli row, while (2) has value two.

Hence no such argument can prove (FTC5).  This includes any attempt to
combine the lifted Kazhdan identity with the full Pauli rows while using only
dimension-free norm inequalities.  The exact finite-dimensional collapse
does not contradict this statement: its final collision step uses
compactness of `U(D) times U(D)` for one fixed `D`.  The infinite tensor
family

~~~text
x -> (A_x,B_x)
~~~

has no repeated or convergent pair in the `L^2` metric of `R`, so that step
fails in (8).

A matrix theorem must therefore detect more than the universal tracial
relations.  Equivalently, it must prove that the exact tracial algebra (8)
does not embed in a tracial matrix ultraproduct for the pinned action.  That
is a Connes-embedding/nonhyperlinearity statement, not a formal consequence
of property (T).  This is the precise finite-dimensional residue left by
the tracial firewall.
