---
rg: 2
id: free-label-word-traces-and-the-direct-product-cancellation-proof
kind: route
title: Compute the free-label word trace and the canceling-label group
target: free-label-haarization-restates-the-group-factor-gate
requires:
  - perfect-qc-separation-yields-finite-bcs-with-no-matrix-model
  - finite-phase-pauli-dilation-is-twisted-group-factor-compiler
  - unrestricted-algebraic-envelope-equals-nonhyperlinearity
---

# Universal free labels lose the source trace

Fix a finite tracial von Neumann algebra `(M,tau)` and unitaries
`u_1,...,u_n`.  Write `A=W^*(u_1,...,u_n)`.  In
`M tensor L(F_n)` let

~~~text
v_i=u_i tensor lambda(s_i),
b_i=1 tensor lambda(s_i),                                (1)
~~~

where the `s_i` freely generate `F_n`.

## 1. Every nontrivial labeled word has trace zero

Let

~~~text
w=s_(i_1)^(epsilon_1) ... s_(i_k)^(epsilon_k)
~~~

be a reduced nonempty word in `F_n`, with
`epsilon_j in {1,-1}`.  Substitution in (1) gives

~~~text
w(v)
 =u_(i_1)^(epsilon_1) ... u_(i_k)^(epsilon_k)
      tensor lambda(w).                                  (2)
~~~

The second tensor factor has canonical trace zero because `w!=1`.
Consequently

~~~text
(tau tensor tau_F)(w(v))=0                               (3)
~~~

for every nonidentity reduced word, while the empty word has trace one.
These are exactly the joint star-moments of the canonical free generators.

Define on the group algebra

~~~text
T:C[F_n] -> M tensor L(F_n),
T(lambda(s_i))=v_i.                                      (4)
~~~

Equation (3) says that `T` preserves the canonical trace.  In particular,
for every `x in C[F_n]`,

~~~text
||T(x)||_2^2
 =(tau tensor tau_F)(T(x)^*T(x))
 =tau_F(x^*x)
 =||x||_2^2.                                             (5)
~~~

Thus `T` has no algebraic kernel.  Its GNS extension is a unitary from
`L^2(L(F_n))` onto the `L^2` closure of `T(C[F_n])` and intertwines left
multiplication.  It therefore implements a trace-preserving normal
star-isomorphism

~~~text
L(F_n) -> W^*(v_1,...,v_n).                              (6)
~~~

Nothing in (3)--(6) depends on the moments or relations of the original
`u_i`.  This is the precise erasure statement.

## 2. Canceling labels give a direct product, not a new group model

The extra generators satisfy

~~~text
v_i b_i^*=u_i tensor 1.                                  (7)
~~~

Hence `W^*(v_i,b_i)` contains `A tensor 1` and
`1 tensor L(F_n)`.  The reverse inclusion follows from (1), so

~~~text
W^*(v_1,...,v_n,b_1,...,b_n)=A tensor L(F_n).             (8)
~~~

Let

~~~text
H=<u_1,...,u_n> subset U(A),
Gamma=<v_1,...,v_n,b_1,...,b_n>
      subset U(A tensor L(F_n)).
~~~

Equation (7) puts `H tensor {1}` inside `Gamma`, while the `b_i` put
`{1} tensor F_n` inside `Gamma`.  These two subgroups commute.  Conversely
each generator in (1) belongs to their product.  Therefore

~~~text
Gamma=(H tensor {1})({1} tensor F_n)
     isomorphic to H times F_n.                           (9)
~~~

The product map is injective.  Indeed,
`h tensor lambda(s)=1` forces `lambda(s)` to be scalar.  A left-regular
group unitary is scalar only for `s=1`, after which `h=1`.

## 3. Exact criterion for the ambient trace to be canonical

Under (9), the restriction of the ambient trace is

~~~text
phi(h,s)
 =(tau tensor tau_F)(h tensor lambda(s))
 =tau(h) delta_(s,1).                                    (10)
~~~

The canonical trace on the abstract group `H times F_n` is

~~~text
tau_can(h,s)=delta_(h,1) delta_(s,1).                    (11)
~~~

Comparing (10) and (11) proves

~~~text
phi=tau_can on Gamma
 iff tau(h)=0 for all h in H minus {1}.                  (12)
~~~

There is no hidden weaker condition coming from mixed words.  Any word in
the `v_i,b_i` is an element `h tensor lambda(s)`.  A surviving trace
requires cancellation of its free label, and its remaining coefficient is
exactly `tau(h)`.  Conversely every `h in H` occurs with canceled label,
because each `u_i tensor 1` is the word `v_i b_i^*`.

## 4. The criterion is the original group-factor gate

Assume the right side of (12).  The actual inclusion `H subset U(A)`
defines on `C[H]` a star-homomorphism

~~~text
S:C[H] -> A,    S(lambda(h))=h.                          (13)
~~~

For a finitely supported sum `x=sum_h c_h lambda(h)`,
condition (12) gives

~~~text
||S(x)||_(2,tau)^2=sum_h |c_h|^2=||x||_(2,tau_can)^2.    (14)
~~~

The GNS extension of `S` is therefore a trace-preserving normal injective
star-homomorphism `L(H)->A`.  Its range is `W^*(H)=A` because the `u_i`
generate `A`.  Thus

~~~text
A isomorphic to L(H) trace preservingly.                 (15)
~~~

Conversely, the canonical group trace in any trace-preserving
identification (15) vanishes on every nonidentity element of `H`, so it
implies (12).  Hence (12) and (15) are equivalent.

This also shows exactly why merely viewing `Gamma` as an abstract group
cannot transfer non-Connes-embeddability.  When (12) fails, the
representation of `Gamma` in (8) carries a noncanonical character.  The
canonical group von Neumann algebra is

~~~text
L(Gamma)=L(H) tensor L(F_n),                             (16)
~~~

whereas the algebra generated in the proposed construction is

~~~text
A tensor L(F_n).                                         (17)
~~~

There is no trace-preserving identification between (16) and (17)
provided by the labeled generators.

## 5. Consequence for the finite SynchBCS source

Choose a tracial state on the finite SynchBCS algebra from
`perfect-qc-separation-yields-finite-bcs-with-no-matrix-model`
and let `A` be its GNS von Neumann algebra.  It is non-CE.  Its finite
projection generating set can be replaced by finitely many generating
symmetries, so the calculation above applies.

- Using only the `v_i` produces `L(F_n)` by (6).  Since free groups are
  hyperlinear, this target is CE and has forgotten the non-CE source.
- Adding the `b_i` recovers `A tensor L(F_n)` by (8), but gives the
  canonical group trace only if `A` is already `L(H)` by (12)--(15).
- In that exceptional case `H` is nonhyperlinear, since its group factor
  is the non-CE algebra `A`.  The desired group has already been found
  before the free labels are added.

Therefore free labels are a universal Haarization device but not a
source-specific group compiler.  Canceling them recovers the source
multiplication at exactly the price of reinstating the original canonical
trace problem.  Any successful Pauli or groupoid dilation must add
structure which forces (12); the tensor-label trick alone cannot do so.
