---
rg: 2
id: leavitt-corner-bcs-support-coefficient-gate-proof
kind: route
title: Restrict to the support subgroup, push along a congruence representation, and apply Malcev or the canonical trace
target: leavitt-corner-bcs-support-coefficient-gate
requires:
  - lin-explicit-fixed-bcs-gap-via-generic-conversion
  - paddock-slofstra-bcs-forbidden-projection-dictionary
  - nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
  - finitely-generated-linear-groups-are-residually-finite
---

Notation as in `(CG1)`--`(CG3)`.

## Step 0. What the fixed BCS forbids

By `lin-explicit-fixed-bcs-gap-via-generic-conversion`,
`omega_q^s(B_loop)<=1-delta_loop`.  Quantum-approximable strategies are
limits of finite-dimensional ones, so also `omega_qa^s(B_loop)<1`.
By `paddock-slofstra-bcs-forbidden-projection-dictionary`, unital star
homomorphisms `A(B_loop)->R^U` are perfect quantum-approximable strategies.
Hence `A(B_loop)` has no Connes-embeddable tracial state (the GNS algebra of
such a state embeds in `R^U`), and in particular no nonzero
finite-dimensional star representation (its normalized trace would be
Connes-embeddable; equivalently it is a perfect finite-dimensional strategy).

## Step 1. The diagram lives on the support subgroup

Let `Gamma_X=<X,z> <= Delta`.  Then `P_z` and every `A_x=Phi(x)` lie in
`C[Gamma_X]`, which is a unital star subalgebra of `C[Delta]` (group-basis
inclusion; products of group elements of `Gamma_X` stay in `Gamma_X`).
All BCS relations are identities between elements of `C[Gamma_X]`, and they
hold in `C[Delta]`, hence in `C[Gamma_X]`.  So `Phi` corestricts to a unital
star homomorphism `A(B_loop)->P_z C[Gamma_X] P_z`.

## Step 2. Hyperlinear shadow gate

Let `h:Gamma_X->Lambda` be a group homomorphism into a hyperlinear group
and suppose `h(z)!=1`.  Replace `Lambda` by `h(Gamma_X)`, which is countable
(finitely generated) and hyperlinear (subgroups of hyperlinear groups are
hyperlinear).  Since `z^2=x_13(2q)=1`, `h(z)` has order exactly two and
`Pbar=(1-h(z))/2` is a nonzero projection in `C[Lambda]`.  The linear
extension `h_*:C[Gamma_X]->C[Lambda]` is a unital star homomorphism with
`h_*(P_z)=Pbar`, so

```text
h_* o Phi : A(B_loop) -> Pbar C[Lambda] Pbar                 (P1)
```

is unital.  By `nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear`
and Step 0, `Lambda` is not hyperlinear, a contradiction.  Hence `h(z)=1`
for every such `h`.  This proves the general form and consequence 3.

## Step 3. The coefficient gate

Every element of `pi(Gamma_X)` is a product of the matrices `pi(g)^(+-1)`,
`g in X`, and `pi(z)=I+qE_13`; all these have entries in `S_X`.  So
`pi(Gamma_X) <= GL_20(S_X)`.  Let `rho:S_X->M_k(K)` be a unital ring
homomorphism with `rho(q)!=0`.  Applying `rho` entrywise gives a group
homomorphism

```text
rho_*:GL_20(S_X)->GL_(20k)(K),   rho_*(pi(z))=I+E_13 (x) rho(q) != I.   (P2)
```

`h=rho_* o pi` maps `Gamma_X` onto a finitely generated subgroup of
`GL_(20k)(K)`, which is residually finite by
`finitely-generated-linear-groups-are-residually-finite`, hence has a finite
quotient `theta` with `theta(h(z))!=1`.  Finite groups are hyperlinear, so
Step 2 applied to `theta o h` gives a contradiction.  (Equivalently and
without the trace lemma: `C[F]` for the finite group `F` is a
finite-dimensional C*-algebra and `(P1)` is a nonzero finite-dimensional
star representation of `A(B_loop)`, forbidden by Step 0.)  Therefore
`rho(q)=0` for every such `rho`, which is `(CG3)`.

## Step 4. The listed classes

*Finite-dimensional or commutative `S_X`.*  A finite-dimensional algebra
acts faithfully on itself by left multiplication, giving `rho` with
`rho(q)=q!=0` (`q!=0` since `t_1qs_1=1`).  A commutative `S_X` has a prime
ideal `p` not containing the nonzero idempotent `q` (an idempotent lying in
every prime ideal is nilpotent, hence zero); `S_X/p` embeds in its fraction
field `K`, giving `rho:S_X->K` with `rho(q)!=0`.

*PI `S_X`.*  A nonzero idempotent never lies in the Jacobson radical
`J=J(S_X)` (if `q in J` then `1-q` is a unit, and `(1-q)q=0` forces `q=0`).
`J` is the intersection of the primitive ideals, so some primitive ideal `P`
does not contain `q`.  `S_X/P` is a primitive PI ring; by Kaplansky's
theorem on primitive PI rings (I. Kaplansky, *Rings with a polynomial
identity*, Bull. Amer. Math. Soc. 54 (1948) 575--580: "a primitive ring
satisfying a polynomial identity is a simple algebra finite-dimensional over
its center") it is a central simple algebra, finite-dimensional over its
center `Z`.  Extending scalars to an algebraic closure `Kbar` of `Z` gives an
injective unital map `S_X/P -> M_n(Kbar)`, whose composite with the quotient
is a `rho` with `rho(q)!=0`.  This covers the degree-zero core (locally
matricial over `F_2`, so every finitely generated subalgebra is
finite-dimensional) and bounded-prefix degree-zero inventories.  The nested
spin reservoir is covered by consequence 3 instead: there `Gamma_X` is a
finite extraspecial group, and `h` may be the identity.

*One-sided Toeplitz range algebra.*  If `S_X <= F_2<s_1,t_1> <= R`, the
universal property of `F_2<s,t | ts=1>` gives a unital homomorphism from
the abstract Toeplitz algebra `T=F_2<s,t|ts=1>` onto `F_2`, `s,t |-> 1`.
It remains to see that `T -> F_2<s_1,t_1> <= R` is injective, so that the
character lives on the subalgebra of `R`.  Rewriting `ts -> 1` is confluent,
so `s^a t^b` is a basis of `T`.  Put `e=1-st` and `e_(ij)=s^i e t^j`; from
`te=0=es` one gets `e t^i e_(kl) = delta_(ik) e_(0l)` and
`e_(0l) s^j e = delta_(lj) e`.  Let `f=sum c_(ab) s^a t^b` be a nonzero
kernel element.  If its symbol `sum_(a-b=k) c_(ab)` vanishes for all `k`,
then `f` is a nonzero combination of the `e_(ij)`
(`s^a t^b - s^(a+1) t^(b+1) = e_(ab)`), and compressing gives `e` in the
kernel, i.e. `s_1t_1=1` in `R`; then `s_2t_2=0` and
`1=(t_2s_2)(t_2s_2)=t_2(s_2t_2)s_2=0`, absurd.  Otherwise, for `m` large,
`t^m f s^m = sum_k d_k u_k` with `u_k=s^k` (`k>=0`), `u_k=t^(-k)` (`k<0`)
and some `d_k!=0`; multiplying on the right by `s^N` gives a nonzero
polynomial `p` with `p(s_1)=0` in `R`.  But `R` acts on the `F_2`-space with
basis the sequences in `{1,2}^N` ending in `2^infinity`, by `s_i x=ix`,
`t_i(jx)=delta_(ij)x` (this satisfies the Leavitt relations), and
`p(s_1)2^infinity=sum_k p_k 1^k2^infinity !=0`, absurd.  So the character
exists on `F_2<s_1,t_1>` and restricts to `S_X` with `q=s_1t_1 |-> 1`.

*Sharpness.*  In any unital fd representation, `t_2s_2=1` implies
`s_2t_2=1` (finite-dimensional algebras are directly finite), so
`q=1-s_2t_2 |-> 0`; thus `q in Rad_rep(S)` whenever `s_2,t_2 in S`.
Also `r |-> s_1 r t_1` is an isomorphism `R -> qRq` with unit `q`, and `R`
has no nonzero fd representation (direct finiteness would give
`1=s_1t_1+s_2t_2=1+1=0`), so every unital fd representation of
`qRq+F_2(1-q)` kills `q`.  These pass the gate.
