# Arbitrary BCS predicates are local finite-group corners

Status: exact local construction and exact global gate; not a
nonhyperlinear-group proof.

## 1. Purpose

`FALSE_PERFECT_BCS_IS_NOT_PERFECT_LCS_COMPILER.md` proves that a Boolean
satisfying set can be encoded by scalar group monomials exactly when it is
affine.  That closes direct answer relabeling, but it does not close group
*corners*.  Allowing a projection in the finite group algebra linearizes
every predicate exactly.

This note gives the construction and isolates why the local corners do not
yet glue to a canonical group-factor corner.

## 2. Every predicate is a finite group-algebra corner

Let

```text
D=(C_2)^k=<z_1,...,z_k>
```

and identify its characters with assignments
`a=(a_1,...,a_k) in {+1,-1}^k`.  The minimal Fourier projections are

```text
e_a=2^(-k) product_(j=1)^k (1+a_j z_j) in C[D].
```

They satisfy

```text
e_a^*=e_a=e_a^2,
e_a e_b=0                 (a != b),
sum_a e_a=1,
z_j e_a=a_j e_a.
```

For an arbitrary nonempty satisfying set

```text
R subseteq {+1,-1}^k,
```

put

```text
p_R=sum_(a in R) e_a.
```

Then

```text
p_R C[D] p_R = direct_sum_(a in R) C e_a = C^R,
tau_D(p_R)=|R|/2^k>0.
```

Inside this corner the compressed coordinate elements

```text
Z_j=p_R z_j p_R
```

are commuting self-adjoint involutions relative to the corner unit `p_R`,
and their joint spectrum is exactly `R`.  Every forbidden atom vanishes:

```text
e_a p_R=0                 (a notin R).
```

Thus:

> **Local predicate-corner theorem.**  Every finite Boolean predicate is
> represented exactly, with positive rational canonical trace, in a corner
> of the group algebra of a finite elementary abelian `2`-group.

This construction does not require the predicate to be affine.  The affine
restriction appears only when `p_R` is forbidden and every coordinate must
itself be a scalar group monomial in a full answer group algebra.

## 3. The natural global group

For a BCS with variables `X` and contexts `U_i`, let `Gamma_0` be generated
by involutions `z_x`, `x in X`, with

```text
[z_x,z_y]=1               (x,y in one common context).
```

This is the graph product of copies of `C_2` over the context commutation
graph.  Every clique subgroup

```text
D_i=<z_x:x in U_i>=(C_2)^(U_i)
```

embeds in `Gamma_0`.  Hence every local allowed projection

```text
p_i=p_(R_i) in C[D_i] subseteq C[Gamma_0]
```

exists exactly and has positive canonical trace.

The BCS algebra is obtained by requiring every local allowed projection to
act as the identity, equivalently by killing all forbidden atoms.  A
group-corner realization would therefore need one nonzero projection `p`
such that

```text
p <= p_i                   for every context i,
[p,z_x]=0                  for every variable x.             (BCSC1)
```

The second line is essential.  It makes

```text
z_x |-> p z_x p
```

a unitary representation in the corner.  Without it, compression is only a
completely positive map and does not preserve products.

## 4. Why multiplying the local projections does not work

Local projections belonging to overlapping contexts need not commute in
`C[Gamma_0]`.  Consequently

```text
p_1 p_2 ... p_m
```

is generally not a projection.  The von Neumann meet

```text
p_1 meet ... meet p_m
```

may be zero, need not lie in the algebraic group ring, and still need not
commute with the variable generators.  Alternating-projection limits repair
none of these three issues.

If `p in L(Gamma_0)` satisfies the commutation conditions in `(BCSC1)`, and
the variables generate `Gamma_0`, then `p` is central in `L(Gamma_0)`.  In
the usual ICC cases this forces `p=0` or `p=1`; the latter can satisfy
`p<=p_i` only for tautological local predicates.  Thus the regular group
factor of the bare context group has no nontrivial reducing predicate
corner.

Putting all context groups in a direct product makes the local projections
commute, but it also makes all variables commute globally.  The resulting
algebra is classical and loses the contextual/non-Connes-embeddable
behavior.  This is the local-corner version of the same gluing obstruction.

## 5. The surviving Hecke-corner theorem

Let `B` be one of the finitely presented synchronous BCS algebras supplied
by the negative solution to Connes embedding: `B` has a tracial state but no
Connes-embeddable tracial state.  This formulation is recorded explicitly by
Paddock--Slofstra in
[Satisfiability problems and algebras of boolean constraint system games](https://arxiv.org/abs/2310.07901).
An unconditional nonhyperlinear group would follow from the following
concrete construction.

> **Canonical Hecke-corner target.**  Construct a finitely presented group
> `Gamma`, a finite subgroup `K<=Gamma`, and elements
>
> ```text
> V_x in p_K C[Gamma] p_K,
> p_K=|K|^(-1) sum_(k in K) k,
> ```
>
> such that:
>
> 1. the `V_x` are self-adjoint involutions with the BCS context
>    commutation and forbidden-atom relations;
> 2. they generate a trace-preserving copy of the chosen BCS algebra in
>    `p_K L(Gamma) p_K`; and
> 3. the normalized corner trace restricts to one of its non-CE traces.

If `Gamma` were hyperlinear, `L(Gamma)` and its positive trace
`1/|K|` corner would be Connes embeddable.  Every trace-preserving von
Neumann subalgebra generated by the `V_x` would then be Connes embeddable,
contradicting item 3.  Therefore `Gamma` would be nonhyperlinear.

This target is different from asking that `p_K g p_K` be a representation
of `Gamma`: Hecke operators are allowed.  It is also stronger than merely
mapping the BCS algebra into a quotient of the corner.  Connes embeddability
passes to von Neumann subalgebras, not backward through arbitrary quotients.

## 6. A finite graph of finite groups cannot supply the gluing

One natural attempt is to realize the local finite groups and their overlaps
as the vertex and edge groups of a finite graph of groups, then take its
Bass--Serre fundamental group.  This entire class is too small.

A fundamental group of a finite graph of finite groups is virtually free.
It is therefore residually finite, sofic, and hyperlinear.  Its group von
Neumann algebra and every positive finite-subgroup Hecke corner are Connes
embeddable.  Such a corner cannot contain a trace-preserving copy of the
chosen non-CE BCS algebra.

Hence the local construction cannot be completed by ordinary one-dimensional
Bass--Serre gluing of finite gadgets.  A successful realization must use at
least one of:

1. genuinely higher-dimensional compatibility relations, such as a
   developable complex of groups;
2. an infinite vertex/coefficient group together with a separately proved
   canonical-trace theorem; or
3. non-group Hecke data followed by a new groupification theorem.

The first option is the one closest to the existing Steinberg/Leavitt atlas:
multiplication and two-dimensional holonomy, rather than a tree of finite
pieces, must carry the non-CE information.

## 7. Relation to the phase-safe toric route

The phase-safe toric theorem uses a central finite-character projection and
keeps the game generators as genuine group unitaries.  The Hecke route uses
a noncentral finite-subgroup projection and allows the BCS variables to be
double-coset operators.

```text
phase-safe toric route:
    group words are easy; arbitrary predicates are hard.

Hecke-corner route:
    arbitrary local predicates are easy; compatible global gluing is hard.
```

The two routes meet at one precise requirement: a positive canonical group
trace corner must carry the non-CE BCS trace *as a subalgebra*, not merely as
a vector-state quotient.

## 8. Audited endpoint

The local affine obstruction is not the end of the game-groupification
program.  Every predicate already has an exact finite group-algebra corner.
What remains is a finite presentation of one global Hecke corner that
simultaneously:

1. identifies shared variables across contexts;
2. preserves the noncommuting contextual structure;
3. retains a positive canonical group trace; and
4. embeds, rather than quotients onto, the non-CE tracial algebra.

Any proposed graph-of-groups or finite-groupoid compiler should be audited
against these four requirements before it is treated as progress toward a
nonhyperlinear group.
