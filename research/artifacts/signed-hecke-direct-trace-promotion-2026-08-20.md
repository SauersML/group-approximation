# Direct trace promotion through signed Hecke corners

Date: 2026-08-20

## Outcome

This pass does **not** construct a non-hyperlinear group. It does shorten the
signed-Hecke route to one exact algebraic construction problem.

Let `B` be a finite BCS whose universal BCS algebra `A(B)` has a tracial state
but has no Connes-embeddable tracial state, as supplied by
`mipstar-bcs-tracial-nonru-exists`. It is enough to construct a finitely
presented group `Gamma`, a nonzero algebraic projection `q in C[Gamma]`, and a
unital star homomorphism

```text
Phi : A(B) -> q C[Gamma] q.                                (1)
```

If (1) exists, then `Gamma` is non-hyperlinear. Injectivity of `Phi`,
surjectivity onto the corner, uniqueness of a corner trace, and an
approximate-representation decoder are all unnecessary.

For signed Hecke corners one may take `q=z_rho`, the central idempotent of a
nontrivial irreducible representation of a finite subgroup. The augmentation
then vanishes, so the corner has no scalar group character. Every individual
Boolean predicate admits an exact finite-dimensional block of this kind. The
only remaining gate is to put all context blocks in one algebraic group corner
so that their projections have identical marginals on shared variables.

This gate is recorded as
`signed-hecke-compatible-projection-atlas-for-nonce-bcs`.

## 1. Exact corner trace-promotion theorem

Let `Gamma` be a discrete group and let `tau_Gamma` be the canonical trace on
its group von Neumann algebra `L(Gamma)`. Let `q in C[Gamma]` be a nonzero
projection. Faithfulness of `tau_Gamma` gives

```text
tau_Gamma(q)>0.
```

The normalized corner trace is

```text
tau_q(x)=tau_Gamma(x)/tau_Gamma(q),    x in qL(Gamma)q.     (2)
```

### Theorem

Suppose a unital star algebra `B` has no Connes-embeddable tracial state. If
there is a unital star homomorphism

```text
Phi : B -> q C[Gamma] q,                                  (3)
```

then `Gamma` is non-hyperlinear.

### Proof

Assume for contradiction that `Gamma` is hyperlinear. Then its canonical
tracial von Neumann algebra embeds trace-preservingly into a tracial
ultraproduct of matrix algebras (equivalently into `R^omega`). Compressing by
the image of `q` gives a trace-preserving embedding of the normalized finite
corner

```text
(qL(Gamma)q,tau_q).
```

Pull back the corner trace:

```text
sigma=tau_q o Phi.                                        (4)
```

Because `Phi` is unital into a corner with unit `q`, `sigma(1)=tau_q(q)=1`.
Positivity and traciality follow from (2). Thus `sigma` is a tracial state on
`B`.

The trace `tau_q` is faithful on `qL(Gamma)q`. Consequently the GNS von
Neumann algebra of `(B,sigma)` is naturally the von Neumann algebra generated
by the image,

```text
pi_sigma(B)'' ~= W*(Phi(B)) subset qL(Gamma)q.             (5)
```

Indeed, the GNS null ideal is exactly the inverse image under `Phi` of the
`L^2(tau_q)` null ideal, and faithfulness makes the latter zero on the image.
Restrict the corner embedding to the subalgebra in (5). This proves that
`sigma` is Connes embeddable, contradicting the hypothesis on `B`. Therefore
`Gamma` is not hyperlinear. QED.

The proof is wired as
`nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear`, with proof
route `algebraic-corner-trace-promotion-proof`.

### Direction matters

The established theorem uses a map

```text
non-CE algebra -> canonical positive group corner.
```

This is different from `unique-trace-signed-corner-quotient-forces-nonhyperlinear`,
which asks for a quotient

```text
group corner -> prescribed unique-trace algebra.
```

For a quotient, one must know that the canonical corner trace descends and
becomes the desired trace. For (3), the canonical positive corner trace is
simply pulled back. This reversal removes the trace-classification problem.

## 2. The augmentation gate

Let `epsilon:C[Gamma]->C` be the augmentation character and let `q` be a
projection. Then

```text
epsilon(q)^2=epsilon(q)=conjugate(epsilon(q)),
```

so `epsilon(q)` is either zero or one.

If `epsilon(q)=1`, the restriction

```text
epsilon : qC[Gamma]q -> C
```

is a unital star character, because the unit of the corner is `q`. Therefore
any unital homomorphism `B->qC[Gamma]q` pulls this character back to a
character of `B`. A characterless nonclassical BCS algebra cannot enter such
a corner.

In particular, the subgroup average

```text
p_K=|K|^{-1} sum_(k in K) k
```

always has augmentation one and is the wrong corner. This is formalized by
`augmentation-one-corner-retains-a-character`.

## 3. Finite-type signed corners remove all scalar characters

Let `K<=Gamma` be finite, let `rho` be an irreducible complex representation
of `K`, and put

```text
z_rho=(d_rho/|K|) sum_(k in K) chi_rho(k^{-1}) k.          (6)
```

This is the central projection onto the `rho`-isotypic block of `C[K]`. If
`rho` is nontrivial, character orthogonality gives

```text
epsilon(z_rho)
 = (d_rho/|K|) sum_k chi_rho(k^{-1})
 = 0.                                                      (7)
```

More generally, any one-dimensional group character `lambda` restricts to an
irreducible character of `K`, and

```text
lambda(z_rho)=0
```

whenever `d_rho>1`. Thus a higher-dimensional finite-type corner kills every
scalar group character, not only augmentation. Its canonical trace is

```text
tau_Gamma(z_rho)=d_rho^2/|K|>0.                            (8)
```

These facts are wired as
`nontrivial-finite-type-corner-kills-scalar-characters`.

## 4. Every Boolean predicate has a local character-free block

Fix a nonempty relation `R subset {+1,-1}^U`.

If `|R|>=2`, act on `H_R=C^R` with basis `(e_a)_(a in R)`. Let

```text
X_x e_a = a_x e_a,       x in U.                          (9)
```

Let `K_R` be the finite group generated by all coordinate-sign diagonal
matrices and all permutation matrices of the basis. Its tautological
representation `rho_R` is irreducible: the coordinate-sign projections give
the diagonal matrix units, and conjugating them by permutations gives all
matrix units. Hence `C[K_R] z_(rho_R) ~= End(H_R)` and `d_(rho_R)=|R|>1`.
The joint spectral projections of (9) are

```text
p_a=|e_a><e_a|,    a in R,                                (10)
```

so the joint spectrum is exactly the satisfying set `R`.

If `R={a}` is a singleton, use `K_R=C_2 x S_3` and the tensor product of the
required sign character of `C_2` with the two-dimensional standard
representation of `S_3`. Each variable acts by the scalar `a_x` in this
irreducible two-dimensional block. Again the joint spectrum is exactly `R`
and the block has no scalar group character.

Thus every context separately has an exact algebraic satisfying-assignment
partition in a higher-dimensional finite-type corner. This is
`every-boolean-predicate-has-a-character-free-finite-type-block`.

Local predicate realization is therefore solved. It does not solve overlap
compatibility between different contexts.

### One common finite type suffices locally

The local construction can be normalized further.  If `D` is twice the least
common multiple of the cardinalities `|R_c|`, every context uses the same
hyperoctahedral group `(C_2)^D semidirect S_D` and its same tautological
irreducible type.  Repeating each allowed assignment `D/|R_c|` times gives the
required joint spectrum.  The corner unit has `D` explicit rank-one algebraic
atoms and the same positive canonical trace for every context copy.  This is
`all-bcs-contexts-share-one-hyperoctahedral-signed-type`.

There is also a sharp limitation.  If piecewise transports place every
context partition back inside the one finite root algebra `M_D(C)`, the atlas
itself is a finite-dimensional BCS representation and its normalized trace is
Connes embeddable.  Hence that construction is impossible for the chosen BCS.
The context copies must be differently embedded finite-dimensional
subalgebras of the infinite signed corner, not merely different bases of the
root block.  This is
`root-block-piecewise-transport-cannot-host-nonce-bcs`.

## 5. BCS models are compatible projection atlases

Let `B` be a Boolean constraint system. For each context `c` with allowed
assignments `R_c`, suppose a unital star algebra `A` with unit `q` contains
projections

```text
p_(c,a),    a in R_c,                                     (11)
```

such that

```text
p_(c,a)p_(c,b)=0                     for a!=b,             (BPA1)
sum_(a in R_c) p_(c,a)=q,                                  (BPA2)
sum_(a in R_c) a_x p_(c,a)
  = sum_(b in R_d) b_x p_(d,b)       whenever x in c cap d.(BPA3)
```

Define the common signed marginal

```text
X_x=sum_(a in R_c) a_x p_(c,a).                           (12)
```

Equation (BPA3) makes this independent of the chosen context. Within a
context the `X_x` commute and square to `q`; the joint spectral atom for an
assignment `a` is exactly `p_(c,a)`. Forbidden atoms vanish because no such
projection occurs in (11). Therefore (12) defines a unital star homomorphism

```text
A(B) -> A.                                                 (13)
```

Conversely, from a unital homomorphism (13), take the joint spectral
projections of the commuting involutions belonging to each context. The BCS
relations kill the forbidden atoms, and functional calculus gives
(BPA1)--(BPA3).

Hence (11)--(BPA3) are equivalent to a unital BCS-algebra model. This is
`bcs-corner-model-is-a-compatible-projection-atlas`.

For the direct trace-promotion theorem, take `A=qC[Gamma]q`. The open problem
is now concrete: build finitely many algebraic projections satisfying these
three equations.

## 6. Exact piecewise group transport

Single compressed group elements need not be unitaries in a corner. The
correct exact replacement is piecewise transport.

Let `p_1,...,p_n` and `r_1,...,r_n` be two orthogonal partitions of a corner
unit `q`, and suppose group elements `g_i` satisfy

```text
g_i p_i g_i^{-1}=r_i.                                     (14)
```

Put

```text
v_i=g_i p_i=r_i g_i,       V=sum_i v_i.                   (15)
```

The initial and range projections are

```text
v_i* v_j=delta_(ij) p_i,    v_i v_j*=delta_(ij) r_i.      (16)
```

Indeed, for `i!=j`, insert the orthogonal range projections `r_i r_j=0` in
`v_i* v_j`, and insert the orthogonal source projections `p_i p_j=0` in
`v_i v_j*`. Summing (16) gives

```text
V*V=VV*=q.                                                 (17)
```

Thus `V` is a corner unitary assembled from finitely many group translates.
If an involution `s` of the indices satisfies

```text
p_(s(i))=r_i,       g_(s(i))=g_i^{-1},                    (18)
```

then `v_(s(i))=v_i*`, so `V=V*` and `V^2=q`.

The smallest nontrivial example is

```text
q=p_0+p_1,   g p_0 g^{-1}=p_1,
V=g p_0 + g^{-1} p_1.                                    (19)
```

Then `V` is a self-adjoint corner unitary exchanging the two pieces.

This is wired as `piecewise-group-transport-gives-corner-unitaries`.
It supplies the correct transport syntax for a signed-Hecke compiler, but it
does not by itself choose compatible context partitions.

## 7. The exact remaining gate

Fix the finite no-CE-trace BCS `B`. Construct:

1. a finitely presented group `Gamma`;
2. a finite subgroup `K<=Gamma`;
3. an irreducible `rho in Irr(K)` with `dim(rho)>1`;
4. algebraic projections `p_(c,a) in z_rho C[Gamma] z_rho`;

such that (BPA1)--(BPA3) hold.

The local blocks in Section 4 solve (BPA1)--(BPA2) context by context. The
entire obstruction is (BPA3): copies of the same Boolean variable in different
contexts must define exactly the same signed marginal in one corner.

Ordinary free products leave these marginals independent. Straight
Bass--Serre amalgamation over scalar or diagonal subgroups does not create the
required finite holonomy. A single compressed group element usually has the
wrong source and range projections. Piecewise transports (15) can repair the
last defect if one constructs a finite transport quiver whose cycles enforce
all overlap identities without collapsing a context partition.

This precise construction problem is
`signed-hecke-compatible-projection-atlas-for-nonce-bcs`; the route
`nonhyperlinear-via-signed-hecke-projection-atlas` now reaches the root from
that one gate using only established claims.

## 8. Falsification and next computation

The next useful finite computation should not search for scalar phase gadgets.
It should encode the fixed BCS incidence hypergraph and search for a finite
projection-transport quiver with:

```text
- one orthogonal partition for every context;
- a labelled signed marginal for every context-variable incidence;
- piecewise group arrows pairing equal marginals across overlaps;
- cycle holonomy preserving every source projection;
- one common higher-dimensional finite-type corner.
```

A candidate fails immediately if augmentation survives, if a cycle identifies
two distinct atoms in one context, or if the overlap equations imply a scalar
character. A positive candidate must output explicit finite group words and
finite group-ring formulas, after which all atlas equations are exact symbolic
identities.

The mathematical status is therefore sharp: direct trace promotion is proved;
local character-free predicate blocks are proved; exact piecewise transport is
proved; the global compatible projection atlas remains open.
