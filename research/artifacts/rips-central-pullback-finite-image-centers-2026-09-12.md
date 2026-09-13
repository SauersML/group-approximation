# Rips pullbacks: a fixed-prime finite-quotient-center criterion

Date: 2026-09-12. This develops a different construction route into
`non-residually-finite-hyperbolic-group` and
`persistent-degree-two-class-on-hyperbolic-group`. The pullback theorem and
the fixed-prime equivalence below are proved. An explicit hyperbolic input
satisfying the new finite-image hypothesis has not been obtained.

## The elementary pullback theorem

Suppose there are exact sequences

```text
1 -> A -> E -> Q -> 1,
1 -> N -> G -> Q -> 1,
```

where `A` is finite and central in `E`. Suppose that `z in A` has prime
order `p` and belongs to the finite residual `R_f(E)`. Let

```text
P = E x_Q G = {(e,g) in E x G : e and g have the same image in Q}.
```

Then `P -> G` is a surjection with central kernel `A`, and `P -> E` is a
surjection with kernel `N`, embedded as `{(1,n): n in N}`. The element
`z_P=(z,1)` has order `p` in `P`.

Assume the following property of `N`:

```text
For every homomorphism rho:N -> F to a finite group,
the center Z(rho(N)) contains no element of order p.                 (C_p)
```

Then `z_P in R_f(P)`, so `P` is not residually finite. If `G` is
word-hyperbolic, `P` is word-hyperbolic too, because it has finite kernel
over `G`.

**Proof.** Let `phi:P -> F` have finite image. Replace `F` with that image,
so `phi` is onto, and set `J=phi(N)`. The subgroup `J` is normal in `F`.
The induced map `P -> F/J` kills `N`, hence factors through
`P/N=E`. Since `z in R_f(E)`, it follows that `phi(z_P) in J`. The element
`z_P` is central in `P`, so `phi(z_P)` belongs to `Z(J)`. Its order divides
`p`. Property `(C_p)` implies `phi(z_P)=1`. This holds for every finite
image, and `z_P` has order exactly `p`, completing the proof.

The argument does not require `Q` or `E` to have no finite quotients. It
uses only the specified invisible central element. It also does not require
`G` to be residually finite, `N` to have property (T), or any approximation
property.

Property `(C_p)` passes to quotients: a finite quotient of a quotient of
`H` is a finite quotient of `H`. Thus it is enough to arrange `(C_p)` for
a prescribed group `H` of which `N` is a quotient.

## Fixing the central extension once and for all

Take `Q=Sp_4(Z)`, a finitely presented arithmetic group. Let

```text
1 -> <t> = Z -> E_infinity -> Q -> 1
```

be the inverse image of `Sp_4(Z)` in the universal covering group of
`Sp_4(R)`. Deligne proved that every finite-index subgroup of `E_infinity`
contains `<t^2>`. Consequently, for each prime `p`, the quotient

```text
E_p = E_infinity / <t^(2p)>
```

is a central extension of `Q` by `C_(2p)`, and the image `z=t^2` has
order exactly `p` and belongs to `R_f(E_p)`. This also works for `p=2`:
the central kernel is `C_4` and the invisible mark is its square.

Primary source: Pierre Deligne, *Extensions centrales non résiduellement
finies de groupes arithmétiques*, C. R. Acad. Sci. Paris **287** (1978),
203--208. The needed statement is in the opening paragraph and its English
summary on p. 203; read directly from the
[IAS author PDF](https://publications.ias.edu/sites/default/files/35_ExtensionsCentrales.pdf)
on 2026-09-12. Only the containment of `<t^2>` in the finite residual is
needed, not equality with the whole residual.

## The Rips construction and the resulting equivalence

Let `H` be any non-elementary word-hyperbolic group satisfying `(C_p)`.
The Belegradek--Osin Rips theorem supplies

```text
1 -> N -> G -> Sp_4(Z) -> 1
```

with `G` word-hyperbolic and `N` a quotient of `H`. Thus `N` satisfies
`(C_p)`. Applying the pullback theorem to `E_p` gives a word-hyperbolic
group `P` with a specified nonidentity central order-`p` element in its
finite residual. It is therefore not virtually torsion-free either.

Primary source: I. Belegradek and D. Osin, *Rips construction and Kazhdan
property (T)*, Groups Geom. Dyn. **2** (2008), 1--12,
[DOI 10.4171/GGD/29](https://ems.press/journals/ggd/articles/1580),
[arXiv:math/0605553](https://arxiv.org/pdf/math/0605553), Corollary 1.2,
p. 1, checked 2026-09-12. It is the ordinary-hyperbolic specialization of
their Theorem 1.1.

It follows that, **for each fixed prime `p`**, the following are equivalent:

1. Some word-hyperbolic group is not residually finite.
2. Some non-elementary word-hyperbolic group `H` satisfies `(C_p)`.

The direction `(2) -> (1)` was proved above. For `(1) -> (2)`, the
Kapovich--Wise equivalence already established in the repository produces
an infinite word-hyperbolic group without nontrivial finite quotients. It
is non-elementary, since elementary groups are residually finite, and its
only finite image is the trivial group, which satisfies `(C_p)` for every
prime.

This equivalence does not exhibit an `H`. It makes the required finite
quotient restriction more specific than the previous Rips target
`rips-kernel-without-finite-quotients`: arbitrary nontrivial finite images,
including images whose orders are divisible by `p`, are allowed, provided
their centers contain no order-`p` element. For example, finite centerless
groups satisfy this restriction even when `p` divides their order.

## The cohomological version and the role of property (T)

For any finite-index `G_0<=G`, write `N_0=N intersect G_0` and
`Q_0=image(G_0 -> Q)`. The low-degree inflation--restriction sequence for
trivial `C_p` coefficients contains

```text
H^1(N_0;C_p)^(Q_0) -> H^2(Q_0;C_p) -> H^2(G_0;C_p).
```

Thus a persistent class on `Q` remains persistent after pulling back to
`G` if its restriction to every `Q_0` avoids the displayed transgression
image. In particular, it suffices that all the spaces
`H^1(N_0;C_p)^(Q_0)` vanish. Requiring every finite-index subgroup of `N`
to have vanishing `H^1(-;C_p)` is stronger. That latter condition is
equivalent to every finite quotient of `N` having order prime to `p`:
one direction follows by taking the normal core of a finite-index subgroup
mapping onto `C_p`; for the other, the preimage of a Sylow `p` subgroup of
a finite quotient maps onto a nontrivial finite `p` group and then onto
`C_p`.

Choosing the Rips input `H` with property (T) ensures that `N` and every
finite-index `N_0` have property (T). Their abelianizations are finite.
This implies `H^1(N_0;Z)=0`, giving injectivity

```text
H^2(Q_0;Z) -> H^2(G_0;Z)
```

for every finite-index pair. It does **not** imply
`H^1(N_0;C_p)=0`: a finite abelianization may have `p`-torsion. Nor does
injectivity over `Z` make the image primitive. Reduction modulo `p` can
vanish when an integral class becomes divisible by `p` after inflation.
Hence integral persistence does not by itself close the finite-central
extension argument.

The elementary finite-image-center condition `(C_p)` can prove survival
of the chosen mark without proving vanishing of every transgression space.
No input `H` with this condition was produced by the present investigation.

## An exact invariant-character formulation

For an arbitrary group `H`, property `(C_p)` is equivalent to

```text
H^1(L;F_p)^H = 0 for every finite-index normal subgroup L of H.     (I_p)
```

Here `H` acts by conjugation, and the coefficient action on `F_p` is
trivial. This does not require finite generation or property (T).

**Proof.** Suppose a nonzero invariant character `chi:L -> F_p`
exists. Its kernel `K` is normal in `H`, since `chi` is invariant, and
`K` has finite index in `H`. Invariance says `[H,L] <= K`; hence
`L/K`, which has order `p`, lies in the center of the finite quotient
`H/K`. Conversely, if a finite quotient `H/K` has a central subgroup
`C` of order `p`, its preimage `L` is a finite-index normal subgroup of
`H`. The quotient map `L -> L/K=C` is a nonzero `H`-invariant
character. These implications prove the equivalence.

Consequently, the desired input may have nonzero mod-`p` first
cohomology in finite covers. What must vanish is the part fixed by the
full group when the covering subgroup is normal. Equivalently, no
finite quotient may have a central chief factor of order `p` at its
bottom. This formulation identifies the exact finite-cover vanishing
statement needed; property (T), which only gives finite integral
abelianizations, does not prove it.

## Candidate families checked against the exact requirement

Kassabov--Nikolov frame groups supply finitely generated residually
finite groups whose profinite completion is a Cartesian product of
finite nonabelian simple groups. Such a completion has only finite
products of nonabelian simple groups as continuous finite quotients,
so these groups satisfy `(C_p)` for every prime. However, their
Definition 7 requires the frame group to contain the full direct sum of
the finite simple factors. In the infinite families in their theorem,
these finite subgroups have unbounded orders. A hyperbolic group has a
uniform bound on orders of finite subgroups, so none of these frames is
a hyperbolic input. Nor can passing to finite index repair this: if
`H_0` has index `d` and `S` is a finite subgroup, then
`[S:S intersect H_0] <= d`, and the resulting finite subgroups of
`H_0` still have unbounded orders.

Primary source: M. Kassabov and N. Nikolov, *Cartesian products as
profinite completions*,
[arXiv:math/0602446](https://arxiv.org/pdf/math/0602446), Theorems 2
and 4 and Definition 7, pp. 2--3, checked 2026-09-12. The exclusion of
hyperbolicity and the finite-index argument above are deductions here.
A dense hyperbolic subgroup of such a profinite product, if one were
constructed, would still need a proof that its **full** profinite
completion is the prescribed product. Density alone does not exclude
additional finite quotients.

M. Aka's profinitely isomorphic property-(T) and non-property-(T)
arithmetic examples do not remove this missing input. Theorem 1 and
its proof realize both groups as lattices in products of two noncompact
real Lie groups. They are not lattices in a single negatively curved
rank-one symmetric space. Primary source: *Profinite completions and
Kazhdan's property (T)*,
[arXiv:1005.4566](https://arxiv.org/pdf/1005.4566), Theorem 1 and
Section 3, checked 2026-09-12.

For quaternionic hyperbolic lattices, no theorem proving `(C_p)` for
one fixed prime was recovered. The known congruence completion alone
controls congruence quotients; applying its finite-center restrictions
to every finite quotient needs an additional argument. The centrality
theorems in the congruence-subgroup literature impose higher total
local rank, so the phrase "rank one" in their isotropic case must not
be mistaken for a theorem about a lattice in `Sp(n,1)`. For example,
T. N. Venkataramana's *Centrality*,
[arXiv:2108.09006](https://arxiv.org/pdf/2108.09006), Theorem 1,
assumes rational rank at least one **and real rank at least
two**. The latter hypothesis excludes the intended quaternionic
hyperbolic application. These checks do not prove that a weaker
fixed-prime center bound is impossible; they leave that bound as a
specific unresolved target.

## Central-cover equations for a finite presentation

Write `H=<x_1,...,x_d | r_1,...,r_m>` and fix a finite quotient
`theta:H -> F`, with `f_i=theta(x_i)`. A normalized cocycle
`alpha:F x F -> F_p` defines the central extension `E_alpha` with
multiplication

```text
(a,f)(b,g) = (a+b+alpha(f,g),fg).
```

Let `A_j(alpha)` be the central coordinate obtained by evaluating
`r_j` in the elements `(0,f_i)`. This is a linear function of `alpha`.
More explicitly, walk along the relator with prefixes `v_0=1,v_1,...`
in `F`. A positive letter `x_i` contributes `alpha(v_(k-1),f_i)`;
a negative letter contributes

```text
alpha(v_(k-1),f_i^(-1)) - alpha(f_i^(-1),f_i).
```

If `e_ji` is the exponent sum of `x_i` in `r_j`, then a lift of
`theta` to `E_alpha` exists exactly when the following finite linear
system has a solution `u=(u_1,...,u_d)`:

```text
sum_i e_ji u_i = -A_j(alpha)  for j=1,...,m.                       (L)
```

The images of the generators in that lift are `(u_i,f_i)`.
The other finite linear equations are the cocycle equations

```text
alpha(f,g)+alpha(fg,h)=alpha(g,h)+alpha(f,gh),
alpha(1,f)=alpha(f,1)=0.
```

Coboundaries have the form
`alpha(f,g)=b(f)+b(g)-b(fg)`. Thus these equations describe the exact
obstruction for a specified finite quotient; they are not a bounded
search over all finite quotients.

If `H^1(H;F_p)=0`, the low-degree sequence gives

```text
H^1(ker(theta);F_p)^H
  = ker[ H^2(F;F_p) -> H^2(H;F_p) ].                              (T)
```

Consequently, with this hypothesis, `(C_p)` is equivalent to saying
that for every finite quotient `F`, any cocycle for which `(L)` is
solvable is a coboundary. This is an exact finite-presentation target
for a uniform argument.

## Coprime triangle stabilizers give lifting, not center exclusion

Suppose `H` is the colimit of a simple triangle of finite vertex groups
`V_1,V_2,V_3`, with their edge groups identified, and that `p` divides
none of the orders `|V_i|`. Then

```text
H^1(H;F_p)=H^2(H;F_p)=0.                                        (A)
```

Here is a direct proof, which does not assume any spectral theorem.
For a finite group `V` of order prime to `p`, a normalized cocycle
`alpha` is the coboundary of

```text
b(g) = |V|^(-1) sum_(h in V) alpha(g,h).
```

This follows by summing the cocycle identity over its third variable.
It proves that every central `C_p` extension of `V` splits. The
splitting is unique, because two splittings differ by a homomorphism
`V -> C_p`, and no such nonzero homomorphism exists.
Now take a central `C_p` extension of `H`. Pull it back to each `V_i`.
The unique local splittings agree on every edge group, because those
groups also have order prime to `p`. By the colimit presentation they
define a splitting on `H`. This proves `H^2(H;F_p)=0`. The same
colimit presentation shows that every homomorphism `H -> C_p`
vanishes on the generating vertex groups, proving `H^1(H;F_p)=0`.

For every finite quotient `theta:H -> F`, (T) therefore specializes to
the isomorphism

```text
H^1(ker(theta);F_p)^H  ~=  H^2(F;F_p).                            (U)
```

Moreover, every nonsplit central `C_p` extension `E -> F` is itself
a finite quotient of `H`. Indeed, (A) produces a lift `H -> E`.
Its image surjects onto `F`. If it met the kernel `C_p` trivially, it
would give a splitting `F -> E`, a contradiction. It therefore
contains `C_p` and is all of `E`.

Thus a local coprime-order certificate automatically solves the
lifting equations for **every** finite-group cocycle, including any
nontrivial ones. It does not exclude those cocycles. For these triangle
groups the required uniform statement is exactly

```text
H^2(F;F_p)=0 for every finite quotient F of H.                     (Q)
```

For perfect finite `F`, this says that the Schur multiplier of `F`
has no `p`-torsion. Looking only at the centers of currently known
simple quotients can miss this obstruction: a centerless simple
quotient with a nonzero `p`-part in its multiplier forces a further
quotient with central `p`-torsion.

## A concrete remaining candidate: H_31 at p=7

Use the following explicit group of Caprace--Conder--Kaluba--Witzel:

```text
H_31 = <a,b,c |
  a^5, b^5, c^5, [a,c], [b,c,b], [b,c,c,b], [b,c,c,c],
  a b a^2 b a^2 b a b^(-1) a b^(-1),
  b^2 a b a^(-1) b a^(-1) b a b^2 a,
  (b a b^(-1) a b a^(-1))^2 >.
```

Their Theorem 1.2 proves that this group is infinite, hyperbolic, and
has property (T). Its triangle vertex groups are `PSL_2(31)`,
`C_5 x C_5`, and a Sylow `5` subgroup of `Sp_4(5)`.
Their orders are respectively `14880`, `25`, and `625`, all coprime
to `7`. Therefore (A)--(U) apply with `p=7`.
The abelianization is `C_5`: the local perfect subgroup
`<a,b>=PSL_2(31)` kills `a,b` in the abelianization, and sending
`a,b` to `1` and `c` to a generator of `C_5` respects every relator.

This supplies a concrete candidate for the input of the Deligne--Rips
construction. Its precise remaining condition is

```text
H^2(F;F_7)=0 for every finite quotient F of H_31.                  (H31)
```

For this presentation, the first three rows of the exponent-sum
matrix are `5 I_3`. In characteristic `7`, equations (L) uniquely
determine the three generator corrections from the power relators.
The coprime triangle argument proves that all remaining lift equations
then hold for any finite quotient and any cocycle. Hence solving those
local equations, even exactly, cannot certify (H31); one must show
that the finite-quotient cocycle is a coboundary. No proof of (H31) has
been obtained here.

Primary source for the presentation, triangle groups, and geometric
properties: P.-E. Caprace, M. Conder, M. Kaluba, S. Witzel,
*Hyperbolic generalized triangle groups, property (T) and finite simple
quotients*,
[arXiv:2011.09276](https://arxiv.org/pdf/2011.09276), Theorem 1.2,
pp. 2--3. The cohomology and central-lifting deductions above are
proved here.

## The first retraction kernel has a complete local certificate

Setting `c=1` defines a retraction

```text
pi:H_31 -> Q=PSL_2(31),
```

whose section is the vertex group `<a,b>`. Its kernel `K` is the
normal closure of `c`: after killing `c`, precisely the presentation
of the vertex group `<a,b>` remains. In particular, `K` is generated
by conjugates of an element of order `5`; its abelianization has
exponent `5`.

There is a stronger geometric certificate. Let `X` be the contractible
triangle complex in the cited construction. The quotient `K\X` is
the cone on the bipartite coset graph with vertex sets
`Q/<a>` and `Q/<b>` and edge set `Q`.
Indeed, there is one vertex of `<a,b>` type, which is the cone apex;
the other two vertex types are these two coset spaces. The edges of
`a` and `b` type are the radial edges, the edges of `c` type are
indexed by `Q`, and the triangles are indexed by `Q`, each joining
one such base edge to the apex. Thus `K\X` is contractible.

For comparison, its numbers of vertices, edges and faces are

```text
1+2976+2976 = 5953,
2976+2976+14880 = 20832,
14880,
```

giving Euler characteristic `1`. The `K` stabilizers of vertices
have orders `1`, `125`, and `5`, respectively. Its only nontrivial
edge stabilizers have order `5`, and face stabilizers are trivial.
For every prime `p!=5`, the higher cohomology of these stabilizers
with `F_p` coefficients vanishes by averaging. The equivariant
cohomology spectral sequence for the contractible complex therefore
has only its row of degree zero, which is the cochain complex of
`K\X`. It follows that

```text
H^j(K;F_p)=0 for every j>0 and every prime p!=5.                  (K)
```

In particular, for every `F_7[Q]`-module `V` inflated along `pi`,
the kernel `K` acts trivially and has vanishing higher cohomology
with coefficients in `V`. Since `7` does not divide `|Q|`, the
Hochschild--Serre sequence then gives

```text
H^j(H_31;V)=0 for every j>0.                                    (V)
```

This rules out an initial extension of the quotient `Q` by a
nontrivial elementary abelian `7` group as a quotient of `H_31`
over `pi`. Such an extension splits by coprimality. Lifts of `pi`
to the resulting semidirect product differ by a cocycle with
coefficients in that elementary abelian group; (V) makes every
such lift conjugate to the complement, so none is surjective.

This certificate does not apply to every deeper normal cover.
If a further finite quotient has a nontrivial image of `c`, its
kernel need not contain the order-`5` vertex or edge stabilizers
used above, and its quotient complex need not be a cone.
In particular, exclusion of `7`-parts in the multipliers of
finite **simple** quotients would not establish (H31): arbitrary
finite quotients and their possible solvable radicals remain in
the quantifier.

## A concrete obstruction to using only the usual link criterion

The Kac--Moody--Steinberg examples in the same paper provide a direct
test of a proposed certificate based only on property-(T) link
expansion and vertex-group orders coprime to the target prime.
For an odd defining prime `r>=7`, their hyperbolic KMS examples have
finite `r`-group vertex stabilizers and satisfy the stated link-based
criterion for property (T). Corollary 7.10 gives quotients
`SL_3(F_(r^e))` for every `e>=3`.
Choose `r!=3` and even `e>=4`. Then `r^e=1 mod 3`, so the scalar
matrices with scalar of order `3` form a central `C_3` in this finite
quotient. Thus `(C_3)` fails, although all vertex-group orders are
coprime to `3` and the link criterion holds.

This is not a proof that no more specific finite certificate can
work. It disproves the inference from those particular local
hypotheses. The usual real spectral-gap estimate proves vanishing
over characteristic zero; it gives no estimate ruling out the
invariant `F_3` characters just exhibited. A new certificate for
(H31) would have to control finite-quotient central cocycles beyond
the local splitting and real spectral information.

## Other attempted transfers

The existing compression examples do not supply a mark for this pullback
construction. In any homomorphism to a word-hyperbolic group, an image of
a property-(T) subgroup is either finite or non-elementary. In the finite
case, a conjugation inclusion into itself is equality. In the non-elementary
case, its centralizer is finite, and conjugation compression also forces
equality of the two centralizers. This is the established
`hyperbolic-compression-centralizer-rigidity` argument. Thus the associated
compression commutator witnesses are killed in every hyperbolic image.
Passing those same marked words through fillings or marked limits does not
preserve a nonidentity witness.

The present construction is aimed at residual finiteness and virtual
torsion-freeness. A central element invisible in finite images need not be
invisible in arbitrary operator-norm matrix approximations. Consequently
this theorem supplies no unproved passage from the first three existence
questions to the non-MF question.
