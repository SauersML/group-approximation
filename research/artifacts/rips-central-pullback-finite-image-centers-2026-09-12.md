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
