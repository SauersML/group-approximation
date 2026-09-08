# Local decoder defects and generic Cantor fibers

Research derivation, 2026-09-07. **Gottschalk's conjecture remains open in
this work.** The theorems below are proved in ordinary mathematics. They
are not Lean-verified and no external priority claim is made.

## 1. Statement and conventions

Let G be a group and A,B finite nonempty alphabets. Give their full shifts
the product topology. Write (h.x)(g)=x(h^{-1}g). A cellular map with memory
M reads x on gM to produce its value at g. Products of finite subsets below
are ordered group products; commutativity is never assumed.

Suppose cellular maps

    tau : B^G -> A^G,    sigma : A^G -> B^G

satisfy sigma tau=id. Thus tau is a section of sigma. Put R=tau sigma.
Choose memories N for tau and M for sigma containing the identity e, and
put K=NM. Then R has memory K and

    R^2=R,    sigma R=sigma,    image(R)=image(tau).

Two configurations are asymptotic if they differ at finitely many sites.
A map is pre-injective if it identifies no distinct asymptotic pair.

**Theorem.**

1. If R is not the identity, sigma has a distinct asymptotic collision
   u,v. Both configurations can be chosen equal to a constant fixed point
   of R outside KK^{-1}, with v=R(u).
2. Consequently a cellular map with a cellular section is pre-injective
   if and only if it is bijective. This assertion allows different input
   and output alphabets.
3. If G is infinite and R is not the identity, there are a finite set W,
   a pattern p in B^W, and pairwise disjoint translates h_i W (i>=1)
   with the following property. Whenever z contains p on infinitely many
   of these translates, sigma^{-1}(z) contains a closed subspace
   homeomorphic to {0,1}^N.
4. The preceding set of z is a dense G_delta and has measure one for
   every Bernoulli product measure on B^G whose one-site distribution
   gives positive weight to every symbol. Every z with dense G-orbit also
   has a Cantor subset in its fiber, without needing to use the same
   predetermined translates.

For countably infinite G, a fiber containing this Cantor set has exactly
continuum cardinality, since A^G has at most that cardinality. For arbitrary
infinite G only the lower bound and the Cantor embedding are asserted.

The square-alphabet case is the application to Gottschalk. The rectangular
case is useful both for the proof and as a nonvacuous test family.

## 2. A local reverse error produces a finite collision

Take a constant configuration b_* in B^G and set c=tau(b_*). Equivariance
makes c constant, and R(c)=c. If R is nontrivial, equivariance supplies a
configuration x with R(x)(e) != x(e). Define u to agree with x on K and
with c off K. Since e belongs to K and R has memory K,

    R(u)(e)=R(x)(e) != x(e)=u(e).

Set v=R(u). We have sigma(v)=sigma(u). Locality and R(c)=c imply

    supp(u,c) subset K,
    supp(v,c) subset KK^{-1}.

Indeed v(g) can differ from c(g) only if gK meets K; writing gm=k gives
g=km^{-1}. Since e is in K, both supports are contained in KK^{-1}.
Thus u != v is the asserted finite collision. Notice that this uses a
fixed point supplied by the section, not an assumed quiescent symbol for
an arbitrary cellular map.

If sigma is pre-injective, this forces R=id. Together with sigma tau=id
it makes tau and sigma mutually inverse. Conversely a bijection is
pre-injective. Also sigma is bijective exactly when R=id: a bijective
sigma has a unique section, its inverse. This proves parts 1 and 2.

For a nontrivial idempotent cellular endomorphism the same argument, using
any constant point in its image, shows directly that it is not
pre-injective. This elementary idempotent fact is not a solution of
surjunctivity: it concerns the decoder's failure of pre-injectivity, not
the encoder, which is already injective.

## 3. A finite output guard licenses a local alternative

Let u,v be the pair just constructed, and now use its exact nonempty
difference set

    D={g : u(g) != v(g)} subset KK^{-1}.

In particular e belongs to D. Set

    H=D M^{-1} M,    W=H N,    z_0=sigma(u)=sigma(v),
    p=z_0 restricted to W.

Because e belongs to M and N, W contains H, D M^{-1}, and D.
If z agrees with z_0 on W, its preferred preimage y=tau(z) agrees with
v=tau(z_0) on H. Form y' by replacing y on D with u on D, and leave all
other coordinates unchanged. Then

    sigma(y')=sigma(y)=z.                                      (1)

To check (1), an affected output coordinate g must belong to D M^{-1}.
Its entire read window gM lies in H. On gM the patched configuration
equals u: on D this is the replacement, and on H\D we use y=v=u.
The original read window equals v. Since sigma(u)=sigma(v), the two
outputs agree at g. All other read windows miss D and are unchanged.

This is a local argument on an arbitrary background. Merely knowing
sigma(u)=sigma(v) would not license insertion into arbitrary preimages:
the guard z|W=p and the section y=tau(z) supply exactly the required
collar. Omitting that collar is an invalid shortcut.

By equivariance the construction applies at a translate h whenever
z(hk)=p(k) for all k in W. Its replacement set is hD and its affected
output set is hD M^{-1}.

## 4. Independent alternatives in one fiber

For infinite G choose h_1,h_2,... with h_i W pairwise disjoint. At each
stage the forbidden choices of h belong to the finite union of previous
h_j W W^{-1}, so the recursion continues. No amenability, metric growth,
sofic approximation, or finite generation is used.

Fix z and let I={i : z(h_i k)=p(k) for every k in W}. Starting from
y=tau(z), independently perform or omit the replacement from Section 3
at each h_i D, i in I. Disjointness of h_i W implies disjointness of
the affected output sets h_i D M^{-1}. In particular no read window of
sigma meets two replacement sets. The local verification of (1) therefore
holds for every output coordinate, even with infinitely many replacements.

We have obtained a map

    F_z : {0,1}^I -> sigma^{-1}(z).

Each output coordinate of F_z depends on at most one choice bit, so F_z
is continuous in the product topology. The two possible values at h_i
are u(e) and v(e), which differ. Hence F_z is injective. Compactness of
the source and the Hausdorff property of A^G make it a homeomorphism
onto a closed subset. When I is infinite, enumerate it to identify the
source with {0,1}^N. If I has n elements this also gives 2^n distinct
preimages with independently readable finite changes.

This proves part 3. It does not assert that the entire fiber is perfect
or homeomorphic to a Cantor set.

## 5. Generic outputs and transitive outputs

For the fixed sequence above write U_i={z : z|h_i W is the translate of p}.
Each U_i is a nonempty clopen cylinder. The set

    Omega = intersection_{n>=1} union_{i>=n} U_i

is a G_delta. Each tail union is dense: a cylinder prescribed on finitely
many coordinates meets only finitely many of the disjoint h_i W, so one
can prescribe p on an unused translate. Density of the intersection
follows from the Baire theorem for compact Hausdorff spaces; alternatively
one can insert p on infinitely many unused translates while respecting
any given finite cylinder.

Under a full-support Bernoulli product distribution lambda^G, the events
U_i are independent with the same probability

    rho = product_{k in W} lambda(p(k)) > 0.

For each n, the probability of no success among i=n,...,n+m-1 is
(1-rho)^m, tending to zero. A countable union over n shows
lambda^G(Omega)=1. For the first n prescribed locations, the number of
licensed alternatives has the exact Binomial(n,rho) distribution, and
their independent choices give at least 2 to that power preimages.

Now let z have dense orbit. It contains arbitrarily many disjoint
occurrences of p: choose any n pairwise disjoint translates of W,
prescribe p on all of them, and use orbit density to realize that entire
finite pattern in z. If a maximal family of disjoint occurrences were
finite, every other occurrence would intersect its finite union. Each
fixed site lies in at most |W| translates hW, so there would be only
finitely many occurrences in total. This contradicts the arbitrarily
large families. Thus there is an infinite disjoint family, to which
Section 4 applies. This proves part 4.

For a countable group, transitive full-shift configurations exist. One
can enumerate its finitely supported patterns and insert them on disjoint
translates recursively. For a singleton alphabet this is immediate.

## 6. An exact criterion for the unresolved positive goal

For any injective CA tau:A^G -> A^G, compactness gives a cellular decoder
sigma with sigma tau=id: the inverse on the closed image is continuous,
its identity-coordinate rule has finite memory, and that rule extends
arbitrarily on the finite patterns absent from the image. The extension
is still a cellular map. It is not automatically an inverse off the image.

For an infinite countable G and any such decoder, the following are
equivalent:

* tau is surjective;
* sigma is pre-injective;
* sigma is bijective;
* sigma has a countable fiber over at least one transitive configuration.

The first three equivalences follow from the split identities and
Section 2. In the bijective case every fiber is a singleton, and
transitive configurations exist. In the nonbijective case Section 5
excludes a countable fiber over any transitive point.

Consequently Gottschalk's conjecture is equivalent to the following
condition: over every finitely generated infinite group, every injective
finite-alphabet CA admits a cellular decoder with a countable fiber over
some transitive configuration. This is a reduction, not an established
universal countability theorem.

For completeness this restriction to finitely generated groups loses
nothing. If a CA over G has memory M, take H=<M>. Each left coset of H
evolves independently by the same CA on A^H. Injectivity on A^G implies
injectivity on A^H by extending a hypothetical collision to the other
cosets identically. Surjectivity on A^H implies surjectivity on A^G by
choosing a preimage on each coset. Finite H is settled by counting the
finite set A^H. Apply the proposed countable-fiber condition only to the
remaining finitely generated infinite H.

## 7. Attempts to turn the dichotomy into a contradiction

**Finite counting needs a volume comparison.** The construction produces
2^n distinct decoder preimages. Their supports occupy n disjoint bounded
regions. A full shift has exponentially many configurations on those
regions too. Without another upper bound, these two facts agree. A
finite collision of a surjective CA is not itself impossible on a
nonamenable group.

**Cardinality does not imply conditional entropy for the section measure.**
Let G be infinite, B={0,1}, A=B x {0,1}, sigma(a,b)=a, and tau(z)=(z,0).
These are cellular maps with sigma tau=id and nontrivial R. Every fiber
is a full binary shift. Nevertheless for nu=tau_*(lambda^G), sigma is
one-to-one on a set of nu-measure one and its conditional measure on
each fiber is the point mass at tau(z). Thus an inference from uncountable
fibers to positive conditional entropy of this chosen measure is false.
This example has unequal alphabets, so it does not refute Gottschalk or
settle the square-alphabet obstruction. It identifies the invalid measure
inference, which otherwise does not use alphabet equality at all.

**An output guard is not a shift-equivariant extra full alphabet.** The
extra bits can be stored only where the finite guard occurs. The packing
centers in the proof are chosen externally, not by a cellular rule. The
argument does not supply an equivariant injection of a larger full shift
into a smaller one. Such an injection would already fail on constant
configurations. Ignoring the guards or the choice of centers is unsound.

**Choosing a different local decoder has not repaired the gap.** If tau
is strict, the theorem applies to every extension of its inverse, whatever
larger finite memory is chosen. No construction here produces the desired
countable fiber. Requiring it universally would settle the original
conjecture and must remain an open prerequisite.

## 8. Relation to existing work and evidence

The split-epimorphism and generalized-inverse terminology is standard;
see Ville Salo, [*On von Neumann regularity of cellular automata*](https://arxiv.org/html/2209.13373v1),
Section 3. Its full-shift extension observation is the familiar decoder
construction used above. The proof here treats arbitrary groups, permits
different finite alphabets, and spells out the output guard and generic
fiber packing. No claim is made that these elementary consequences are
previously unpublished.

Capobianco, Kari, and Taati,
[*Post-surjectivity and balancedness of cellular automata over groups*](https://dmtcs.episciences.org/3918),
prove that pre-injective, post-surjective CA are reversible. Their
post-surjectivity condition lifts finite changes near every preimage.
A section gives a preferred preimage; the present argument does not
silently assume their stronger lifting condition at arbitrary preimages.

Seward's [*Krieger's finite generator theorem for actions of countable
groups II*](https://arxiv.org/abs/1501.03367) gives a conditional route from
positive Rokhlin entropy assumptions to surjunctivity. No such universal
entropy assumption is proved or imported here.

The separate dependency-free replay exercises the finite collision,
ordered memory sets, guarded replacement, and simultaneous choices on a
nonlinear rectangular split pair over the noncommutative free group F_2.
It also checks that dropping the guard causes an explicit failure.
Those are exact finite computations on finitely supported configurations
of an infinite group, not simulations on a finite quotient. The proof
above supplies the infinite packing, Baire, and probability assertions.
