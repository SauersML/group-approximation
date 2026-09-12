# Conservative syndrome updates: verified consequences and the remaining gap

This records an explored alternative in which data and verification syndromes
move jointly, while the number of nonzero symbols is conserved. The argument
below does not prove Gottschalk's conjecture, construct a strict embedding,
or establish surjunctivity of all conservative cellular automata. No novelty
claim is made.

Update later on 2026-09-07: the higher-particle gap in this exploratory
argument has been closed by the separate
[collision-algebra proof](../cluster-hall-matching-and-collision-transpose-proof.md).
Its theorem proves surjectivity from conservation and injectivity on
finite configurations over arbitrary groups. The still stronger
[positive-charge nonincrease theorem](../finite-injective-charge-noncreation-forces-surjectivity.md)
allows general finite alphabets and positive real charges. The original
expectation and two-particle arguments below remain valid, but their
unresolved higher-sector status is historical.

Let G be any group. Write 0 for the all-zero binary configuration, and let
tau:{0,1}^G->{0,1}^G be a cellular automaton with tau(0)=0. Assume that
for every finitely supported binary configuration x,

    sum_(g in G) tau(x)(g) = sum_(g in G) x(g).         (C1)

Both sums are finite because tau has finite memory and fixes 0. Injectivity
is not required in the first result. All polynomial coefficients below are
ordinary integers or rational numbers, not coefficients in F_2.

## Conservation implies a conserved expectation for every invariant measure

Choose a finite memory M containing the identity and write the origin rule
as its unique multilinear Boolean polynomial over Q:

    f(x)=sum_(S subset M) c_S m_S(x),
    m_S(x)=product_(s in S) x(s).

Here c_empty=0. Put h(x)=f(x)-x(1_G), and denote its coefficients by d_S.
The empty coefficient is again zero. For each finite nonempty T subset G
define its setwise translation stabilizer

    H_T={g in G : gT=T}.

This stabilizer is finite: fixing t_0 in T, the map g->g t_0 embeds H_T
into the finite set T. In particular its positive integer order is
nonzero in Q.

Fix a finite set D subset G and restrict x to configurations supported in
D. The expression

    H_D(x)=sum_(g in G) h(g^(-1).x)

is a finite multilinear polynomial in the coordinates indexed by D. To
see finiteness directly, a nonempty monomial indexed by S can contribute
only when gS is contained in D, and fixing one element of S leaves only
finitely many possible g. By (C1), H_D vanishes at every point of
{0,1}^D. Boolean Mobius inversion, equivalently uniqueness of multilinear
representation, says that each coefficient is zero.

For a nonempty T subset D its coefficient is

    sum_(nonempty S subset M) d_S |{g : gS=T}|
      = |H_T| sum_(S subset M, S in G.T) d_S.         (C2)

Indeed, the set of translators is empty unless S and T are in the same
translation orbit; otherwise it has size |H_T|. Taking D=T in the
preceding vanishing identity and dividing by |H_T| proves

    sum_(S subset M, S in O) d_S=0                    (C3)

for every orbit O of finite nonempty subsets. Thus the corresponding
orbit sums for f vanish except on the singleton orbit, where their sum
is 1. The finite stabilizer factor in (C2) is necessary when G has torsion.

Now let mu be any G-invariant Borel probability measure on {0,1}^G. The
expectation of m_S is the same for all S in a translation orbit. Grouping
the finitely many coefficients of h by their orbits and using (C3) gives

    integral h dmu=0,
    integral tau(x)(1_G) dmu(x)=integral x(1_G) dmu(x). (C4)

In particular, if the input has independent Bernoulli(t) coordinates,
the output has one-site marginal t for every t in [0,1]. More explicitly,
the expectation of m_S under this input is t^|S|, so (C3) reduces the
expectation of f to t. Equivariance makes every pushforward tau_*^n(mu)
G-invariant, and (C4) therefore also preserves this expectation under
iteration.

This is a statement about one observable. It does not say that
tau_*(mu)=mu, that output coordinates are independent, or that tau is
surjective. In particular, preserved Bernoulli marginal density cannot be
substituted for preservation of the whole Bernoulli product measure.

## An injective conservative binary rule is onto the two-particle sector

Assume additionally that tau is injective. Let delta_p denote the
configuration with its only 1 at p. Conservation gives
tau(delta_(1_G))=delta_a for some a in G. Equivariance then gives

    tau(delta_g)=delta_(ga).

Define the right-coordinate shift R_a by

    (R_a x)(g)=x(ga),

and set eta=R_a composed with tau. This shift is an equivariant reversible
CA over an arbitrary, possibly nonabelian, group. It sends delta_(ga) to
delta_g, so eta fixes every one-particle configuration. The composition
is injective, fixes 0, and conserves particle number. We do not assume
R_a commutes with tau.

Choose a finite memory N for eta. If two particles at p and q never
occur together in any translated neighborhood gN, locality and the
identities on 0 and one-particle configurations imply that eta fixes
the pair. A translated neighborhood can contain both particles only if

    p^(-1)q is in N^(-1)N.

Let C_2 be the set of all two-particle configurations, and let B_2 consist
of those for which this condition holds. The set B_2 is a union of
finitely many translation orbits: each such orbit has a representative
supported on {1_G,d}, with d in the finite set N^(-1)N minus {1_G}.
Every point of C_2 outside B_2 is fixed by eta.

Conservation gives eta(C_2) subset C_2. Injectivity forces eta(B_2)
subset B_2: if an element of B_2 mapped to a point y outside B_2, that
point would also be its own preimage. An equivariant map takes each
transitive G-orbit onto an entire G-orbit. Injectivity ensures that two
different source orbits have different image orbits. Hence eta induces
an injection of the finite set B_2/G into itself, which is a permutation.
Its restriction to each source orbit is a bijection onto the image orbit.
It follows that eta, and therefore tau, is bijective on C_2.

The argument also covers finite G. It does not use finiteness or
triviality of the stabilizers of two-particle configurations: equivariance
and injectivity already give the required orbit bijections.

## Why the attempted induction does not establish full surjectivity

The normalization fixes the one-particle sector, but we have proved only
bijectivity, not pointwise identity, on the two-particle sector. A
configuration of three particles can have a nearby pair and a distant
single particle. The pair's behavior has not been shown to be trivial.
There can therefore be infinitely many affected three-particle translation
orbits, indexed by the position of the distant component. The finite-orbit
permutation argument does not repeat as stated.

More generally, bijectivity on smaller finite-particle sectors does not
by itself provide a compatible local inverse on configurations with several
interacting components. A proof of post-surjectivity would supply a much
stronger repair property: every finite change to an attained output would
lift to a finite change of each chosen input. Neither (C1), the expectation
identity (C4), nor the two-particle argument establishes that property.

Thus this investigation has not produced a globally injective strict
full-shift rule with data-dependent syndrome updates. It has identified
verified constraints on a conservative version of such a program and an
exact missing step, rather than a completed higher-particle induction.

## Primary literature and exact scope

- [Pivato, Conservation Laws in Cellular Automata](https://arxiv.org/pdf/math/0111014),
  Proposition 3, gives finite local conservation tests. Proposition 7 uses
  amenability for its expectation characterizations. Section 5, Proposition 9
  and Corollary 10 use finite quotient groups injective on the doubled memory
  set, with that quotient family defined in Section 1. Corollary 10 records
  a uniform-Bernoulli one-site expectation identity. Those arguments should
  not be cited as a proof of unrestricted arbitrary-group surjunctivity.
- [Kari and Taati, Conservation Laws and Invariant Measures in Surjective
  Cellular Automata](https://siamak.isoperimetric.info/articles/automata2011.pdf),
  Theorem 1, assumes a surjective CA on Z when relating an additive conserved
  quantity to invariance of its associated full-support Bernoulli measure.
  Section 4 discusses higher-dimensional extensions on Z^d, still with
  surjectivity. The assumption cannot be dropped when applying that theorem
  to the present question.
- [Capobianco, Kari and Taati, Post-surjectivity and balancedness of cellular
  automata over groups](https://dmtcs.episciences.org/3918), proves that
  pre-injectivity together with post-surjectivity gives reversibility over
  arbitrary finitely generated groups, and that reversible CA over arbitrary
  groups preserve the uniform product measure. Its hypotheses provide
  stronger information than particle conservation or a conserved marginal.

The bounded literature inspection did not verify a theorem resolving
injective number-conserving CA over all groups. That search outcome is
neither evidence of novelty nor a claim that the question is open in the
literature. The self-contained proofs above are the authoritative scope
of this artifact.
