# A hyperlinear nonsofic group: attempt, results, failures, and what survives

Date: 2026-08-26.  Target: `hyperlinear-nonsofic-group` (Pestov Question 3.4,
separation side).  Companion to `notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md`.

## 0. Outcome, stated first

No hyperlinear nonsofic group was produced.  What was produced:

- a structural argument that the separation cannot come from any known
  Connes-embeddability permanence theorem, because each such theorem has a
  soficity twin (Section 1) -- so the first hyperlinear nonsofic group must
  be certified by bare-hands microstates for a Kazhdan group with a
  non-normalizing compression, an unprecedented kind of construction;
- three new established nodes: a stakes lemma showing the Leavitt fork's
  hyperlinear branch is at least as hard as hyperlinearity of Thompson's `V`
  (`leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear`); an
  embedding of the Kun--Thom wreath candidate into a finitary-permutation
  extension whose von Neumann algebra is `R rtimes G`
  (`wreath-candidate-embeds-in-finitary-permutation-extension`); and the
  lifting criterion `R rtimes_alpha G` is Connes embeddable iff `alpha` lifts
  to `N_(R^omega)(R)`, with the trace condition automatic for outer actions
  (`finitary-extension-ce-iff-action-lifts-to-normalizer`);
- an analysis, in my own terms, of exactly what microstates of the
  Kun--Thom wreath would have to look like and of why each natural design
  collapses (Sections 3--5), matching but re-deriving the graph's fences;
- a recommendation of which fork machine to attack and in which
  formulation (Section 6).

Everything is labelled proved / computed / speculated.

## 1. No permanence theorem can produce the separation (structural)

Every Connes-embeddability permanence theorem I know of has a soficity twin:

| CE permanence | sofic twin |
|---|---|
| subgroups, direct limits, direct products | same |
| amalgamated free products over amenable subalgebras/subgroups (Brown--Dykema--Jung, Popa) | Elek--Szabo, Paunescu |
| HNN extensions over amenable associated subgroups | Elek--Szabo |
| extensions with amenable quotient (crossed products by amenable groups) | Elek--Szabo |
| graph products (Caspers--Fima) | Ciobanu--Holt--Rees |
| wreath products over sofic actions (Hayes--Sale, GKEP) | same theorems |

So if a group `H` is shown hyperlinear by assembling hyperlinear pieces with
any of these, and all the pieces are sofic, `H` is sofic.  The first
hyperlinear nonsofic group therefore either (a) has a nonsofic piece, which
begs the question, or (b) is certified hyperlinear by a direct microstate
construction with no permanence input.  All known nonsofic groups (Leavitt
unit group, Kun--Thom wreath, Fournier--Facio) are (T)-compression groups,
so (b) means microstates for a Kazhdan group with a non-normalizing
compression that are simultaneously far from every finite-quotient
representation.  Nothing of this kind exists in the literature.

This is not a theorem (it is a statement about the literature), so it is
recorded here and not as a node.

## 2. The fork machines and their price tags (proved)

Every nonsofic group is a fork machine: hyperlinear gives the separation,
nonhyperlinear gives `non-hyperlinear-group`.  The new stakes lemma prices
the hyperlinear branches:

- **Leavitt unit group / `EL_D(R)`.**  Contains Thompson's `V`
  (`leavitt-cylinder-swaps-generate-thompson-in-el`).  So hyperlinearity of
  the Leavitt group implies hyperlinearity of `V`, an open problem in its own
  right that this graph is simultaneously attacking in the negative
  direction.  Attacking the Leavitt fork's hyperlinear branch is attacking
  "is `V` hyperlinear" with extra baggage.
- **Fournier--Facio group.**  Contains an injective copy of a finitely
  presented simple torsion-free group `S` (Burger--Mozes or Hyde--Lodha).
  Hyperlinearity of these is not recorded as known.
- **Kun--Thom wreath `W`.**  Contains the residually finite actor `G`
  (free) and the sub-wreaths over parabolic orbits (`positive-core-bernoulli-ce`
  shows the positive part is sofic).  No named open problem sits below its
  hyperlinear branch.

Recommendation: `W` is the candidate whose hyperlinear branch is not known
to be at least as hard as a famous open question.

## 3. What microstates of `W` must be (computed)

Fix the Kun--Thom pair `Gamma = EL_r(R_+) < G = EL_r(R) rtimes SL_d(Z)`,
`X = G/Gamma`, `W = C_2 wr_X G`, base coset `x_0`, compressor `t` with
`t Gamma t^(-1) < Gamma`.  A hyperlinear model of `W` is, without loss of
generality (all lamps are translates of the base lamp), an HS-asymptotic
representation `u_n: G -> U(d_n)` with canonical traces together with a
projection `e_n` of trace `1/2` such that:

- (i) `e_n` asymptotically commutes with `u_n(Gamma)`;
- (ii) the translates `u_n(g) e_n u_n(g)^*`, `g` ranging over coset
  representatives, asymptotically commute pairwise and are asymptotically
  independent (`tr(e u_g e u_g^*) -> 1/4` for `g notin Gamma`);
- (iii) mixed traces `tr(e_(x_1) ... e_(x_k) u_n(g)) -> 2^(-k) delta_(g,1)`.

Two consequences follow from finite-dimensional commutant rigidity alone
(no property (T)):

**(a) The actor cannot be a finite quotient, even approximately.**  If
`u_n` were a genuine finite-dimensional representation then `u_n(t)`
normalizes `u_n(Gamma)'` (injective self-map of a finite-dimensional
commutant), so the transported lamp `u_n(t)e_nu_n(t)^*` commutes with
`u_n(Gamma)`, whereas in `W` the element `gamma in Gamma \ t Gamma t^(-1)`
moves the coset `t x_0`; condition (ii) is violated.  This is
`finite-quotient-blindness` in commutant language.  In particular the
profinite closure `bar Gamma = cap_n Gamma N_n` is a normal subgroup strictly
containing `Gamma`, and the lamp pairs `(x_0, h x_0)`, `h in bar Gamma \ Gamma`,
are identified in every finite quotient of `W`.

**(b) The actor must be far from genuine representations along every
compressor simultaneously.**  The graph's
`kt-wreath-relative-canonical-actor-exactification` says actor-leg
exactification is already terminal (it would prove non-hyperlinearity), and
`kt-single-compressor-canonical-lamps-do-not-exactify-actor` builds, for
each single compressor, canonical permutation microstates of the
one-compressor wreath.  So "exotic" microstates of `G` exist for each
compressor separately; the separation needs them for at least two
incompatible compressors at once (`kt-two-positive-compressors-generate-full-obstruction`).

## 4. Designs I tried, and how they die

1. **Lamps diagonal, actor arbitrary.**  Put lamps in a diagonal
   `D_(Y_n) tensor 1` and let `u_n(g)` map the joint eigenspaces of a lamp
   window to those of the shifted window.  If the target partition were a
   coarsening of a fixed one, `u_n(g)` would be block-monomial over a fixed
   index set and `block-monomial-coordinate-collapse` applies.  It is not:
   `u_n(g)` maps atoms of `P_F` to atoms of `P_(gF)`, a different partition
   with new lamps.  So this design is *not* killed by the collapse theorem;
   it is simply the abstract problem of Section 3 restated, and I could not
   produce the actor.

2. **Tensoring two single-compressor models.**  The tensor product of the
   canonical permutation models for `W_A` and `W_B` (the two positive cores)
   is again a permutation model, hence would be a sofic approximation of a
   group containing `W`; dead by Kun--Thom.

3. **Induced representations.**  Fibres of `Ind_Gamma^G` give
   `Gamma`-invariant projections whose translates are orthogonal, not
   independent, and of vanishing trace; the graph's
   `no-invariant-mean-on-coset-space` kills the charge version.

4. **Embedding `W` into `U(R)`.**  A faithful `pi: W -> U(R)` restricts
   to `G` as a character with injective GNS, hence (Bekka; the graph's
   `amenable-rep-of-kazhdan-has-fd-subrep`) a mixture of finite-dimensional
   characters, so `pi(G)''` is type I; I could not derive a contradiction
   because the lamps need not decompose along the center of `pi(G)''`, but I
   also see no way to build such a `pi`.  Inconclusive.

5. **Enlarging the group to make the base a factor.**  This one survives
   and is recorded (Section 5).

## 5. The finitary-extension reformulation (proved)

`W = C_2 wr_X G` embeds in `Sigma_2 = Sym_fin(X x {0,1}) rtimes G` (lamp at
`x` to the transposition of its two copies).  `Sym_fin` of an infinite set
is countable, locally finite and ICC, so `L(Sym_fin) ~= R`, and
`L(Sigma_2) = R rtimes_alpha G`.  Hence:

```text
R rtimes_alpha G Connes embeddable   =>   W hyperlinear   =>   Q3.4 separation.
```

And `R rtimes_alpha G` is Connes embeddable iff `alpha` lifts to a
homomorphism `G -> N_(R^omega)(R)` (Connes: every automorphism of `R` is
approximately inner, so `N -> Aut(R)` is onto with kernel `U(R' cap R^omega)`;
embeddings of `R` into `R^omega` are all conjugate), and for outer actions
the trace condition is automatic.  If every nonidentity element of `G`
moves infinitely many cosets -- which holds at least for every nonidentity
element of `EL_r(R)`, since a monomial substitution sends some exponent of a
nonzero Laurent polynomial out of the positive cone -- then all `alpha_g`
are outer and the whole question is the bare lifting problem:

```text
Does the pullback of  1 -> U(R' cap R^omega) -> N_(R^omega)(R) -> Aut(R) -> 1
along alpha: G -> Aut(R) split?
```

Why this is a better place to stand than `L(W) = D rtimes G`:

- the base is a factor, all of whose embeddings into `R^omega` are
  conjugate, so there is no "invariant Cartan completion" step and none of
  the diagonal/block-monomial collapse theorems has an abelian algebra to
  act on;
- the kernel `U(R' cap R^omega)` of the lifting problem is the unitary
  group of a `II_1` factor, and the obstruction is a nonabelian 2-cocycle
  `c(g,h) = u_g u_h u_(gh)^(-1)` valued there, for any set-theoretic lift;
- the calibration is sharp: trivial action reproduces hyperlinearity of
  `G`, free actor always lifts, amenable actor always lifts (the crossed
  product is hyperfinite).

What it does not do: it is a one-directional reduction (`Sigma_2`
hyperlinear implies `W` hyperlinear, not conversely), and the lifting
problem is not easier in any way I could exploit.  The natural attack --
lift on `Gamma` first (a genuine representation of a Kazhdan group into
`N`), then extend along the compressors -- runs into the same
two-compressor incompatibility: the lifts `u_t`, `u_(t')` of two compressors
must each implement a compression of the (T) subgroup on `R`, and the
cocycle between them is where the nonsoficity lives.

## 6. Where I would go next

1. Work on `W`, not on the Leavitt group (Section 2), in the `R rtimes G`
   formulation (Section 5), with the two named compressors
   `A, B` of `kt-two-positive-compressors-generate-full-obstruction`.
2. The concrete cocycle problem: choose lifts `u_A, u_B in N_(R^omega)(R)`
   of the two compressor automorphisms (each exists by Connes) and a lift of
   `Gamma` (exists: `Gamma` is residually finite, so
   `Gamma -> U(R) subseteq N` via a direct sum of finite quotients, but
   that lift is exactly the one item 3(a) forbids -- the correct lift of
   `Gamma` must itself be exotic).  The whole difficulty is now visible as a
   single nonabelian cohomology class of the finitely presented actor with
   coefficients in `U(R' cap R^omega)`.
3. Any positive proof will, by Section 1, be the first bare-hands
   microstate construction for a Kazhdan group with a non-normalizing
   compression.  I do not see it, and I do not think a small idea closes
   it.

## 7. Honest conclusion

The separation question remains open.  The three new nodes are a stakes
lemma and two reformulations; none of them is the theorem.  The structural
point of Section 1 is, I think, the most useful thing here: it says that
the hyperlinear branch of every fork machine is not a "wait for a
permanence theorem" problem but a new kind of construction, which is why
this graph's eleven routes into the root all bottom out in bare microstate
requirements.
