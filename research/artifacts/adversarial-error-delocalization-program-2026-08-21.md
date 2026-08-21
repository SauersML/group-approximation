# Adversarial error delocalization and recursive challenge libraries

**Date:** 2026-08-21

## Executive conclusion

The motivating diagnosis is correct: normalized Hilbert--Schmidt microstates
can hide arbitrary behavior on an `o(d)`-dimensional reducing summand. A useful
non-hyperlinearity mechanism therefore cannot merely locate one bad region. It
must either begin with a mark that already has positive trace density, or prove
that every surviving marked model pays a fixed fraction of global relator
energy.

The self-aware-machine idea also survives, but in a cleaner form than “search
for the current matrix approximation.” The machine need not observe matrices,
their dimensions, or a soundness threshold. It may install an infinite
recursively enumerable challenge library; a reverse-Kleene program searches
only for a formal proof that its marked word is trivial. If NONHALT semantics
kill the mark in every tracial matrix ultraproduct, compactness, Kleene, and
effective Higman perform the rest.

The combined target is therefore

```text
an amplification-invariant r.e. challenge library
+ a standard-index/no-tail theorem
+ a positive-density marked carrier
+ finite global consistency or feedback.
```

Raw recursion, expanders, heavy-tailed observables, ambient dimension sensors,
and “a group containing every finite configuration” do not by themselves
supply the missing density.

## 1. Source ideas preserved

The proposed mechanisms were:

- make approximation error grow as more of the group is exposed;
- prevent error from remaining localized;
- force incompatible elements to spread distinct failures through a shared
  carrier;
- use self-similarity or recursive copying so a late failure returns with
  constant weight;
- build a Turing-complete group-word machine which searches for finite models
  and manufactures a dimension-overflow challenge;
- exploit a flexible dichotomy: either relator error remains visible or a
  fixed nonidentity marked word is erased;
- create an infinite-recursion/nonhalting phase that finite matrices cannot
  reproduce;
- use redundancy, error correction, or PCP-style checks so corrupting the
  computation itself causes widespread error;
- place every potentially useful finite configuration inside one universal
  “library group”; and
- imitate a heavy-tailed singularity whose rare bad regions have unavoidable
  global impact.

These intuitions all point at the same mathematical bottleneck: turn a local
or late obstruction into a bounded, amplification-invariant, positive-density
normalized-HS obstruction.

## 2. Exact closure under sublinear contamination

If `V_n` is a regular `d_n`-dimensional microstate and `W_n` is any
`r_n`-dimensional tuple with `r_n/d_n->0`, then

```text
Z_n=V_n direct_sum W_n
```

is a microstate for the same trace. Every fixed word trace changes by
`O(r_n/d_n)`, and every fixed relator's squared HS defect receives only an
`O(r_n/d_n)` contribution.

This is the fundamental adversary. It may put a maximally false predicate,
tiny singular value, exotic finite packet, or marked finite-dimensional
representation on `W_n`, and all bounded finite tests still ignore it.

The determinant version is especially severe:
`sublinear-block-poisons-normalized-torsion` shows that an unbounded `log`
statistic can be changed by order one using a superexponentially small singular
value on the vanishing corner. Heavy tails help the approximator, not the
proof. A viable global statistic should be bounded and continuous; singular
tail sensitivity is an `o(d)`-corner vulnerability.

## 3. Recursive copying cannot cross a reducing projection

The exact result `word-recursion-cannot-amplify-sublinear-summands` covers any
finite depth packet of word maps, polynomial checks, recursive conjugates,
expander walks, self-similar copies, or decoded tests. Such evaluations respect
direct sums. Consequently their total normalized-HS energy is the
dimension-weighted average of the bulk and bad-block energies.

Even if depth `L_n`, copy count `N_(L_n)`, and norm bound `C_(L_n)` grow with
`n`, the adversary can first choose a sufficiently accurate bulk microstate,
amplify it by `K_n` copies, and append one fixed bad block, with `K_n` chosen so
that

```text
N_(L_n) C_(L_n)^2 dim(W)/(K_n dim(V_n)) -> 0.
```

This defeats every recursion packet that is finite at each stage.

The invariant explanation is sharper. If `p` projects onto the reducing bad
summand, every evaluated word commutes with `p`. For any probability measure
`mu` on words, the adjoint averaging channel

```text
Phi_mu(X)=sum_g mu(g) rho(g) X rho(g)^*
```

fixes `p`. Hence `p-tau(p)I` is a nonzero trace-zero fixed vector whenever
`0<tau(p)<1`. No word-generated adjoint channel can have a scalar-only spectral
gap uniformly over reducible microstates. Its correct fixed algebra is always
`rho(G)'`, which contains the localized summand projection.

So expansion can mix **inside** a recovered irreducible carrier, but it cannot
manufacture that carrier's density or mix across central reducing summands.

## 4. What error spreading can still do

Suppose a fixed marked word gives a spectral projection `p` with

```text
tau(p)>=beta>0.
```

If a local-to-global decoder proves

```text
sum_j ||R_j p||_2^2 >= c tau(p),
```

then global relator energy is at least `c beta`. This is the productive
architecture:

```text
marked separation
 -> positive-density carrier
 -> coherent local coordinates on that carrier
 -> redundant/expanding consistency checks
 -> fixed global HS payment.
```

The exact analytic condition is now isolated by
`relative-fixed-algebra-payment-lemma`. If `N` is the full fixed algebra of
the packet action, an adjoint Poincare gap charges only
`||p-E_N(p)||_2^2`. Thus positive density must be supplemented by a
no-capture estimate

```text
||E_N(p)||_2^2 <= (1-gamma)tau(p).
```

For a finite packet this is the explicit averaged-overlap inequality

```text
|H|^(-1)sum_h tau(p h p h^*) <= (1-gamma)tau(p).
```

A covariance bridge must then charge the resulting commutators to defining
relators. This criterion is sharp: if `p` lies in an external multiplicity
reservoir, it has positive density but belongs to `N` and pays zero energy.

The graph already separates these roles:

- `marked-hs-separation-forces-spectral-density` supplies macroscopic mass;
- `tree-transitive-site-noise-localization` asks to convert group relator
  energy into bounded bad-site density after coherent tensor recovery;
- `bgv-adversarial-fault-tolerance` repairs a specified tensor-site noise
  model;
- `robust-locally-satisfiable-relator-code` asks for PCP-style redundant
  noncommutative checks; and
- `constant-hs-groupification-of-residual-dimension-tape` is the explicit
  capacity-overflow program with a runtime-independent HS budget.

The new recursion firewall says those mechanisms may route an existing
positive-density mark, but none may begin from “there exists one bad finite
corner.”

## 5. Threshold-free self-reference

One strong surviving self-aware construction is semantic rather than
introspective. A total computable compiler outputs

```text
Gamma_e=<S_e | R_(e,1),R_(e,2),...>,       w_e,
```

where `S_e` is finite and the relators are uniformly recursively enumerable.
It is enough to prove

```text
e halts       => some exact representation detects w_e,
e does not halt
              => every homomorphism Gamma_e -> product_omega U(d_n)
                 kills w_e.
```

The fixed-point program enumerates only formal normal-closure certificates for
`w_e=1`. It never reads a matrix dimension, runtime, defect threshold, cutoff,
decoder modulus, or convergence rate. Kleene produces a nonhalting index with
a nontrivial word in the hyperlinear radical; effective Higman embeds the
finitely generated r.e. group in a finitely presented non-hyperlinear group.

This is recorded by:

- `hyperlinear-radical-presentation-compactness`;
- `threshold-free-reverse-kleene-higman-diagonal`; and
- the concrete weak target
  `fanizza-native-signal-ultraproduct-groupification`.

This radical-valued interface is stronger than necessary. The weaker
`canonical-profile-kleene-higman` permits a rational group-algebra mark and
requires NONHALT collapse only along canonical-delta microstates. Its concrete
open target is `fanizza-canonical-profile-groupification`. The fixed-point
program still reads no numerical modulus, and noncanonical exact
representations are irrelevant.

For an unconditional **word** library,
`hyperlinear-radical-is-finitely-witnessed` proves more: if the whole r.e.
presentation kills the mark, some finite relator prefix already has that word
in its hyperlinear radical. Thus the infinite library is useful for effective
syntax and self-reference, not for additional semantic radical power. The
prefix need not be computable, so effective Higman remains the mechanism that
actually names a finite presentation.

## 6. The standard-index/no-tail requirement

An r.e. list of challenges is not automatically sound. At coordinate `n`, a
matrix model may move its active failure to challenge index `j_n->infinity`.
Every fixed standard challenge is then eventually satisfied, so all standard
relators hold in the ultraproduct while the marked obstruction survives at a
nonstandard index.

Any successful recursive library therefore needs one of:

- a finite feedback cycle returning every surviving carrier to a fixed root;
- a strict bounded recurrence, such as `a_n<=lambda a_(n+1)` with
  `lambda<1`, forcing `a_0=0`;
- a first-hit or expander theorem charging one standard test; or
- an amplification-invariant intrinsic selector preventing drift to infinity.

Compactness plus tensor powers says that if the entire standard word library
really kills the mark in every matrix ultraproduct, one finite prefix already
kills it exactly in every matrix ultraproduct. The analogous canonical-profile
word statement uses one finite relator-and-trace window at any cutoff below
`sqrt(2)`. What compactness cannot do is prove the semantic no-tail statement
for a proposed compiler.

Two concrete firewalls explain common failures. By
`closed-local-rules-have-uniform-hitting-or-infinite-safe-tail`, a closed
finite-range recursion with arbitrarily long safe runs has an infinite safe
tail. By `amenable-finite-propagation-feedback-has-folner-tail-models`, an
exact amenable shift-local tail compresses to matrix models whose relator
defect lives only on a vanishing Folner boundary while a positive-density mark
survives. The latter refutes a canonical-profile compiler only when the tail
models also have the regular character.

## 7. Why a raw dimension-overflow detector fails

Tensor amplification

```text
U -> U tensor I_k
```

preserves normalized-HS relator defects and marked-word distances exactly.
The same model therefore has apparent dimensions `d,2d,3d,...`. A challenge
selected from raw ambient dimension is not intrinsic. It is sound only if all
multiples activate equally strong tests, which returns to the original uniform
problem.

Threshold-free reverse Kleene makes the dimension sensor unnecessary. The
challenge selector should instead be built from amplification-invariant data:
trace moments, packet characters, projective/commutant structure, or a fixed
word-generated carrier.

## 8. Why a universal library group is insufficient

`universal-finite-packet-library-can-be-amenable` gives a sharp counterexample.
The two-generated amenable group

```text
Sym_fin(Z) semidirect Z
```

contains every finite group. In its canonical trace, every irreducible sector
of every finite subgroup occurs at the exact Plancherel fraction
`(dim rho)^2/|F|`. Thus “every finite configuration is somewhere inside, at a
positive canonical fraction” is compatible with amenability and
hyperlinearity.

The trace budget explains why. Infinitely many packet projections may overlap
or behave independently; then their positive densities do not add. If
cross-relations force them pairwise orthogonal, `N alpha<=1` already in the
exact regular model, so infinitely many fixed-density carriers are impossible
and the intended exact witness collapses.

A useful library must therefore reuse one physical carrier and force a
finite-dimensional-only inconsistency in its multiplicity or holonomy. Library
cardinality alone has no capacity consequence.

## 9. Proper infiniteness is only a completeness tool

The HALT witness may live on `H isomorphic_to H direct_sum H` and absorb
arbitrary finite packet multiplicities. It need not be finite-dimensional or
tracial. This legitimately simplifies completeness.

It cannot by itself prove NONHALT soundness. The left regular group von Neumann
algebra is finite and directly finite. Any exact group identity forcing the
mark to vanish in every finite von Neumann algebra would also kill it in the
regular representation, making the group word trivial. The soundness theorem
must distinguish Connes-embeddable finite algebras from the canonical regular
algebra, not merely finite from properly infinite representations.

## 10. Clean surviving research target

The weakest currently identified version of the audacious program reduces to
one honest compiler:

> Construct a finitely generated, uniformly r.e. recursive challenge library
> with a HALT-detectable rational group-algebra mark and NONHALT death of that
> mark along every canonical-delta microstate sequence. The soundness proof
> must use amplification-invariant intrinsic data, prevent escape to a
> nonstandard challenge index, and begin from a mark with positive spectral
> density before invoking expansion or recursion.

This target is weaker than both a finite quantitative compiler and
unconditional hyperlinear-radical death. No modulus or finite relator window
must be computed. It is stronger than an enumerated collection of finite
challenges, because the canonical-profile no-tail theorem is essential.

The strategic slogan is:

```text
Do not ask recursion to create density.
Use the mark to create density, recursion to spread consistency,
the r.e. library to contain every intrinsic challenge,
and reverse Kleene plus Higman to finish.
```

## 11. Nonamenable ownership theorem

The lower half of a nonamenable feedback mechanism can be proved exactly.
By `embedded-group-algebra-carriers-have-no-excess-fixed-component`, if
`L(G)` embeds trace-preservingly in any finite tracial algebra, the projection
of an embedded `x in L(G)` onto the ambient `H`-fixed space is exactly the
embedded canonical conditional expectation. Excess multiplicity commutants
cannot capture more of this particular carrier.

Consequently, if a cyclic Fourier carrier

```text
x=sum_k c_k lambda(w^k)
```

has every supported nonzero power on an infinite `H`-conjugacy orbit, its
conditional expectation is `c_0 I` in every canonical embedding. A
property-`(T)` Kazhdan set then gives the amplification-proof floor

```text
sum_s||[s,x]||_2^2 >= kappa sum_(k!=0)|c_k|^2.
```

This eliminates the generic multiplicity-capture objection for a carrier
whose canonical orbit geometry is designed correctly. Property `(T)` alone
is not enough: `property-t-does-not-force-marked-carrier-transversality`
exhibits the hyperlinear group `D_infinity times K` with a positive-density
spectral carrier fully fixed by an infinite property-`(T)` subgroup.

The surviving construction target is
`matrix-only-cyclic-carrier-invariance`: force the transverse Fourier carrier
to become asymptotically invariant in finite matrices, while the regular
representation retains the strict lower floor. Such an upper bound must be
finite-dimensional/CE-specific; if it followed formally from group relations,
it would contradict the regular representation itself.

The canonical finite-packet audit reaches the same boundary from the finite
side. `canonical-finite-packet-data-stop-at-scalar-overlaps` computes all
forced Plancherel masses, two-subgroup intersection-character overlaps, and
finite-conjugation Reynolds checks. Exact regular representations still allow
independent rotations of every isotypic multiplicity reservoir. Canonical
trace authenticates scalar leakage when group combinatorics already moves a
sector, but it does not manufacture a common carrier or reservoir gauge.
