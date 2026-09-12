# Phase-preserving multi-relator search

## Question

The exact block-eight alignment makes the survivor class `C11` equal to
`i I`, but the complete radius-ten audit shows that it kills none of the 178
perfect-overlap relators.  Those 178 words collapse to 24 cyclic classes.
This experiment asks whether one relative alignment of the two honest
`A8` charts can simultaneously make representatives of all 24 classes close
to the identity while retaining the `C11` phase.

This is a finite compatibility diagnostic.  It neither presents all of the
Leavitt relation module nor proves a lower bound for arbitrary dimension.

## Executable model

`atlas_self_similarity_multirelator_export.py` reconstructs the complete
boundary and the 178 exact perfect-overlap certificates, deduplicates them to
24 cyclic classes, and exports their exact 64-dimensional chart matrices.  It
also exports the exact phase alignment.  The optional multiplicity parameter
replaces each chart representation by its direct sum with itself while
allowing the subsequent relative unitary to move in the full enlarged unitary
group.

`atlas_self_similarity_multirelator_search.py` optimizes only that relative
unitary.  For class values `r_j(U)` and phase value `s(U)`, its loss is

\[
 {1\over24}\sum_{j=1}^{24}\|r_j(U)-I\|_2^2
 +\lambda\|s(U)-iI\|_2^2.                         \tag{1}
\]

All chart representations remain exact throughout.  Norms below are
normalized Hilbert--Schmidt norms unless explicitly labeled operator norm.
The certificate scan used radius five, boundary-only mode, and at most ten
leaves.  It reproduced the exact counts 178 certified words, 56 survivors,
and 24 certified cyclic classes.

## First `U(64)` Pareto front

Every weight started from the exact `s(U)=iI` alignment and used 80 L-BFGS
steps.

| phase weight | zero RMS | zero maximum | phase HS | phase operator | imaginary phase trace |
|---:|---:|---:|---:|---:|---:|
| 0.01 | 0.712811 | 1.188805 | 1.411691 | 1.999738 | 0.003564 |
| 0.1 | 0.763481 | 1.204151 | 1.365901 | 1.999649 | 0.067157 |
| 1 | 1.123011 | 1.424848 | 0.179794 | 0.378045 | 0.983837 |
| 10 | 1.269077 | 1.415785 | 0.035223 | 0.071803 | 0.999380 |
| 100 | 1.331615 | 1.414400 | 0.011385 | 0.023243 | 0.999935 |

Thus the first local front has a sharp tradeoff rather than a simultaneous
small-error point.  Extending the zero-weight run to 314 closure calls gave
zero RMS `0.653964` and maximum `1.133119`, but destroyed the phase: phase HS
error `1.415631` and trace approximately zero.  Two independent Haar starts
gave zero RMS `0.684800` and `0.665196`, so the plateau is not peculiar to the
exact phase seed.  These are local-search observations, not certified global
minima.

Continuation from the best zero-only point did not uncover a hidden favorable
branch.  At phase weights `0.01`, `0.1`, `1`, and `10`, the pairs
`(zero RMS, phase HS)` were respectively

\[
 (0.645263,1.410973),\quad
 (0.644353,1.382246),\quad
 (1.017440,0.238724),\quad
 (1.262011,0.046090).                              \tag{2}
\]

## Multiplicity-two test

To break the direct-sum symmetry, the exact doubled alignment was perturbed
by a small dense skew-Hermitian exponential before optimization in the full
`U(128)`.  At weight 100, continued searches gave

| dimension | zero RMS | phase HS | phase operator | imaginary phase trace |
|---:|---:|---:|---:|---:|
| 64 | 1.279437 | 0.008520 | 0.018013 | 0.999964 |
| 128 | 1.271406 | 0.008401 | 0.019884 | 0.999965 |

The doubled optimizer is genuinely non-block-diagonal: relative to the two
64-dimensional multiplicity blocks, its off-diagonal part has normalized HS
norm `0.334236`, and its two diagonal blocks differ by normalized HS norm
`0.415487`.  Hence the `0.6%` zero-RMS improvement is a real multiplicity
coupling effect, not duplicated 64-dimensional output.  It is nevertheless
far too small to indicate that both errors tend to zero.

A zero-weight doubled run reached RMS `0.667557` after 251 total closure calls,
again with phase HS error `1.413304`.  At the present resolution multiplicity
two therefore does not change the qualitative tradeoff.

## Conclusion and next decision

The fixed-representation, one-relative-unitary ansatz has produced no direct
FALSE construction.  Near the exact phase, four certified classes with source
indices `70`, `86`, `90`, and `91` remain close to the orthogonal scale
`sqrt(2)` in both dimensions.  In zero-only optimization, the persistent worst
package instead contains `35`, `68`, `126`, and `127`.

An exact calculation made immediately after this run prevents a false
interpretation of the persistent four-class package.  Classes `70`, `86`,
`90`, and `91` together with the phase class lie in a local `S4*S4`.  There is
a homomorphism from its quotient by those four zero relators onto
`PSL(2,7)` under which the phase survives.  Therefore no inequality using
only the local `S4` laws and those four relators can force the phase to vanish.
The durable certificate is
`experiments/atlas_stubborn_s4_certificate.py`, with proof scope in
`notes/FALSE_ATLAS_STUBBORN_S4_QUOTIENT.md`.

Do not spend a large sweep on more weights, seeds, or an exact four-class
obstruction.  The next high-yield work is one of:

1. add enough of the other 20 certified-zero classes to expose the first
   package that prevents the local separating map from extending;
2. implement a representation-theoretic enlargement in which the two vertex
   representations themselves acquire new irreducible multiplicities, rather
   than merely duplicating the current `(5,2,1)` chart;
3. test multiplicities above two only after changing the evaluator to exploit
   word/block structure, since dense cost scales cubically.

The present data rule out none of those routes and say nothing universal about
hyperlinear versus sofic groups.

## Outer-stable exact-zero endpoint and the involutory phase

The subsequent exact `A8` quotient changes the representation family.  Let

\[
 \theta(g)=(g^{-1})^{\mathsf T},\qquad
 \sigma=\rho\oplus(\rho\circ\theta),                \tag{3}
\]

where `rho` is the 64-dimensional `(5,2,1)` representation.  The direct sum
is stable under the outer automorphism.  If `h` is the certified outer
alignment and `S` swaps the two summands, then

\[
 U_0=\sigma(h)S,qquad
 U_0\sigma(g)U_0^*=\sigma(h\theta(g)h^{-1}).         \tag{4}
\]

The exporter now constructs this point exactly.  In dimension 128 all 24
certified classes have identity error at most `6.47e-15`.  The survivor is a
noncentral involution with trace zero, hence is at HS distance `sqrt(2)` from
both `iI` and `-I`.

The exact quotient point is stationary for the smooth loss.  After a dense
`1e-2` skew-Hermitian perturbation, weights `0.1` and `1` return to it when
the phase target is `iI`; weight `10` crosses to the old phase-side basin.
Backward continuation gives:

| `iI` phase weight | zero RMS | phase HS |
|---:|---:|---:|
| 10 | 1.272649 | 0.034630 |
| 1 | 1.092851 | 0.224533 |
| 0.3 | 0.943395 | 0.418604 |
| 0.1 | 0.701255 | 1.372264 |

The target `iI` is not intrinsic to central-kernel survival.  Repeating the
same continuation with the involutory target `-I` is dramatically better:

| `-I` phase weight | zero RMS | zero maximum | phase HS | phase operator | phase trace |
|---:|---:|---:|---:|---:|---:|
| 10 | 0.491114 | 0.794729 | 0.057228 | 0.115708 | -0.998362 |
| 1 | 0.352252 | 0.555910 | 0.212666 | 0.412192 | -0.977386 |

The weight-ten line is after two 120-step continuations; the weight-one line
continues backward from it.  The operator norm is computed against the actual
selected target.  Earlier `iI` operator values were already correct; an
initial diagnostic for `-I` accidentally compared against `iI` and has been
discarded.

This is the strongest simultaneous numerical signal in this experiment, but
both errors remain macroscopic.  The next decisive test is multiplicity
scaling of `(3)--(4)` from the retained `-I` states.  If the errors do not
improve under symmetry-broken full-unitary coupling, stop this fixed-irrep
family.  If they do, extract whether the optimizer is isolating a shrinking
bad subspace, as suggested by the small phase operator error and trace.

That multiplicity test has now been run.  Two copies of the balanced
128-dimensional state were embedded in dimension 256 and perturbed in the
full `U(256)`, first narrowly and then with a ten-times larger dense
skew-Hermitian perturbation.  The weight-one results are:

| dimension | zero RMS | phase HS | phase operator | weighted objective |
|---:|---:|---:|---:|---:|
| 128 | 0.352252 | 0.212666 | 0.412192 | 0.169308 |
| 256, narrow break | 0.352035 | 0.212209 | 0.410029 | 0.168961 |
| 256, wide break | 0.352294 | 0.212443 | 0.410379 | 0.169243 |

The best objective improvement is only `0.205%`.  The narrowly broken final
state has off-block normalized HS mass `0.00557`; the wide run retains
`0.03240` off-block mass but does not improve the errors.  Thus there is no
useful multiplicity scaling signal in the fixed outer pair through dimension
256.  Stop this family.  A new continuation must change the actual irrep
content, rather than duplicate `rho directSum (rho after theta)`.

## Explicit centrality in the 30-dimensional tangent model

The exact outer-tangent theorem uses the permutation representation on the
15 nonzero vectors and its outer twist, for dimension 30.  Its outer quotient
kills all 24 zero classes exactly and has a 136-dimensional zero-relation
tangent kernel, with phase derivative rank 60 on that kernel.  To test the
actual central-kernel requirement, the bundle was enlarged by the 12 words

\[
 [r_{11},g],\qquad g\text{ a generator of either }A_8\text{ chart}. \tag{5}
\]

The exact quotient starts with certified-zero RMS zero, centrality RMS
`0.869227`, centrality maximum `1.264911`, and `-I` phase error `1.712698`.
A partial symmetric eigensolver was used to perturb inside the numerical
136-dimensional kernel.  Full-unitary L-BFGS then gave:

| phase weight | all-identity RMS | all-identity max | phase HS | phase trace |
|---:|---:|---:|---:|---:|
| 0.1 | 0.498453 | 1.265065 | 1.712612 | 0.466521 |
| 1 | 0.480563 | 1.368373 | 1.366428 | -0.066438 |
| 10 | 0.484497 | 1.367831 | 1.366273 | -0.066649 |

Without the commutators, weights from `0.1` through `100` simply converge to
an exact certified-zero quotient with phase trace `-1/15` and phase error
`1.366260`.  With `(5)`, the worst constraints are phase commutators and stay
macroscopic.  Thus generic full-unitary descent does not integrate the exact
phase-moving tangent space into a central phase.

This does not contradict the tangent theorem: its rank statement concerns
the full phase matrix derivative, while the scalar-target character is
stationary at a representation and nonlinear centrality can have second-order
obstructions.  Stop generic L-BFGS in this 30-dimensional model.  The next
specific lanes are to solve the second-order equations inside the tangent
kernel, or start from the exact order-2688 local central block and couple in
the 20 outside certified classes using induced/regular representation
coordinates rather than dense 20,160-dimensional matrices.
