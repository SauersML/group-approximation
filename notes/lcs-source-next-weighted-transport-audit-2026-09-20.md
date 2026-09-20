# Next source attempt: non-literal embeddings need weighted, family-uniform transport

Date: 2026-09-20. Bounded independent source audit; no computation or build.
The HALT-positive weighted linear-plus-conjugacy source remains OPEN.
This note adds no canonical claim. It tests a concrete proposed route:
choose a group/representation source using an exact algebraic embedding,
then use a succinct subdivision or solution-group embedding to obtain the
required bounded-width matrix-energy family.

## 1. The useful positive interface is a weighted proof certificate

For unitary presentations, let source relators r_i have positive weights
mu_i and target relators t_j have positive weights nu_j. Suppose substitution
along fixed generator words has explicit free-group identities

    iota(r_i) = product_l g_il t_(j_il)^(epsilon_il) g_il^-1.

Let a_ij count appearances of t_j in this certificate, L_i=sum_j a_ij,
and set

    C = max_j [sum_i mu_i L_i a_ij]/nu_j.                 (1)

For every matrix dimension and every unitary target tuple, unitary
invariance, telescoping, and weighted Cauchy--Schwarz give

    ||iota(r_i)-I||_2 <= sum_j a_ij ||t_j-I||_2,
    sum_i mu_i ||iota(r_i)-I||_2^2
        <= C sum_j nu_j ||t_j-I||_2^2.                  (2)

The proof uses `(sum_j a_ij d_j)^2 <= L_i sum_j a_ij d_j^2` and then
interchanges the finite sums. Repetitions and inverse relators are counted;
conjugator lengths do not enter (2). Equivalently, a bound on the weighted
operator norm of the nonnegative incidence matrix gives a possibly better
constant. This is a soundness certificate, not an embedding theorem.

For an LPC application one must include **every** tested word, including
within-row commutators, and ensure substituted source generators are
involutions on the target domain (or pay separately for rounding them).
The factor 1/4 in the source energy cancels if used on both sides.
Completeness additionally needs a matrix-model extension that sends
source energy tending to zero to target energy tending to zero. An exact
abstract group embedding alone does not give that extension.

If these conditions hold with C bounded independently of the machine
input, a source lower bound Delta gives target lower bound Delta/C.
This is the precise reusable quantitative interface, not a claim that a
HALT-positive source or the required certificates have been constructed.
For succinct instances, polynomial-time row access alone does not certify
(1); the weighted bound must be proved uniformly over all exponentially
many rows.

This is the weighted version of the fixed-relator restriction estimate
already used in `wagon-wheel-stops-before-bcs-groupification` and
`marked-approximate-radical-survives-solution-group-embedding`. Its relevance
here is that a dimension-free constant for each presentation can grow
without bound through a family. The following exact countermodel shows
that even Tietze equivalence, width two, and efficient sampling do not
remove this issue.

## 2. A width-two, two-dimensional countermodel to uniform transport

Use the energy convention of `lcs-construct-weighted-conjugacy-to-lcs`:
for a two-variable row with sign epsilon,

    e_epsilon(A,B) = (1/4)||AB-epsilon I||_2^2
                       +(1/4)||AB-BA||_2^2,

where A and B are self-adjoint involutions and the matrix trace is
normalized. Take the two rows AB=I and AB=-I, each with weight 1/2.
The parallelogram identity gives, in every dimension,

    E_source(A,B) = 1/2 +(1/4)||AB-BA||_2^2 >= 1/2.     (3)

Equality holds for commuting A,B, so the infimum is exactly 1/2.

For N>=1 replace the positive row by a path on X_0,...,X_N:

    X_i X_(i+1)=I,     i=0,...,N-1, weight 1/(2N),
    X_0 X_N=-I,                    weight 1/2.          (4)

Each row has two distinct variable names. The positive family still has
total weight 1/2, so this is not dilution of the whole contradictory test
by an arbitrarily small test probability.

As a presentation over a central involution J, replace the last -I by J.
The path equations eliminate X_1,...,X_N by Tietze transformations. The
last equation then sets J=1. Both the original and subdivided marked
presentations are the same group C_2 with collapsed mark. In particular
the subdivision preserves the exact group and every exact representation;
neither system has a J=-I representation.

Nevertheless, let X and Z be the real Pauli matrices, put theta=pi/N,
and assign the balanced 2-by-2 reflections

    X_i = cos(i theta) Z + sin(i theta) X.              (5)

They are exact self-adjoint involutions. The last row is exact because
X_N=-X_0. On every positive edge,

    (1/4)||X_i X_(i+1)-I||_2^2 = sin^2(theta/2),
    (1/4)||X_i X_(i+1)-X_(i+1) X_i||_2^2 = sin^2(theta).

These follow by multiplying two Pauli reflections; the first product has
eigenvalues exp(plus/minus i theta), and the commutator difference has
squared normalized norm 4 sin^2(theta). Thus

    E_target <= (1/2)[sin^2(pi/(2N))+sin^2(pi/N)]
             <= 5 pi^2/(8N^2).                        (6)

This is an explicit matrix tuple, not a claim of the exact optimum.
It already excludes any family-independent transfer constant in (2)
for this substitution. Under the endpoint decoder A=X_0,B=X_N, the
source energy is 1/2 on these very tuples. The required constant is at
least of order N^2. The positive source word telescopes through N path
relators, and (1) gives exactly N^2 for that word, matching the order of
the obstruction.

Take N=2^n. An exact fair-bit sampler first chooses positive/negative
with one bit and, on the positive branch, chooses i with n bits. A row
decoder uses only increment and endpoint naming. Variable and requirement
identifiers have O(n) bits; width stays two. Consequently all the stated
efficient succinct access requirements can hold while a constant source
gap becomes exponentially small in the succinct input length.

The same phenomenon occurs in dimension two, so choosing a finite exact
dimension, excluding exotic infinite-dimensional traces, or bounding
witness dimension cannot repair this particular transport failure.

## 3. What the primary results do and do not supply

Primary sources were rechecked on 2026-09-20.

* [Slofstra, arXiv:1703.08618v2](https://arxiv.org/pdf/1703.08618),
  Lemma 2.2, gives a constant for restriction along a fixed homomorphism
  between fixed finite presentations. Theorem 1.2 uses a recursively
  presented family with qa-perfect iff qc-perfect, in the word-problem
  orientation. Theorem 1.3 gives, for each prescribed computable runtime
  function, a family whose exact q-perfect decision problem exceeds that
  bound and has q-perfect iff qc-perfect. Corollary 1.4 deduces global
  undecidability by a runtime diagonal argument. This is not a stated
  uniform HALT-positive constant-gap reduction. In particular, one cannot
  simply read such a reduction out of the word "undecidable."
* [Culf--Mastel, arXiv:2410.21223v2](https://arxiv.org/html/2410.21223v2),
  introduction and Sections 2.3, 8, explicitly organize soundness through
  weighted algebra maps and constant defect bounds. Their perfect-gap
  succinct 3-colouring source is relevant, but its forbidden projection
  relations are not supplied by (1), which starts with word identities.
* [Paddock--Slofstra, Section 5](https://arxiv.org/html/2310.07901#S5),
  especially Proposition 5.8, identifies the LIN tracial-versus-CE gap
  with the finitely presented nonhyperlinear-group question. It does not
  provide a generic projection-algebra-to-group embedding.
* [Taller--Vidick v2](https://arxiv.org/html/2507.22444v2#S1) explicitly
  distinguishes its imperfect-completeness reduction from the missing
  perfect-completeness endpoint and discusses the generic algebra-map
  obstruction. Nothing above upgrades its completeness.

The existing `group-corner-decoders-split-into-coset-and-matrix-readouts`
does give genuinely non-affine readouts of any already chosen perfect
M_d model through a finite Heisenberg corner. That avoids the affine
support obstruction, but is model-dependent: it does not choose d and
the model from a HALT instance, extend arbitrary matrix models of a
uniform target presentation, or supply the weighted estimate (2).
This audit does not refute more sophisticated non-literal readouts.

## 4. Bounded conclusion

The candidate shortcut tested here fails: exact representation-level
equivalence plus dimension-uniform approximation estimates plus succinct
bounded-width presentation do not imply a uniform matrix-energy gap.
Equations (4)--(6) are a concrete countermodel with all those elementary
features. The positive replacement is the explicit weighted certificate
(1), together with completeness and a valid decoder, not an unquantified
appeal to an embedding theorem.

No proposed theorem in the maintained graph is refuted by this note:
the completed LPC compiler already proves constants uniform in row width
and is not the growing path construction. No HALT-positive source was
constructed, and no claim about a failure of Culf--Mastel's weighted
reductions is made. This is a calibration for the missing upstream
non-literal groupification, kept in notes to avoid duplicating the
existing general embedding and decoder boundaries.

Root review checked the weighted telescoping calculation, exact marked
Tietze elimination, normalized two-dimensional reflection energies,
and succinct sampling description. No repair was required. This is
internal proof review, not a formalized or externally refereed result.
