# Swarm attack on qd-nuclear-algebra-with-qd-trace-positive-singular-class (2026-09-16)

Agent lane: `swarm-qd-nuclear-algebra-with-qd-tra`.  The hole was locked with
`bin/cairn lock` for the attack and unlocked at the end.  Nothing was
committed.  The outcome is a reduction plus an obstruction to one construction
family.  The hole remains open.

## 1. Setup

**Target (open).**  There are a separable, unital, nuclear, quasidiagonal `A`
and `x in K_0(A)` with `Zx cap K_0^+(A) = {0}` and `(Tr (x) tau)(x) > 0` for
every quasidiagonal tracial state `tau`.  Call such an `A` a *witness*.  It
refutes STW Problem VII (`stw07-qd-trace-positive-class-kills-qd-extension`).

Notation:
- `T(A)` is the tracial state space and `T_qd(A)` the set of quasidiagonal
  tracial states (Brown's definition).
- `tau_*` is the state induced on `(K_0(A), K_0^+, [1])`.
- `r_A: T(A) -> R^(K_0(A))`, `tau -> tau_*`, with the product topology.

Established inputs used:
- `stw07-singular-classes-change-sign-or-sit-on-boundary` (Theorem C of
  `research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md`): on a
  unital exact stably finite algebra a singular class is never strictly
  one-signed on `T(A)`.
- `stw07-trace-obstruction-forces-nonqd-trace-and-non-uct` (Theorem E): a
  witness has a nonquasidiagonal trace and a non-UCT trace-kernel quotient.
- `blackadar-rordam-haagerup-k0-states-are-traces`.
- Classical: Künneth theorem for the bootstrap class, Connes' uniqueness of
  `R`, uniqueness of the normal trace on a finite factor, Krein--Milman,
  Hahn--Banach in `R^G`.
- Gabe, arXiv:1511.02760v1, abstract read 2026-09-16: every amenable trace on
  a separable exact quasidiagonal UCT algebra is quasidiagonal.

## 2. What was proved

Full proofs are in
`research/artifacts/qd-trace-positive-class-k0-state-form-2026-09-16.md`.

### 2.1 Theorem 1: K_0-state form

Node `qd-trace-positive-class-iff-k0-state-off-qd-traces`, route
`...-proof`, which requires Theorem C.

For `A` separable, unital, exact and quasidiagonal, the following are
equivalent:
- (a) a singular class positive on `T_qd(A)`;
- (b) a class positive on `T_qd(A)` and negative at some trace;
- (c) `r_A(T(A)) != r_A(T_qd(A))`.

The separated trace can be taken extreme with `pi_sigma(A)'' ≅ R` when `A` is
nuclear.

Key steps:
- `T_qd` is closed and convex.
- (a) => (b): Theorem C and `y = Nx - [1]`.
- (c) => (b): strict separation in `R^(K_0)`.  Continuous functionals there
  are finite combinations of coordinates, the coefficients are made rational
  using `|tau_*(g)| <= n`, and denominators are cleared.
- (b) => (a): positivity of states excludes `m >= 1`, and nonemptiness of
  `T_qd` excludes `m <= -1`.
- Extreme form: Krein--Milman.  A type I_k GNS closure would make `sigma` a
  matrix trace.

With Blackadar--Rørdam--Haagerup, the hole asks for the K_0-states of
quasidiagonal traces to form a proper subset of the K_0-state space.  With
Gabe, a witness itself fails the UCT.  That is not implied by Theorem E, which
concerns a quotient, nor does it imply Theorem E.

### 2.2 Theorem 2: bootstrap tensoring

Node `bootstrap-tensoring-cannot-create-qd-trace-positive-class`, route
`...-proof`, which requires Theorem 1.

For `A` and `D` separable, unital, nuclear and quasidiagonal with `D` in the
bootstrap class, `A (x) D` is a witness iff `A` or `D` is.  By Gabe, `D` never
is.  So `A (x) D` is a witness iff `A` is.

Key steps:
1. The Künneth cokernel is torsion.
2. External products of K_1-classes are invisible to every trace: they are
   pushed forward from a rank-zero class on `T^2`.
3. Extreme traces of `A (x)_min D` are product traces.  The GNS closure is a
   factor, the left leg is a finite factor, and `w(. pi(1 (x) d))` is a normal
   tracial functional on it.
4. Replace each factor trace by a quasidiagonal one with the same K_0-state,
   then apply Krein--Milman.

Consequences:
- a witness may be assumed `Z`- and `Q`-stable;
- `A x|_(Ad w) Z ≅ A (x) C(T)` gives nothing new;
- tensoring a nonquasidiagonal-trace non-witness with such a `D` never makes
  `K_0` separate traces.

### 2.3 Proposition 3: trace-separating K_0

Route `qd-trace-positive-class-from-k0-separated-nonqd-trace` into the target,
requiring Theorem 1 and the new hole
`trace-separating-k0-nuclear-qd-algebra-with-nonqd-trace`.

If `r_A` is injective, a witness is the same as a nonquasidiagonal trace.
Real rank zero implies injectivity, and injectivity passes to quotients.

### 2.4 Proposition 4: extreme normal form and the IX(1) dichotomy

In the artifact; no node.  Let `A` be a witness with separated extreme `sigma`
and `B = A/J_sigma`.
- `B` is prime and nuclear, with a faithful extreme nonquasidiagonal trace
  separated from `T_qd(B)` by `q_* y`.
- Either `B` is quasidiagonal, and is then a prime witness, or `B` refutes
  STW IX(1).

This is recorded in the artifact only, because it adds no new named
proposition beyond Theorem E.

## 3. Approaches tried and where each dies

The hole needs a nuclear quasidiagonal algebra with a nonquasidiagonal trace
(Theorem E).  None is known, and by Gabe any such algebra fails the UCT.  So
every construction below was examined as a *transfer mechanism*: given some
algebra with a nonquasidiagonal trace, can a separating class be manufactured?

1. **Tensoring with bootstrap-class algebras** to enlarge `K_0`.  Dies by
   Theorem 2.  The new classes are torsion-rational combinations of external
   products.  Even products see only the K_0-states of the factors, and odd
   products see nothing.
2. **Interval, dimension-drop, pullback and gluing algebras**
   `E ⊆ C([0,1], F)`.
   - The projection-trace value `tau(p(t))` is constant along the norm
     continuous path `p(t)`.  So `(tau o ev_t)_* = (tau o ev_0)_*` on `K_0(E)`,
     and this is the K_0-state of a trace of the endpoint algebra.
   - Dies when the endpoint algebras have only quasidiagonal traces.
   - More structurally, homotopy domination preserves "all amenable traces
     quasidiagonal" (Shulman, arXiv:2508.00125v5, application 2; repo node
     `stw10-homotopy-domination-preserves-amenable-qd`), and homotopy
     invariance holds under a faithful amenable trace (Neagu,
     arXiv:2211.01666v1).  So homotopy-type constructions cannot even create
     the nonquasidiagonal trace.
3. **Mapping tori.**  For `Ad(e^(2 pi i h))` the mapping torus is `C(T, A)`,
   which is covered by item 1.  For non-inner automorphisms the new K_0-classes
   come from `K_1` and have trace values given by de la Harpe--Skandalis
   determinants.  No separating example was found.  Not a no-go.
4. **Crossed products by `Z`.**
   - Inner: `A (x) C(T)`, covered by item 1.
   - Approximately inner or outer: the Pimsner--Voiculescu classes from
     `ker(1 - alpha_*)` again have determinant-type trace values.
   - Invariant traces of the crossed product restrict to invariant traces of
     `A`.  A separating class would need the determinant to separate a
     nonquasidiagonal invariant trace from all quasidiagonal invariant ones.
   - No candidate automorphism found.  Open direction, not a no-go.
5. **Free products.**  Unital full free products are non-nuclear except in
   degenerate cases such as `C^2 * C^2`.  That one is subhomogeneous, so it
   satisfies the UCT and all its traces are quasidiagonal.  Dies at
   nuclearity.
6. **Infinite tensor powers and Bernoulli shifts.**
   - **Reduction to finite powers (proved here).**  Every class of
     `A^(x) infinity` comes from some finite power `A^(x) n`.
     - Every quasidiagonal trace `tau` of `A^(x) n` extends to the
       quasidiagonal trace `tau (x) rho (x) rho (x) ...` for any
       `rho in T_qd(A)`.  It is quasidiagonal on every finite stage by
       Lemma 1.4, and Arveson extension of the stage models gives models on
       the limit.
     - Quasidiagonal traces of the limit restrict to quasidiagonal traces
       (Lemma 1.3).
     - With condition (b) of Theorem 1, `A^(x) infinity` is a witness iff some
       `A^(x) n` is.
   - Finite powers are not settled: Theorem 2 needs a bootstrap factor, and
     `A` is not one.
   - Bernoulli crossed products `A^(x) Z x| Z`: the new Pimsner--Voiculescu
     classes need shift-invariant `K_1`-classes, and none giving separation
     was found.
   - Examined, no separation.
7. **Twisted or averaged inductive limits.**  Connecting maps that average over
   automorphisms preserve K_0-states of limit traces, in the examples checked.
   No separation.
8. **Direct sums.**  `A (+) B` is a witness iff `A` or `B` is.  `T_qd` of a
   direct sum is the convex hull of the summands' `T_qd`, `K_0` splits, and
   the K_0-state records the weight `t` and each summand's state.  Dead.
9. **Index classes of extensions.**  For `0 -> I -> E -> A -> 0`, classes in the
   image of the index map from `K_1(A)` vanish in `K_0(E)` after pushing
   forward.  They are therefore invisible to bounded traces on `E`.  Dead as a
   source of separating classes on `E`.
10. **Real rank zero directly** (the new hole).  Dies at the UCT.  An instance
    would be a nuclear algebra known to fail the UCT, and none is known
    (`nuclear-algebra-without-uct-exists` is open).

Honest scope:
- Items 1, 2, 8 and 9 are proved obstructions for their families.  Item 2's
  first part is proved only for endpoint algebras with quasidiagonal traces.
- Item 6 contains a proved reduction, from infinite to finite tensor powers.
- Items 3, 4, 7 and the rest of item 6 are examined examples without an
  impossibility theorem.

## 4. Literature consulted (all dates of access 2026-09-16)

- N. P. Brown, M. Dadarlat, *Extensions of quasidiagonal C\*-algebras and
  K-theory*, arXiv:math/0008182v1 (2000-08-23).  PDF text read.
  - Theorem 4.11 is the class-wide equivalence between the QD extension
    property and the K_0-Hahn--Banach property.
  - Theorem 4.12 gives the implications for individual algebras.
  - No real rank zero statement relevant to separation.
- J. Gabe, *Quasidiagonal traces on exact C\*-algebras*, arXiv:1511.02760v1
  (2015-11-09; J. Funct. Anal. 272 (2017)).  Abstract read.  Used for
  "amenable traces on separable exact quasidiagonal UCT algebras are
  quasidiagonal".
- I. Moutzouris, *Extensions of quasidiagonal C\*-algebras and controlling the
  K_0-map of embeddings*, arXiv:2112.03224v3 (2021-12-06).  Already imported in
  the repository (`moutzouris-singular-subgroup-has-vanishing-trace`).
  Consulted for context only.
- M. Moradi, M. Amini, *On locally finite-dimensional traces II*,
  arXiv:2606.13924v1 (2026-06-11).  Unrefereed; HTML proof sketch of
  Theorem 2.10 read: quasidiagonal traces form a face.  Context only, not used
  in any proof.
- N. Ozawa, *The hyperfinite II_1 factor is not quasidiagonal*,
  arXiv:2609.08892v1 (2026-09-08).  Abstract; already in the repository.  `R`
  is not exact, so this gives no nuclear example.
- T. Shulman, *Homotopy lifting, asymptotic homomorphisms, and traces*,
  arXiv:2508.00125v5 (2025-07-31).  Abstract read (application 2: homotopy
  domination and amenable traces).
- T. Shulman, *Sections and cones*, arXiv:2507.22783v3 (2025-07-30).  Listing
  only.
- R. Neagu, *A note on when amenable traces are quasidiagonal*,
  arXiv:2211.01666v1 (2022-11-03).  Abstract read (homotopy invariance).
- S. Hua, S. White, *Uniqueness for embeddings of nuclear C\*-algebras into
  type II_1 factors*, arXiv:2601.08779v2 (2026-01-13).  Abstract read.  UCT
  setting, not relevant to a witness.
- V. I. Paulsen, M. Rahaman, E. Samei, *Amenable traces and the joint numerical
  radius*, arXiv:2606.18369v1 (2026-06-16).  Abstract read.  Not relevant.
- Listing only, not relevant: J. Bell, arXiv:2604.18410v2; B. Jacelon,
  R. Neagu, arXiv:2506.18352v2.
- C. Schafhauser, S. White, A. Tikuisis, *Nuclear C\*-algebras: 99 problems*,
  arXiv:2506.10902v2.  Problems VII, IX(1), X(1) through the repository's
  ingested nodes.
- Standard, not re-fetched:
  - Künneth theorem for the bootstrap class (Schochet 1982; Rosenberg--Schochet,
    Duke Math. J. 55 (1987); Blackadar, *K-theory for operator algebras*, §23);
  - Connes' uniqueness of the injective II_1 factor;
  - uniqueness of the normal trace on a finite factor (Kadison--Ringrose);
  - gauge-invariant uniqueness for `Z`-crossed products.
- Bounded arXiv API searches (2026-09-16):
  - `abs:quasidiagonal AND abs:trace`;
  - `abs:quasidiagonal AND abs:"real rank zero"` (newest hit 2017);
  - `abs:"quasidiagonal trace"` (only 2606.13924);
  - `abs:nonquasidiagonal` (no hits).

  No construction of a nuclear quasidiagonal algebra with a nonquasidiagonal
  trace was found.

## 5. Files

- `research/artifacts/qd-trace-positive-class-k0-state-form-2026-09-16.md`
  (proofs)
- `research/qd-trace-positive-class-iff-k0-state-off-qd-traces.md` (claim) and
  `research/qd-trace-positive-class-iff-k0-state-off-qd-traces-proof.md`
  (route)
- `research/bootstrap-tensoring-cannot-create-qd-trace-positive-class.md`
  (claim) and
  `research/bootstrap-tensoring-cannot-create-qd-trace-positive-class-proof.md`
  (route)
- `research/trace-separating-k0-nuclear-qd-algebra-with-nonqd-trace.md` (new
  hole)
- `research/qd-trace-positive-class-from-k0-separated-nonqd-trace.md` (route
  into the target)

## Referee (2026-09-16)

Adversarial referee pass before landing.

**Checked line by line.**
- Theorem 1 (artifact §2): closedness and convexity of `T_qd` (the
  multiplicities `p l_n`, `(q-p) k_n` give normalised trace
  `t tr phi + (1-t) tr psi`); strict separation in `R^(K_0(A))` with the dual
  of a product of lines being finite coordinate combinations; the rational
  perturbation keeps a gap `>= delta/3` on `C` and at `s_0`; `y = Nx - [1]`;
  singularity of `y` in (b) => (a); the extreme normal form (tracial GNS
  vector is separating, so the factor argument works; an `M_k` GNS closure
  makes `sigma = tr o pi_sigma` quasidiagonal; nuclear gives injective, then
  Connes).  No gap found.
- Theorem 2 (artifact §3): the external-product naturality
  `[u] × [v] = (phi_u (x) phi_v)_*([z] × [z])`, evaluation at a point killing
  `[z] × [z]` since `K_1(C) = 0`, and the integration
  `(Tr (x) omega)((id (x) Phi)(P)) = int rank P(t) d nu(t)` for the positive
  functional `nu = (Tr_(nk) (x) omega) o Phi` on `C(T^2)`.  Lemma 1.5 (extreme
  traces of `A (x)_min D` are products): the left leg is a finite factor and
  `x -> w(x pi(1 (x) d))` is positive (via `x^(1/2)` commuting with `h`),
  normal and tracial.  Künneth for `D` in the bootstrap class with arbitrary
  `A` (Rosenberg--Schochet 1987; Blackadar §23) has Tor cokernel, torsion.
  Sound.
- Proposition 3, Proposition 4, the inner crossed-product isomorphism
  (covariance `(w (x) z)(a (x) 1)(w (x) z)* = waw* (x) 1`, gauge-invariant
  uniqueness for injectivity) and the infinite-tensor-power reduction in §3
  item 6.  Sound.
- `bin/cairn search --similar` on all three new claims: no duplicate.

**Citations spot-checked.**
- Gabe arXiv:1511.02760v1 abstract fetched: "any amenable trace on a
  separable, exact, quasidiagonal C*-algebra in the UCT class is
  quasidiagonal".  Matches the use.
- Moradi--Amini arXiv:2606.13924v1 abstract fetched: "quasidiagonal traces
  form a face of the trace simplex".  Matches (context only).
- Neagu arXiv:2211.01666v1 abstract fetched: homotopy invariance of "all
  amenable traces quasidiagonal" for separable exact algebras with a faithful
  amenable trace.  Matches.

**Changes made.**
- `trace-separating-k0-nuclear-qd-algebra-with-nonqd-trace`: the
  `distinct_from` entry for `bk-rr0-uct-stably-finite-algebras-are-qd` said
  that claim "proves" its statement; it is OPEN.  Corrected.
- Artifact Lemma 1.4: the defect bound had `||aa'||` where `||a|| ||a'||` is
  needed; fixed and the identity behind the bound written out.
- Claim bodies of `qd-trace-positive-class-iff-k0-state-off-qd-traces` and
  `bootstrap-tensoring-cannot-create-qd-trace-positive-class`: the
  consequences using Gabe's theorem (not a graph node) are now explicitly
  marked as remarks outside the certificate of the routes.

**Scope caveats.**
- Deep classical inputs in the two routes are cited, not re-proved: Künneth
  theorem, Connes' uniqueness of `R` (only for the "isomorphic to `R`" clause),
  Choi--Effros (nuclear gives injective bicommutant), uniqueness of the normal
  trace on a finite factor.
- §3 item 2 (interval/gluing algebras) is proved only for subalgebras
  `E ⊆ C([0,1], F)` containing `C[0,1] (x) 1` whose interior fibres are all of
  `F`, so that extreme traces are point traces `tau o ev_t` with `tau in T(F)`
  for interior `t`.  It is not an impossibility theorem for general gluings.

**Verdict.** Theorems 1 and 2 and the reduction route are sound; landed with
the small fixes above.  The target hole remains OPEN, and so does the new,
stronger hole `trace-separating-k0-nuclear-qd-algebra-with-nonqd-trace`.
