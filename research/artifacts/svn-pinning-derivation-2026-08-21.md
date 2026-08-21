---
rg: 2
id: svn-pinning-derivation-2026-08-21
kind: artifact
title: The Stone-von Neumann pinning of the band transports, derived correctly, with the failed-instrument autopsy
---

# The SvN pinning of the canonical band transports

Status: derivation artifact for the flux step of
`lambda-exact-p-three-closure-route`.  Records (A) the autopsy of the
two failed numerical instruments, (B) the correct finite model, (C)
the computable loop that measures the flux, (D) what remains cited.

## A. Autopsy of the failed instruments (methods doctrine)

1. **Plain-DFT loop (s3_weil_loop.py): VACUOUS.**  With V a
   row-orthonormal partial isometry, `Fm V Fa* (Fa V* Fm*) = I`
   identically; the reported scalar 1 was linear algebra, not
   physics.  The plain DFT satisfies `F^4 = 1` exactly -- no anomaly
   CAN appear without quadratic phases.  Diagnostic doctrine: any
   loop instrument must carry a nontriviality witness (an operator
   identity that would FAIL if the loop were algebraically forced).
2. **Levi-SL2 Weil loop (flux_two_prime_loop.py v1): WRONG FRAME.**
   Its own diagnostics rejected it (intertwining residual O(1),
   `w X w* ~ Z` at distance O(10), `w^4` non-scalar).  Root cause:
   in SL_3 NOTHING conjugates e_12 into e_23 inside the upper
   unipotent -- the Weyl elements move roots OUT of the upper
   triangle (w_13 e_12 w_13^-1 = e_32), so there is no Levi SL_2
   acting by a Weil representation on the Heisenberg of SL_3, and
   the u/l/w operator calculus transplanted from the symplectic
   picture does not model the S_3 loop.  The transport weights were
   also mis-imposed (both quadratic legs given the same scaling
   direction; the true Ad(h) weights on (e_12, e_23, e_13) are
   (+1, +1, +2), NOT symplectic (+1, -1)).

## B. The correct finite model

Fix p odd, level q = p^k.  H_k = Heisenberg over Z/q = the upper
unipotent of SL_3(Z/q), with generators x(a) = e_12(a), y(b) =
e_23(b), z(c) = e_13(c), relations [x(a), y(b)] = z(ab), z central.
For a faithful central character psi_s(c) = e(sc/q), gcd(s, p) = 1,
the SvN theorem gives ONE irrep pi_{k,s} up to equivalence, dim q,
model on l^2(Z/q):

    pi(x(a)) = shift by a,   pi(y(b)) = mult by e(s b x / q),
    pi(z(c)) = e(s c / q).

The three coweight transports act on H as (weights of Ad):
    Ad(h):   x -> x^p,  y -> y^p,  z -> z^{p^2}     (h = diag(p,1,1/p))
    Ad(h'):  x -> x^{1/p}, y -> y^{p^2}, z -> z^p   (h' = diag(1,p,1/p))
    Ad(h''): x -> x^{p^2}, y -> y^{1/p}, z -> z^p   (h'' = diag(p,1/p,1))
with h' = h h''^{-1} (the three-term relation).  Negative powers mean
the transport is PARTIAL (defined on the p-divisible part) -- these
are the parahoric leg maps; on band spaces they become partial
isometries.

The composite pi_{k,s} o Ad(g) is a rep of (part of) H_k whose
central character is psi_s composed with the z-weight: Ad(h) sends
the central character DOWN TWO LEVELS (z -> z^{p^2}: e(s p^2 c / q)
= e(s c / p^{k-2})), Ad(h') and Ad(h'') send it down ONE level.
By SvN each composite decomposes as a multiplicity space tensor the
standard irrep at the shifted level, and the CANONICAL TRANSPORT
T_g is the (Schur-unique up to phase) isometric intertwiner onto a
fixed irreducible band once the multiplicity is cut.  The
multiplicity cut is where the earlier scripts went wrong: it must be
performed by the AMBIENT lattice action (the parahoric subgroup of
SL_3(Z/q) that normalizes the leg), not by an imported symplectic
SL_2.  Concretely: the normalizer of the pair (leg data, central
character) inside SL_3(Z/q) contains the diagonal torus and the
OPPOSITE root groups e_21, e_32 in parahoric depth; their images
under pi_{k,s} generate the commutant coordinates that select a
unique irreducible multiplicity slot.

## C. The correct formal home: the Maslov triple index

Attempting to phase-pin the naive hexagon
`T_{h'}^* T_h T_{h''}^{-1}` fails: the three edge transports live on
DIFFERENT level pairs, the S_3 conjugations relate transports only
across levels, and each edge appears once, so a free phase
theta_h' + theta_h'' - theta_h survives.  The structural reason is
sharper and is the artifact's main finding: the DOUBLE-weight
direction of Ad(h) is e_13, of Ad(h') is e_23, of Ad(h'') is e_12 --
the "center" of the relevant Heisenberg data ROTATES around the S_3
hexagon.  The three legs use three different polarization-type data,
and the closed loop is a triple-intertwiner composite between three
pairwise-transverse realizations: exactly the Lion--Vergne /
Maslov-triple-index mechanism, whose composite scalar is the Weil
index gamma of the triple's quadratic form -- in the p-adic
normalization (Rao), a Gauss-sum quotient whose class computes
Hilbert symbols.  This is the correct derivation route for the
capstone's flux = (p,p)_p identification: not a Levi SL_2 (none
exists in the SL_3 unipotent frame -- section A), but the triple
index of the three coweight polarizations on the flag complex.

Two consequences.  (i) The ARITHMETIC ENGINE is testable in the
clean SL_2 setting: for product-one triples of SL_2(Z/p^k) elements
with invertible lower-left entries, the composite of the three
canonical metaplectic kernels (one fixed formula) is scalar by
Schur, and the scalar's 8th-root class is the Weil-cocycle triple
product; run identically at p = 3 and p = 5, the class difference
is the (-1|p) split.  Instrument: experiments/maslov_triple_flux.py
(witness-gated: kernels must intertwine the Weyl-symmetrized
Heisenberg operators phase-free at 1e-8, composite must be scalar
at 1e-8, else VOID).  (ii) The remaining derivation step for the
capstone is the DICTIONARY: expressing the S_3 hexagon of parahoric
band transports as a Maslov triple for an explicit quadratic form
over Z_p built from two coweight legs, so that the engine's
gamma-arithmetic evaluates the SL_3 flux.  This replaces the
"SvN-pinning write-up" dependency with one precisely-shaped lemma.

## C'. Engine CONFIRMED (2026-08-21, witness-clean)

The v3 instrument (verified primitives only: F0 with kernel
e(-ux/q)/sqrt(q), mult(t) = diag e(2bar t x^2/q), parity P; every
factor a fixed concrete matrix, witnesses phase-free against the
Weyl-symmetrized rho_W at 1e-15) measured the canonical anomaly word
A(1) = (F0 mult(1))^3 P, equal to the identity in SL_2(Z/q), hence
scalar by Schur with NO free phase anywhere.  Result, all witnesses
passing (nonscalarity ~ 1e-16, |scalar| = 1):

    q     9    27    81    243   25    125   625
    A(1)  +1   -i    +1    -i    +1    -1    +1

which is EXACTLY (2|q) * eps_q (Jacobi symbol times the Gauss sign,
eps_q = 1 for q = 1 mod 4, i for q = 3 mod 4) at every level -- in
particular -1 at q = 125 where q = 1 mod 4 separates the Jacobi
factor from the eps factor.  Control: F0^4 = 1 exactly (the plain
DFT carries no anomaly, consistent with the vacuous-instrument
autopsy in A).  CONCLUSION: canonical operator composites on the
finite oscillator models produce classical Gauss-sum classes on the
nose, with the p = 3 versus p = 5 arithmetic split operational.
The order-3 word (F0 mult(-1))^3 = +1 in SL_2 provides the second
class, measured witness-clean at every level, and the QUOTIENT is
the theorem-shaped output:

    A(+1)/A(-1) = (-1 | q)   exactly, at all seven levels:
    -1 at q = 27, 243 (p = 3, odd k); +1 at q = 9, 81, 25, 125, 625.

The Legendre class (-1|p) -- the capstone's (p,p)_p -- appears as a
canonical operator holonomy that ALTERNATES per tower level at
p = 3 mod 4 (Jacobi squares kill even levels) and is trivial at
every level for p = 1 mod 4.  This is exactly the shape the flux
mechanism requires: a per-level sign carried by depth-one legs, so
the depth-two h-route versus the (h', h'') hexagon split differ by
the class.  What remains is only the dictionary of C(ii).

## D. What remains cited (unchanged)

The identification of the hexagon scalar with the Matsumoto/
Steinberg class and the orbit-method density of oscillator bands in
the regular decomposition remain cited-level steps of
`lambda-exact-p-three-closure-route`; this artifact replaces only
the "SvN-pinning write-up" dependency with an explicit derivation
and a falsifiable instrument design.

## C''. Direct hexagon probe on the bare Heisenberg tower (p = 3, k = 4): slots are NOT cut

`experiments/hexagon_direct.py` solves the three leg transports
INTRINSICALLY (Heisenberg intertwining + psi-stable torus
equivariance, exact null spaces of the stacked systems) at levels
81 -> 27 -> 9.  Findings, all witness-clean:
* `V_h` (two-level, agnostic) is UNIQUE (null dim 1, next singular
  value 0.68) and is automatically the uniform transport -- the shift
  constraint wraps u mod 9 while x runs mod 81, coupling the three
  lifts; this confirms mechanism step (iii) exactly.
* `V_h'` and `V_h''` (one-level legs) each have a 2-DIMENSIONAL slot
  space; positivity of the kernel in the leg's own polarization frame
  leaves a 2-real-parameter cone and does not pin the slot.
* With any positive slots the hexagon is scalar on the band
  (nonscalarity 3e-12) with value +1: in a single model all legs can
  be chosen positive in one frame and compose FUNCTORIALLY, so no
  anomaly can appear -- exactly the vacuity mechanism of section A
  in a subtler guise.
(An earlier bookkeeping slip -- x(p) upstairs against y(p^2) at the
mid level, whose commutator is trivial -- made the h'-system
inconsistent; the correct h'-domain is x(1) -> x(1), y(p^2) -> y(p).)

CONSEQUENCE FOR OBLIGATION (ii), now stated precisely.  On a flat
tower a leg transport on an isotypic band of multiplicity m is an
element of `Hom(irrep (x) C^m, irrep' (x) C^m)` = (SvN intertwiner)
(x) U(m); flatness matches m but does not cut U(m).  The U(m) parts
are constrained only by the group elements that move BETWEEN bands
(the Weyl elements and the parahoric root groups outside the
Heisenberg), i.e. by the S_3 interlock in the FULL representation.
Obligation (ii) is therefore: around the hexagon the in-band U(m)
parts cancel (they are conjugated by the same interlock on both
routes), leaving the scalar Gauss class of C'.  The bare Heisenberg
model cannot test this; the test requires the flat tower's full
parabolic action, i.e. it is asymptotic (regular type), consistent
with the bounded-multiplicity floors measured at p = 2.  p = 5 was
not run (dense SVD infeasible at 15625 unknowns; a combinatorial
solver exists in principle but the conclusion above makes the bare
model's p = 5 value uninformative).
