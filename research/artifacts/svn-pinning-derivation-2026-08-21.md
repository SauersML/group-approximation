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

## C. The computable loop

The S_3 hexagon: transport around
    T_{h'} vs T_h o T_{h''}^{-1}
on a fixed band of pi_{k,s} with k >= 3.  Every edge transport
appears once forward and once backward in the comparison scalar

    flux(k, s) = scalar of ( T_{h'}^* T_h T_{h''}^{-1} )

restricted to the common band, so all three edge phases cancel and
the scalar is canonical.  The Gauss sums enter through the
multiplicity cut: the h'-leg and the (h, h'')-composite leg select
their slots through quadratic exponential sums over the corner
coordinate (the e_13-direction carries the p^2 central shift on one
route and two single shifts on the other; matching the two slot
selections is a level-p^2 vs level-p Gauss-sum comparison, and the
Weil-Rao normalization gives gamma-quotients = Hilbert symbols).
Numerically ALL of this is solvable without closed forms: each leg
transport = min-singular-vector of its own intertwining system
(Heisenberg constraints + parahoric normalizer constraints), each
polar-normalized; the hexagon scalar is then convention-free.
Nontriviality witnesses (must both hold or the run is void):
(i) each leg's intertwining residual < 1e-10 with Schur gap > 0.1;
(ii) replacing the parahoric constraints by NOTHING must reproduce
a multiplicity ambiguity (Schur gap ~ 0), proving the constraints
are load-bearing.
Prediction under the flux identification: hexagon scalar = -1 at
p = 3, +1 at p = 5 (and +1 at p ≡ 1 mod 4 generally); any level
k >= 3, stable in k.

## D. What remains cited (unchanged)

The identification of the hexagon scalar with the Matsumoto/
Steinberg class and the orbit-method density of oscillator bands in
the regular decomposition remain cited-level steps of
`lambda-exact-p-three-closure-route`; this artifact replaces only
the "SvN-pinning write-up" dependency with an explicit derivation
and a falsifiable instrument design.
