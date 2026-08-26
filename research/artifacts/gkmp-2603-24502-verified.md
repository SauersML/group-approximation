# Verification record: Gao-Kunnawalkam Elayavalli-Manzoor-Patchell

arXiv:2603.24502 "A new source of purely finite matricial fields", v1 25 Mar
2026, v2 26 Mar 2026 (v4 2 Apr 2026). Authors: David Gao (UCSD), Srivatsav
Kunnawalkam Elayavalli (UMD), Aareyan Manzoor (Waterloo), Gregory Patchell
(Oxford). Read from the arXiv HTML this session (2026-08-26).

## Definitions (verbatim sense)

G is MF: for all finite F ⊆ G, ε>0, there are d and u: G → U(M_d) with
‖u_gh - u_g u_h‖<ε on F, |tr(u_g)|<ε for g∈F\{1}, and the C*_r(G) norms of
combinations converge. PMF: the u can be actual homomorphisms. PFF: with
finite image. PPF: images finite permutation groups + standard irreps.
PPF ⟹ PFF ⟹ PMF ⟹ MF.

## Theorem 1.1 (verbatim)

Suppose G is an MF (resp. PMF, PFF) group and H<G is separable (i.e.
H = ∩_{i∈N} H_i where H_i<G are finite index subgroups). Let L be a
residually finite MF (resp. PMF, PFF) group such that either G or L is exact.
Then the amalgamated free product G *_H (H × L) is MF (resp. PMF, PFF).

## Corollary 1.2 (verbatim sense)

G MF, H<G separable ⟹ the group double G *_H G is MF (resp. PMF, PFF).
Moreover if G,H are PFF and one is exact, G*H is PFF.
Also noted: G *_H (H × Z) ≅ (*_H G) ⋊ Z, the infinite double of G over H with
Z permuting the copies.

## Corollaries 1.3, 1.4

1.3: arbitrary graph products of exact residually finite MF/PMF/PFF groups
are MF/PMF/PFF (generalizes Magee-Thomas RAAG result).
1.4: pi_1 of a non-positively-curved compact orientable aspherical
3-manifold is PFF; all virtually special groups are PFF. (Uses: virtually
special ⟹ subgroup of RAAG; quasi-convex subgroups of such are separable
[Haglund-Wise], fed into Cor 1.2.)

## Method

C*-free-independence / "selflessness" in matrix ultraproducts, after Ozawa
(Section 4.6 of Brown-Ozawa). Exactness essential (enters at the H×L tensor;
MF not known preserved by tensor products in general [18]). Uses MF/PMF/PFF
of F_n (Haagerup-Thorbjornsen; Bordenave-Collins) as a black box.

## Relevance to the finite-presentation MF-completeness program

Theorem 1.1 is a permanence theorem for the product edge G *_H (H × L), the
exact shape of the Higman-rope insertion edge. Two conditions to apply it to
a compiler on the INF branch: (i) the ambient/benign group G is MF and exact
(exactness is automatic: built from BS(1,m) and free groups by HNN and
amalgam, all exactness-preserving); (ii) the edge subgroup H is separable in
G. Chiodo-Vyas (arXiv, Torsion/TorLen) show the Aanderaa-Cohen Higman output
can be taken word-hyperbolic and virtually special; Haglund-Wise then give
separability of quasi-convex subgroups. The remaining mathematical gap is an
HNN-form of Theorem 1.1 (the rope uses a stable-letter twist, not literally
the amalgam) or an embedding of the rope output into such an amalgam.
