---
rg: 2
id: gauge-components-circle-sphere-proof
kind: route
title: Run the factorial gauge sequence on an odd-cell base and read the commutator through the degree-one collapse
target: gauge-components-over-circle-sphere-towers
requires:
  - stw59-exact-factorial-unitary-component-groups
  - samelson-circle-sphere-product-has-order-n
artifacts:
  - research/artifacts/stw59-nonabelian-unitary-component-groups-2026-09-11.md
---

Use the factorial proof's principal bundle G(E) -> G(E+1) -> S(E+1), with
pi_0 S = 0 and pi_1 S = H^(2r)(X;Z) = Z. It needs only dim X = 2r. Its
stable identifications pi_0 G(E+1) = K^1(X) and pi_1 G(E+1) = K^0(X)
hold for every finite complex, and here K^1(X) = Z^2 tensor K^0(Y) is
nonzero. This gives the extension of K^1(X) by Z/im(epsilon_*).

The Euler formula (4.5) is unchanged. In K^0(X) = K^0(Y) + q^*kappa K^0(Y)
the class q^*kappa has integral generating Chern character because the
collapse q has degree one, so the image is n! Z, as over S^(2n).

The kernel is central: conjugating a lift of a section loop by a gauge
unitary fixing the unit section lifts the translated loop. That loop has
the same relative Euler number, since the unitary preserves complex
orientation and local indices.

The pullback along Q = q x id maps the two fibrations compatibly, is an
isomorphism on H^(2r), and meets images n! Z on both sides. So it carries
the factorial group isomorphically onto the kernel.

The commutator of u and v factors through q as <alpha,omega>. The
prerequisite Samelson claim gives order n at Y = pt. Tautological blocks
multiply section-loop integers by ±1, so they are isomorphisms on
kernels. On K^1 they are split pr^*, so the five-lemma argument makes
them injective on components.
