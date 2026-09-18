---
rg: 2
id: shell-envelope-fp-forces-fp-germ-group-proof
kind: route
title: Push the Schreier complex of the point stabilizer into the V germ groupoid with free hat loops, and kill the neighbourhood kernel by disjoint-support commutation
target: shell-envelope-fp-forces-fp-germ-group
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
  - shell-germ-group-has-index-two-fiber-product
  - shell-germ-fp-is-an-ascending-hnn-gate
artifacts:
  - research/artifacts/shell-envelope-germ-necessity-2026-09-18.md
---

Full proof in the artifact, Steps 1-5. Summary:

1. **Groupoids.** G_V is the germ groupoid of V on the singular orbit Omega. It
   is transitive, with isotropy <tau> = Z at p. Every generator of V, and every
   hat(s) at every point other than p, has its germ in G_V. Adjoin free loops
   sigma_s at p to get Pi, with isotropy Z * F(S) at p.
2. **Schreier complex.** Let Y_R be the Cayley 2-complex of a finite presentation
   <Y u hat(S) | R>, divided by St(p). Then pi_1(Y_R, p) = St(p). Send an edge to
   sigma_s when it is hat(s) at p, and to its actual G_V germ otherwise.
3. **Finitely many relator loops.** A relator cell based at x either never applies
   a hat letter at p, and then maps to the trivial germ of the relator at x, or it
   maps to a G_V conjugate of a word w_(r,x) in tau and sigma. Only finitely many
   x occur for each relator: one for each hat position. With W_R the set of these
   words, Phi: St(p) -> Q_R = (Z*F(S))/<<W_R>> is a surjective homomorphism lifting
   the germ map.
4. **Neighbourhood kernel.** Let l be trivial near p and w a word for it. Pick
   p' near p avoiding the finitely many points where w applies a hat letter at p,
   and c in V supported near p with c(p) = p'. Then l = c^-1 l c, and the word
   c^-1 w c never applies a hat letter at p. So Phi(l) is the G_V germ of l at p,
   which is trivial.
5. **Conclusion.** Q_R -> Q is injective, so Q = <tau, S | W_R>. The displayed
   consequences follow from the two imported fiber-product and gate claims.
