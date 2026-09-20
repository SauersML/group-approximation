---
rg: 2
id: deligne-uniform-scalar-models-have-a-level-free-third-floor
kind: claim
title: Uniform scalar, monomial and prime-to-three block-monomial one-third Maslov models of Sp4(Z) have defect bounded below independently of the level, including over non-Kahler classes
distinct_from:
  deligne-schreier-complexes-have-a-uniform-third-cellular-floor: that is the point-norm (finite-window cellular) floor and is still OPEN; this is the uniform (all-pairs sup) floor, where the non-Kahler integral classes that survive there cannot occur, because a uniformly small correction is a bounded class and H^2_b is one-dimensional.
  deligne-opnorm-monomial-models-are-almost-flat-circle-bundles: that kills spherical and Kahler-proportional classes with a cellular floor and leaves non-Kahler classes open; this kills every class, but only for defect measured on all pairs.
  deligne-parameter-group-is-a-virtual-invariant: that supplies the divisibility set {+-1,+-2} used here; this converts it, through H^2_b, into a quantitative level-free defect floor.
  deligne-maslov-tensor-functors-are-asymptotically-regular: its route remark is the conditional version of item (U1); this removes the condition (non-cocompact H^2_b) and adds (U2)--(U4).
  corona-defect-is-not-uniform: that says corona (point-norm) defects need not be uniform; this is a statement about uniform defects only and does not reach point-norm models.
---

**ESTABLISHED** (route `deligne-uniform-scalar-models-level-free-third-floor-proof`).

**Setting.** `Gamma = Sp_4(Z)`. `b'` is the bounded integral representative of the covering class, and
`nu_b = ||[b']_b|| > 0` is its Gromov norm, the same on every finite-index subgroup
(`sp4-lattice-bounded-cohomology-is-the-kahler-line`). `e(x) = exp(2 pi i x)`.

A map `U : L -> U(d)` has *uniform `theta`-defect* `eps` on a subset `L` closed under products if

```text
|| U(g) U(h) - e(theta b(g,h)) U(gh) ||_op <= eps     for ALL g, h in L.
```

This is invariant under replacing `b` by `b + delta k` with `k` integral, via `U -> e(theta k) U`. So the choice of
integral representative does not matter.

**Theorem.** Let `Lambda <= Gamma` have finite index. Let `theta in R/Z`, and write
`||theta||_(1/2) = dist(theta, (1/2)Z)`.

- **(U1) Scalar models.** A map `lambda : Lambda -> U(1)` of uniform `theta`-defect `eps < 1` satisfies

  ```text
  eps >= 4 ||theta||_(1/2) nu_b .
  ```

  At `theta = 1/3`: `eps >= min(1, (2/3) nu_b)`. The bound does not depend on `Lambda`.
- **(U2) Monomial models over any finite `Gamma`-set.** Let `U : Gamma -> U(d)` take monomial values
  (permutation matrix times diagonal unitary), with uniform `1/3`-defect `eps < sqrt 2` on `Gamma`. Then the
  permutation parts form a genuine action, and `eps >= min(1, (2/3) nu_b)`.
- **(U3) Block-monomial models with block size prime to three.** The same holds for block-monomial values with
  `r x r` unitary blocks and `3 not | r`, with floor

  ```text
  eps >= min( 2/(pi r), 4 nu_b /(3 pi r) ).
  ```
- **(U4) Consequences.** No sequence of uniform monomial `1/3`-models, and no sequence of uniform block-monomial
  `1/3`-models with blocks of bounded size prime to 3, has defect tending to 0. This holds even when the
  stabilizers change along the sequence with unbounded index. In the uniform category, the whole survivor list of
  w8 (changing stabilizers) and of w13 (non-Kahler classes `u = kappa mod 3` on congruence subgroups) is empty.

**Where the uniform floor stops, and why the point-norm floor is different.** The only property of `s` that the
proof uses is that the error cocycle `s` is bounded on all of `Lambda x Lambda`. Then `[s]` lies in
`H^2_b(Lambda) = R [b]`, so it cannot carry a non-Kahler class.

For a point-norm model, `s` is small only on a finite window. The class `[c]` can then be any integral class
`u = kappa mod 3`, and its correction need not be in the image of `H^2_b`. This is exactly the residue of
`deligne-schreier-complexes-have-a-uniform-third-cellular-floor`: non-Kahler classes are precisely the classes
outside `image(H^2_b(Lambda) -> H^2(Lambda;R)) = R kappa`. The gap between the two floors is the gap between the
cellular finite-window norm and the bar sup norm on all pairs. Triangles `(g, h, gh)` need unboundedly many
relator cells to fill.

Two cases are not covered: blocks of size divisible by three, and non-monomial uniform models.
