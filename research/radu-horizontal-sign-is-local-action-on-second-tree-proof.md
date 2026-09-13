---
rg: 2
id: radu-horizontal-sign-is-local-action-on-second-tree-proof
kind: route
title: Compute the horizontal letters 2-adically on the star of the S_3-vertex, then factor K through the Zappa-Szep decomposition Q = W C
target: radu-horizontal-sign-is-local-action-on-second-tree
requires:
  - radu-horizontal-quotient-is-arithmetic-lattice
  - radu-metabelian-quotient-embeds-in-edge-lamp-wreath
  - radu-horizontal-projection-kills-delta-squared
artifacts:
  - research/artifacts/radu-h4-star-check.py
  - research/artifacts/radu-h4-star-check-part2.py
  - research/artifacts/radu-h4-star-check-output-2026-09-13.txt
---

# Proof

**Item 1 (computation).** `radu-h4-star-check.py` reruns the exact quaternion setup of
`radu-second-tree-check.py`: structure constants over `F`, the elements `β_s` from Skolem–Noether,
and a matrix model at `𝔮'` to precision `2^70`. The one difference is that its part 2 treats the
letters `a, b, c`. On MSI, 2026-09-13, it prints:

* `M_c ~ M_y M_b M_y`; `a, b, c` are involutions; `v_2(tr^2/det) = 2` for `ab, bc, ca`. These agree
  with item 4 of the target of `radu-horizontal-quotient-is-arithmetic-lattice`.
* Exactly one vertex within radius 5 is fixed by `<xz, xyx>`, namely `p`.
* The neighbours of `p` are labelled `[p, xp] = [p, zp] = 0`, `[p, xy·p] = 2`, `[p, zy·p] = 1`.
* `d(p, M_h p) = 0` for `h = a, b, c`. On the neighbours, `a` acts as `[0,1,2]`, `b` as `[0,1,2]`,
  and `c` as `[0,2,1]`.

All distances are integers at most 10, far below the precision. The same combinatorics follows
from the automaton on `Y` (artifact `radu-edge-lamp-host-and-square-firewall-2026-09-13.md`,
Section 4). `C` preserves the fibre `S_3·o = {1, xz, xyx, xyz, zyx, zyz}`. `a` and `b` preserve its
`<xz>`-cosets, while `c` swaps `{xyx, xyz}` and `{zyx, zyz}`. The computation is what shows that
`C` fixes `p` itself.

**Item 2.**
* *Local sign.* By item 1, `C` acts on the star of `p` through `χ`. So `C ∩ Fix(star p) = C_χ`.
* *Structure of `K`.* Let `k ∈ K`, and write `k = wh` with `w ∈ W`, `h ∈ C`; the factorization
  exists because `Q = W·C` with `W ∩ C = 1`. Then `w = kh^(−1)` fixes `p` and acts on the star as
  `h^(−1)`, so `w ∈ S_3`. `S_3` acts faithfully on the star (`radu-horizontal-quotient-is-arithmetic-lattice`,
  proof Part 2), and `xz` acts as `(1 2)`. So `w = 1` if `χ(h) = 1` and `w = xz` if `χ(h) = −1`. Hence
  `K = C_χ ⊔ xz(C \ C_χ) = C_χ ⊔ xzc·C_χ`.
* *Free action.* `K ∩ W = 1`, and `W` is the stabilizer of the base vertex `v_h`, so `K` acts
  freely on `V(T_h)`.
* *Transitivity.* The two `C_χ`-orbits on `V(T_h)` are the vertices `h·v_h` with `χ(h) = ±1`.
  `xz` acts on `T_h` as the global substitution `a ↔ b` (`radu-horizontal-projection-kills-delta-squared`),
  so `xzc·v_h = c·v_h` lies in the odd orbit. So `K` is transitive.

**Item 3.**
* *Framed vertices.* `W` is transitive on `V(T')`, and `Stab_Q(p) ⊇ S_3` maps onto `Sym(star p)`.
  So `Q` is transitive on framed vertices, with stabilizer `K`.
* *Double cover.* `C_χ = C ∩ K` gives the diagonal embedding `Q/C_χ ↪ Q/C × Q/K`, with
  `Q/C = V(Y)` and `[K : C_χ] = 2`.
* *Soficity of the quotient.* Given orbit charts `π_s` for `Q/C_χ`, colour a framed vertex `x'` by
  the set `{π_s(x) : x ↦ x'}`. Distinct fibres are disjoint, so these sets are distinct, and they
  transform correctly. So `Q/K` is sofic whenever `Q/C_χ` is. ∎
