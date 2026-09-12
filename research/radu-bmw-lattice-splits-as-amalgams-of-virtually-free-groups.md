---
rg: 2
id: radu-bmw-lattice-splits-as-amalgams-of-virtually-free-groups
kind: claim
title: Radu's BMW lattice splits as P_y amalgamated with E_x over A_ev, and as V amalgamated with E_a over V_a
distinct_from:
  radu-bmw-coordinate-subgroups-are-sofic: that proves the letter subgroups P_y and P_xz sofic; this writes the whole lattice as an amalgam of virtually free vertex groups over a virtually free base, in both tree directions.
  radu-horizontal-projection-kills-delta-squared: that computes the kernel of the action on the horizontal tree; this computes the Bass-Serre splittings from both tree actions.
artifacts:
  - research/artifacts/radu-lattice-binary-algebra-splittings-2026-09-12.md
---

**ESTABLISHED** by `radu-bmw-lattice-amalgam-splittings-proof`.

Let `Gamma_R` be Radu's BMW lattice (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`), `A = <a,b,c>` and
`V = <x,y,z>`. Put:
* `A_ev = <a, b, cac, cbc>`, the kernel of the `c`-parity `A -> C_2`, isomorphic to `C_2^(*4)`;
* `P_y = A ⋊ <y>`, where `y` fixes `a` and swaps `b <-> c`;
* `E_x = A_ev ⋊ <x>`, where `x` fixes `a` and `b` and swaps `cac <-> cbc`;
* `V_a`, the index-three preimage of `{id, (b c)}` under the first-level action `V -> S_3` on the
  horizontal tree, with `x -> id`, `y -> (b c)`, `z -> (a b)`; it is isomorphic to `C_2^(*5)`;
* `E_a = V_a ⋊ <a>`.

Then

```text
Gamma_R = P_y *_(A_ev) E_x = V *_(V_a) E_a.
```

These are the Bass–Serre splittings from the actions on the vertical and horizontal trees, after
subdividing inverted edges. Consequently, for every commutative ring `k`,
`k[Gamma_R] = k[P_y] *_(k[A_ev]) k[E_x] = k[V] *_(k[V_a]) k[E_a]` as amalgamated coproducts of algebras.
