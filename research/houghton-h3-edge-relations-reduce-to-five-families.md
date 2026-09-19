---
rg: 2
id: houghton-h3-edge-relations-reduce-to-five-families
kind: claim
title: "With three rays, every edge relation and every letter-on-edge relation costs at most two five-family relators plus linear area"
artifacts:
  - experiments/houghton-h3-theorem-a-2026-09-17/verify_theorem_a.py
  - experiments/houghton-h3-theorem-a-2026-09-17/verify_theorem_a.out
distinct_from:
  houghton-group-h3-has-polynomial-dehn-function: that is the polynomial bound for H_3; this is only the three-ray edge layer, which reduces the edge relations to the five families and bounds nothing absolutely.
  houghton-groups-with-six-or-more-rays-have-polynomial-dehn: its route proves the edge relations for n >= 6 through pours on free auxiliary rays; this treats n = 3, where no free ray exists, and keeps the families as black boxes.
  houghton-dehn-polynomially-equivalent-to-commutation-area: that reduces the Dehn function of every H_n to the commutation area A; this reduces the edge relations of H_3 to five explicit families.
---

Conventions are those of `research/artifacts/zp-houghton-pours-2026-09-17.md` (§0 and
§4), with `n = 3`:

- `P` is the finite presentation of §0 there, and `Q ⊂ P` is the set of all trivial
  words of length `<= 40` in `λ_xy^(±1), τ_x^(±1)`;
- `c` is any route function (`c(x) != x`), `Ed` is the edge-word map of §4 for `c`,
  and `D^u_x(k) = λ_xu^k τ_x λ_ux^k`.

The five literal families are:

| family | word |
|---|---|
| `F_3(k)` | `[τ_x, D^(c(x))_x(k)]` |
| `R_3(k)` | `D^u_x(k) · D^v_x(k)^(-1)`, with `{x,u,v} = {1,2,3}` |
| `B_3(i,j)` | `[Ed t_x(i), Ed t_y(j)]`, with `x != y` |
| `C_3(j)` | `[Ed σ_{x,y}, Ed t_z(j)]`, vertex-disjoint |
| `D_3(j)` | `λ_wz · Ed(t_x(j)) · λ_zw · Ed(t_x(j))^(-1)`, with `{x,z,w} = {1,2,3}` |

Let `Φ(k)` be the largest `Area_P` of a member with all indices `<= k`.

**Claim.** For every route function `c` and every `R >= 1`:

1. Every edge relation (E1), (E2), (E3) of §4, for edges of depth `<= R`, has area
   `<= Φ(R) + 30R`. Each derivation uses `Q` together with at most one family relator:
   - (E1) and (E3) use none;
   - (E2)(i) uses `F_3(|j-i|)`;
   - (E2)(ii) uses `B_3`, and (E2)(iii)/(iv) use `C_3`;
   - (E2)(v) has no instance, because three top vertices admit no two disjoint top
     edges.
2. For every letter `s = λ_zw` and every edge `e` of depth `<= R`, exactly one of the
   two alternatives of Lemma 4.2 holds:
   - the first, where `e' = e^s` is an edge, with
     `Area(s^(-1) Ed(e) s Ed(e')^(-1)) <= 2Φ(R) + 30R`;
   - the second, `e = σ_{w,y}` with `y != z`, at cost `<= 16`.

   The families used are `D_3(j)` for `e = t_x(j)` with `x ∉ {z,w}`, and two
   `R_3`'s of index `<= R` for `e = t_z(j)` (`j >= 2`) or `e = t_w(j)` when
   `c(e's ray)` is the third ray. Every other case costs `O(R)` from `Q` alone.

Consequently the three-ray hulls of the swarm's Theorem A (wave 10, A.2 and A.3) hold
in the sharper form `E(R) <= Φ(R) + 30R` and `Λ(R) <= 2Φ(R) + 30R`. The fourth ray
that the six-ray note uses in Proposition 4.1(ii)–(iv) and in Lemma 4.2, case 1, is
never needed.

The machine check covers all 8 route functions and all edges of depth `<= 20`, 31680
relations in all. It derives each relation step by step and verifies every step
independently. It measures at most `8R + 2` `Q`-steps per relation, not counting the
family relators.
