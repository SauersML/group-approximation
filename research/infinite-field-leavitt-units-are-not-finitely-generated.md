---
rg: 2
id: infinite-field-leavitt-units-are-not-finitely-generated
kind: claim
title: Over an infinite field the Leavitt unit group and its scalar quotient are not finitely generated, and no finitely generated subring of a Leavitt algebra contains Q
distinct_from:
  char-zero-leavitt-unit-groups-have-congruence-kernels: that shows non-simplicity over finitely generated characteristic-zero domains; this shows that over infinite fields every finitely generated piece already lives over such a domain, so the field case is not finitely generated.
  leavitt-unit-group-finitely-presented: that is finite presentation over F_2; this shows no finite presentation (not even finite generation) is possible over an infinite field.
  leavitt-subalgebra-linear-groups-satisfy-boone-higman: that embeds linear groups over subalgebras of the binary Leavitt algebra over F_2; this shows that over a characteristic-zero field no finitely generated subalgebra contains Q.
---

**ESTABLISHED** by `infinite-field-leavitt-units-not-fg-proof` (elementary; not
independently reviewed; no novelty claimed).

Let `k` be an infinite field, `R = L_k(1,2)` and `U = R^x`.
1. **Coefficients stay finitely generated.** Every finitely generated subgroup of `U`,
   and every finitely generated subring of `R`, lies in `L_A(1,2)` for some finitely
   generated subring `A ⊆ k`. For `k = Q` one can take `A = Z[1/m]`.
2. **No finite generation.** Neither `U` nor `U / k^x` is finitely generated.
3. **No Q in a finitely generated subring.** If `char k = 0`, no finitely generated
   subring of `R` contains `Q` (that is, contains an inverse of every nonzero integer).

The same proofs apply to `L_k(1,n)` for every `n >= 2`.

## Consequences for `gl-n-q-embeds-in-fp-simple-group`

- **The rational Leavitt group is no host.** `L_Q(1,2)^x` and
  `Λ = L_Q(1,2)^x / Q^x` contain every `GL_n(Q)`
  (`leavitt-unit-groups-over-every-field-are-simple-mod-scalars`), but neither is
  finitely generated, so neither is itself the finitely presented host.
- **Commutative coefficient rings cannot supply Q.** By part 3, a finitely generated
  ring built inside a Leavitt algebra over a field never contains `Q`. So a route "put
  `Q` in a finitely generated subring of some `L_K(1,2)`, then take units" fails.
  `Q` must enter through noncommutative coefficients (e.g. `B ⊗ L` with `B ⊇ Q` a
  finitely generated noncommutative ring) or through a non-coefficient mechanism.
- **Leavitt unit groups over S-integers.** Every finitely generated subgroup of
  `L_Q(1,2)^x` lies in some `L_(Z[1/m])(1,2)^x`, a group with congruence quotients
  (`char-zero-leavitt-unit-groups-have-congruence-kernels`). The scalar-coefficient
  copy of `GL_n(Q)` lies in none of them.
