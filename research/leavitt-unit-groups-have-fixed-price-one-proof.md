---
rg: 2
id: leavitt-unit-groups-have-fixed-price-one-proof
kind: route
title: Run Gaboriau's commensurated chain through the root subgroups of EL_3 over a noncommutative ring
target: leavitt-unit-groups-have-fixed-price-one
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - fpbs-amen2-betti-cost-input
---

Written check from textbook inputs. It is not a formal verification.

**Inputs.**
- Gaboriau, *Coût des relations d'équivalence et des groupes*, Invent. Math. 139 (2000), Critères VI.24(3),
  restated as Theorem 2.45 of his lecture notes. Both are quoted verbatim in
  `fpbs-elementary-matrix-semidirect-fixed-price-one-citation`. The lemma below is that theorem; its proof
  is repeated so that this route stands alone.
- Kechris--Miller, *Topics in orbit equivalence*, Lemma 6.7 (markers).
- Ornstein--Weiss (free actions of infinite amenable groups are hyperfinite) and Levitt (aperiodic
  hyperfinite relations have cost one, every aperiodic relation has cost at least one).

For `S <= G` and a fixed free p.m.p. action `G` on `(X, mu)`, write `R_S` for the orbit relation of `S`
and `C(R_S)` for its cost.

**Lemma (commensurated step).** Let `K <= G`, and let `g_1, g_2, ...` be countably many elements with
`L_j = K ∩ g_j^(-1) K g_j` infinite for every `j`. Then `C(R_<K, g_1, g_2, ...>) <= C(R_K)`.

*Proof.* Fix `eps > 0`.
- `L_j` is infinite and acts freely, so `R_(L_j)` is aperiodic. By the marker lemma it has a Borel complete
  section `B_j` with `mu(B_j) < eps 2^(-j)`.
- Take a graphing `Phi` of `R_K` of cost below `C(R_K) + eps`. Add the partial maps `g_j|_(B_j)`.
- Given `x`, pick `l in L_j` with `l x in B_j`. Then `g_j x = (g_j l^(-1) g_j^(-1)) (g_j (l x))`.
  - `x` and `l x` are `R_K`-related, since `l in K`.
  - `l x -> g_j (l x)` is an edge of `g_j|_(B_j)`.
  - `g_j l^(-1) g_j^(-1) in K`, since `l in g_j^(-1) K g_j`.
- So the new graphing generates `R_<K, g_1, g_2, ...>`, and its cost is below `C(R_K) + 2 eps`. QED

**Steinberg commutation over an arbitrary ring.** For `a, b in R`, `e_ij(a) = 1 + a E_ij`. If `j != k`
and `i != l`, then `E_ij E_kl = delta_jk E_il = 0` and `E_kl E_ij = delta_li E_kj = 0`. Hence
`e_ij(a) e_kl(b) = 1 + a E_ij + b E_kl = e_kl(b) e_ij(a)`. No commutativity of `R` is used. If `g` commutes
with an infinite subgroup `M <= K`, then `M <= K ∩ g^(-1) K g`, so the lemma applies to `g`.

**Chain for `EL_3(R)`.** Each root subgroup `E_ij(R)` is isomorphic to `(R, +)`, so it is infinite abelian.
- `K_0 = E_12(R)`.
- `K_1 = <K_0, E_13(R), E_32(R)>`. The pairs `(13, 12)` and `(32, 12)` satisfy `j != k`, `i != l`, so every
  new generator commutes with `E_12(R)`.
- `K_2 = <K_1, E_31(R), E_23(R)>`. Here `E_31(R)` commutes with `E_32(R) <= K_1` (pair `(31, 32)`), and
  `E_23(R)` commutes with `E_13(R) <= K_1` (pair `(23, 13)`).
- `K_3 = <K_2, E_21(R)>`. Here `E_21(R)` commutes with `E_23(R) <= K_2` (pair `(21, 23)`).

`K_3` contains all six root subgroups, so `K_3 = EL_3(R)`. Every stage adds countably many elements, as `R`
is countable. Three applications of the lemma give `C(R_(EL_3(R))) <= C(R_(E_12(R)))`.

**Larger `r`.** Start from `E_12(R)` and add every `E_ij(R)` with `j != 1`, `i != 2`. Then add `E_i1(R)`
for `i >= 3`, which commutes with `E_i2(R)`, and `E_2j(R)` for `j >= 3`, which commutes with `E_1j(R)`.
Finally add `E_21(R)`, which commutes with `E_23(R)`. This is the chain of
`fpbs-elementary-matrix-semidirect-fixed-price-one-proof` with `H` trivial, and it uses only the relation
above.

**Cost one.** `E_12(R)` is infinite amenable and acts freely, so `R_(E_12(R))` is aperiodic and hyperfinite,
and has cost one. `R_(EL_r(R))` is aperiodic, so its cost is at least one. Hence every essentially free
p.m.p. action of `EL_r(R)` has cost one, and `EL_r(R)` has fixed price one.

**Leavitt unit groups.** Let `K` be a countable field and `R = L_K(1,2)`, a countably infinite ring. By
`leavitt-gl-equals-el-and-perfect-unit-group`, the three-leaf prefix code gives a ring isomorphism
`R ≅ M_3(R)`, hence a group isomorphism `R^x ≅ GL_3(R)`, and `GL_3(R) = EL_3(R)`. Cost of free actions is
an invariant of the acting group up to isomorphism. So `L_K(1,2)^x` has fixed price one. The case
`K = F_2` is the first nonsofic group.

**First `L^2`-Betti number.** `fpbs-amen2-betti-cost-input` is Gaboriau's inequality
`beta_1^(2)(G) <= C(R_(G -> X)) - 1` for a free p.m.p. action of an infinite group. The right side is zero,
so `beta_1^(2) = 0` for `EL_r(R)` and for `L_K(1,2)^x`.
