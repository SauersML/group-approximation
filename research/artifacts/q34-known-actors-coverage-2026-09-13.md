# BFFHZ Question 3.4: which known finitely presented simple groups satisfy PBH (2026-09-13)

Lane `solve-q34-known-actors`. The target stays OPEN:
`fp-simple-groups-embed-in-fp-simple-mif-groups`.
- By `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`, Question 3.4 for a finitely
  presented simple `S` is equivalent to PBH for `S`.
- This census records which families are settled, and on what basis.

## 1. Census

| Family | PBH status | Basis |
|---|---|---|
| `V`, finitely presented Röver–Nekrashevych commutator subgroups, other finitely presented simple Cantor groups containing a Higman–Thompson commutator subgroup | yes | BFFHZ Remark 3.5, as quoted in `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh` (text not re-pinned here) |
| Thompson `T` | yes | `T <= V` (same Remark) |
| Twisted Brin–Thompson groups | yes | same Remark; BFFHZ Theorem C (ii) |
| Finitely presented simple Burger–Mozes groups | yes | `burger-mozes-simple-lattices-are-highly-transitive` |
| Finitely presented simple non-affine Kac–Moody groups | yes | `fp-simple-kac-moody-lattices-satisfy-pbh` (Rybak MIF, Theorem C) |
| `L_(F_2)(1,2)^×` | yes, two independent routes | `leavitt-pbh-via-cantor-module-affine-actor` (19108f02e) and `binary-leavitt-pbh-via-chen-module-lines` (98a1b7f25) |
| `L_(F_p)(1,2)^× / F_p^×`, `p` odd | **yes (new)** | `leavitt-unit-groups-mod-scalars-satisfy-pbh` (98a1b7f25) |
| `(L_(F_2)(1,2) ⊗ L_(F_2)(1,2))^×` and `(L_p ⊗ L_p)^× / F_p^×` | **yes (added after this census)** | `leavitt-square-unit-groups-mod-scalars-satisfy-pbh` (lane `solve-q34-tensor-leavitt`) |
| `L_(F_2)(E)^×` for other graphs `E` | yes as groups, by embedding (`char-two-leavitt-path-unit-groups-satisfy-pbh`); not yet a finitely presented simple instance | finite presentation and simplicity are still OPEN (`f2-leavitt-path-unit-groups-fp-simple-steinberg`) |
| Lodha's finitely presented simple circle group; Rattaggi-type simple lattices in products of trees; Stein groups, irrational-slope `T_τ`, `V_τ`; BBMZ hyperbolic hosts | not checked against sources in this lane | see §3 |

## 2. The new mechanism: the Chen-module line action

The nodes landed in 98a1b7f25, none independently reviewed:
- `leavitt-units-act-two-transitively-on-chen-module-lines`, proof
  `leavitt-chen-module-line-action-proof`;
- `leavitt-unit-groups-mod-scalars-satisfy-pbh`, route
  `leavitt-units-pbh-via-chen-module-line-action`;
- the second binary route `binary-leavitt-pbh-via-chen-module-lines`.

**Structure of the argument.**
- **Transitivity is free.** Any finite set of points of the tail class `D` of `0^∞`
  sits in incomparable cones of one length. There matrix units give all of
  `GL_m(F_p)` as units.
- **The stabilizer is the work.**
  - The germ of `u` at `0^∞` is a column over `F_p[s, s^-1]` indexed by `D`.
  - It is unimodular, because germs multiply.
  - Entries away from `0^∞` vanish at `s = 1`.
  - Elementary operations in the stabilizer run a Euclidean algorithm in which only
    `(s − 1)`-multiples can flow out of `0^∞`. That still reaches the trivial germ.
  - Trivial-germ units are `g`-conjugates of `(R, +) ⋊ U`, and `R` is spanned by its
    units.
- **Why not the aperiodic class.** On the tail class of an aperiodic point, a unit
  fixing the base vector already fixes a cone around the point pointwise, since distinct
  monomials send an aperiodic tail to distinct points. So the stabilizer is an
  increasing union of cone-fixing subgroups. It is not finitely generated as soon as that
  union is strict, and strictness was not written out here. The periodic class `0^∞` is
  what makes the germ group a Laurent ring.
- **Comparison with the Cantor-module route.** That route needs finite presentation of
  the extension `C(C,F_2) ⋊ U`. This one needs only finite generation of a stabilizer,
  so it extends to every prime `p`.

## 3. Candidates not settled, and first tests

1. **Tensor squares `L ⊗ L`.**
   - **Settled after this census.** See `leavitt-square-units-act-two-transitively-on-chen-lines`. The Euclidean step is replaced by a four-move reduction through a fresh point, so no Suslin-type theorem is needed. The original first tests follow.
   - The simple module `F_p[D] ⊗ F_p[D]` is the natural analogue.
   - Matrix units on products of cones should again give 2-transitivity on lines.
   - The stabilizer germs become a two-variable Laurent ring `F_p[s_1^±, s_2^±]`, which is
     not a PID. The Euclidean step fails as written; a Suslin-type `SL_n` generation over
     Laurent polynomial rings is the natural substitute.
   - Not attempted.
2. **Lodha's circle group.**
   - The analogue of `T` acting 2-transitively on the dyadic circle points with
     stabilizer `F` would be a 2-transitive orbit action with a Lodha–Moore stabilizer.
   - Its finite generation and the 2-transitivity were not verified from the source
     (arXiv:1710.06220 not fetched).
3. **Other simple lattices in products of trees.**
   - Le Boudec's argument in BFFHZ Remark 3.5 needs three things: a projection dense in a
     boundary-2-transitive group, cohomological dimension 2, and FLMMS22 Theorem B.
   - Whether Rattaggi's simple lattices meet the first hypothesis was not checked.

## 4. Exact gap for Question 3.4

- No family above is a counterexample, and no invariant of type (A) actors separating a
  finitely presented simple group was found.
- The open instances named here are the tensor-square Leavitt unit groups, and the
  literature families in §3 not checked against sources.
- For the general question, the reformulation stays
  `pbh-passes-to-relative-free-group-automorphisms`: `Aut_S(S * F_n)` must lie in a type
  (A) actor.
