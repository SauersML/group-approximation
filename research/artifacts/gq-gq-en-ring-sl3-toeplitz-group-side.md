# The group side of the SL_3(Z) Toeplitz harmonic host R_T (lane gq-en-ring, 2026-09-18)

Coordinator's items for `R_T` (`sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`, lane
`gq-deep-adelic-1`):
1. simplicity of `PE_N(R_T)`;
2. the consequence of `Λ_N ⊆ {±1}` for finite presentation;
3. the full-corner `K_2` lemma on letter-cylinder corners (risk R1).

Finite presentation belongs to `gq-steinberg-q`; R1 and R2 for general units belong to
`gq-deep-adelic-1`.

## 1–2. Landed (lane proofs, not refereed)

| Node | Status | Content |
|---|---|---|
| `clopen-crossed-product-subrings-have-local-annihilation` | ESTABLISHED | a unital subring of `C(X,k) ⋊ Γ` containing all clopen indicators has local annihilation, whatever the coefficient functions (`X` infinite compact totally disconnected) |
| `sl3-toeplitz-harmonic-pe-groups-are-simple` | ESTABLISHED (conditional on the lane proof that `R_T` is simple) | `N >= 3`: every normal subgroup of `E_N(R_T)` is central or all; `PE_N(R_T)` is infinite simple; `Z(E_N(R_T)) ⊆ {±I}`; `PE_N(R_T)` is f.p. iff `E_N(R_T)` is; `GL_n(Q) ≤ PE_N(R_T)` for `N >= n+2` |
| `sl3-toeplitz-harmonic-elementary-groups-are-fp` | OPEN | `E_N(R_T)` f.p. for infinitely many `N` (owner `gq-steinberg-q`) |
| `q-algebra-host-via-sl3-toeplitz-harmonic-ring` | route | the two nodes above ⇒ `q-algebra-with-fp-simple-projective-elementary-group` ⇒ root |

So for `R_T` the host question is now **only** finite presentation of `E_N(R_T)` for infinitely
many `N`. Simplicity is settled by the Lean ring criterion (`local-annihilation-makes-projective-el-simple`),
and the centre clause by `Λ_N ⊆ {±1}`.

## 3. R1 on letter-cylinder corners: reduction, not a verdict

The full-corner lemma (`full-corners-must-kill-rational-k2-symbols`) requires, if `E_N(R_T)` is f.p.,
that `K_2(Q) -> K_2(χ_C R_T χ_C)` has finite image for every nonempty clopen `C`.

- **Blocks pass.** For a block `B` of level `d`, `χ_B R_T χ_B ≅ S_d ≅ M_([Γ(d):Γ(dt)])(S_(dt))`.
  The index `[Γ(d):Γ(dt)]` is divisible by `t`: every prime power dividing `t` divides the order of
  the kernel of `SL_3(Z/dt) -> SL_3(Z/d)`. So block corners are matricially divisible and kill
  `K_2(Q)` (`matricial-divisibility-kills-rational-k2-symbols`). This confirms the "Known" line of
  `sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget`.
- **Letter cylinders reduce to their hole parts.** Write `C = [a] = π^-1(D_n) ⊔ E_n`. Here `D_n` is
  the union of the level-`n` cosets on which the Toeplitz point is periodic with value `a`, and
  `E_n ⊆ π^-1(H_n)` lies over the level-`n` holes.
  - Orthogonal idempotents contribute additively to the corner symbols
    `{d_e(λ), d_e(μ)}`: the cross symbols of commuting units in orthogonal corners vanish (standard,
    cited from memory).
  - So the image of `z ∈ K_2(Q)` in the `C`-corner equals its image in the `E_n`-corner, for
    **every** `n`.
  - R1 at `[a]` is therefore a statement about the hole pieces alone. They shrink in measure, but the
    `K_2(Q)`-pairing is not continuous in measure.
- **R1 is a real constraint on the choice of subshift.**
  - **Calibration, `Z`-Toeplitz flows.** A Bratteli–Vershik model with equal row sums, for example
    incidence `[[2,1],[1,2]]`, has `K^0 ≅ Z[1/3] ⊕ Z`, with a non-divisible infinitesimal summand.
    Equal row sums characterize Toeplitz flows (Gjerde–Johansen; recalled, not re-read).
  - Vertex (cylinder) classes then have non-divisible infinitesimal parts. Nothing forces the
    `K_2(Q)`-pairing to kill those, since `K_2(Q)` has elements of every order.
- **Sufficient condition.** Every clopen of `X` is `m`-divisible in the type semigroup of `Γ ⋉ X`, for
  `m` cofinal. Equivalently, the clopen classes are matricially divisible in `R_T`. Then every clopen
  corner kills `K_2(Q)`. For `SL_3(Z)` Toeplitz subshifts this is open.
  - For `Z`, strong orbit equivalence to the universal odometer would give it: the SOE class is
    determined by `(K^0, K^0_+, [1])`, and the odometer's `K^0 = Q` is divisible. But whether an
    expansive Toeplitz subshift lies in that class is not known here.

## 4. Handoffs

- `gq-steinberg-q`: `sl3-toeplitz-harmonic-elementary-groups-are-fp` is the single open condition on
  the group side. A first sub-question is whether `R_T` is a finitely presented ring.
- `gq-deep-adelic-1`: R1 reduces to the hole corners, and R1 depends on choosing a Toeplitz subshift
  whose clopen classes are divisible.
