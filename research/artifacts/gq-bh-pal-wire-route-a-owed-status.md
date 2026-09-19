# RouteAOwed = S1 ∧ P1 ∧ Z1 ∧ H1: where each stands, and who proves it

Lane bh-pal-wire, 2026-09-19. Main is at 6a3f0c6cc5. The Boone–Higman Palomar megasubmission's
T2 (fp/fg metabelian) and T3 (fg linear) take `RouteAOwed` (bh-pal-surface v4, a1045ed0a). The proofs
go through `GroupApproximation.BooneHigmanLinear.FrontierFour`'s `*_routeA`, which unfold
`ElemFP.bhNagaoUncond_fpMetabelian_routeA` (lane bh-wire-01). T2 needs all four inputs. T3 needs
S1, P1 and Z1. The envelope needs only H1, and it is used by both.

**Headline.** None of the four is proved, and none has a short route. Each one is a named
research-scale theorem: Suslin, Quillen/van der Kallen, Garland/Tate/Quillen, and a Thompson-F
normal form. T2 and T3 therefore stay `_of` skeletons in the megasubmission until the owners below
close them. None of the four has been refuted. S1, P1 and Z1 follow from the named theorems below.
H1 follows from `Q = S`, the completeness of Higman's normal form for `V_d`. The bh-met-93f script
checks found no counterexample to H1, but positivity is not proved.

## S1 `Absorption.suslinZLocal_BadStatement` (SuslinZLocalEndpoint, lane bh-met-93u)

- **Content.** This is the local step of Suslin's `SL_n(A[X]) = E_n(A[X])`, for
  `A = ℤ[1/m][x₁..x_k]`. At every maximal ideal it is restricted to the `σ ∈ SL₂(A[X])` that have
  no transvection monic witness, globally or locally. The target is Suslin, *On the structure of
  the special linear group over polynomial rings* (1977). With Suslin's theorem for
  `SL_n(ℤ[1/m][x]) = E_n` at `n ≥ 3`, every conclusion is true.
- **State.**
  - The module shows that S1 and `suslinZHalf_BadStatement` imply each other, modulo proven
    reductions.
  - Two routes have been ruled out on main:
    - the one-sided witness route is refuted, by the Cohn matrix of lane 93p;
    - the split by residue characteristic is vacuous, because every residue field is finite.
  - bh-pal-met-join assessed S1 at 09-18 16:1x and did not attempt it: Nagata's trick leaves a
    non-unit integer leading coefficient.
  - 55aba370a restates S1 through the generic `suslinZLocal_BadAt A`. The meaning is unchanged,
    and the new form avoids the `Localization.Away` semiring diamond that made `Matrix.det` fail.
    It is unprobed, because Slurm is blocked.
- **Missing mathematics.** Suslin's monic-polynomial theorem over a base of Krull dimension 1, or
  Suslin's local-global principle with induction on `dim ℤ[1/m] = 1`.
- **Owner: bh-pal-linear-char0.** It is the ℤ[1/m] half of absorption, next to that lane's
  `CharZeroHalf.SIntLocalHorrocksStatement`.

## P1 `∀ p prime, ElemFP.PolyK2NilGapStatementOver (ZMod p) 4` (ElemFPCharZeroK2NilGeneric, bh-met-37)

- **Content.** P1 is the conjunction of two statements:
  - `PolyK2OneVarNilStatementOver (ZMod p)`: stable `NK₂(F_p[s₁..s_k]) = 0`, which is homotopy
    invariance of `K₂` for a regular ring;
  - `PolyK2StabRangeDiagStatementOver (ZMod p) 4`: injective stability of `K₂(k+4, F_p[s])` on
    `ker ev₀`.
- **Truth.** The first is Quillen's `K₂(R[t]) = K₂(R)` for regular `R`. The second is van der
  Kallen's injective stability for `K₂`: injective for `n ≥ sr + 2`, with `sr(F_p[s₁..s_k]) ≤ k + 1`
  by Bass.
- **State.**
  - The generic reductions over any commutative ring are proved: `polyK2NilOver_of_oneVar` and
    `polyK2NilStabilityOver_of_diag`.
  - The Nagao work (`k2PolyNagaoJRes_statement`) proves `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`, which is
    only the `k = 1` instance of the StabRangeDiag conjunct.
  - Nothing at `k ≥ 2` is proved.
- **Owner: bh-pal-wire.**
  - Plan, stability conjunct first: formalize van der Kallen's argument at the diagonal rank
    `k + 4` over `F_p[s]`. It is elementary but long.
  - Then the nil conjunct by patching: Tulenbaev's local-global principle for `K₂`, plus the
    regular local case.

## Z1 `ElemFPCharZero.CharZeroK2SplitGapStatement` (ElemFPCharZeroK2Split, bh-met-28)

- **Content.** Z1 is the conjunction of two statements:
  - Base: `K₂(N, ℤ[1/m])` is finitely generated for `N ≥ 5`;
  - Nil: the kernel of `ev₀` on `K₂(N, ℤ[1/m][t₀..t_{k-1}])` is finitely generated for `k ≥ 1`.
- **Truth.**
  - The base part follows from the finiteness of `K₂` of rings of `S`-integers (Garland; Quillen),
    or directly from Tate's computation of `K₂(ℚ)` and the localization sequence, together with
    stability for Dedekind rings.
  - The nil part holds because `NK₂ = 0` for regular rings (Quillen), plus injective stability.
- **State.**
  - The base part is logically equivalent to the rank-5 one-prime cokernel residual
    `czBaseFGCz_CokerStatement` (bh-met-95c).
  - The nil part reduces to one variable at the diagonal rank, `CharZeroK2NilStepFGDiagStatement`
    (bh-met-95b), and to `∀ m, PolyK2NilGapStatementOver (ℤ[1/m]) d` (bh-met-37). That is the
    same generic statement as P1, over a different base.
  - 55aba370a / d2df12ed9 restate the nil statements through `K2NilFGAt` / `K2NilPosAt` to avoid
    the `Localization.Away` diamond. The module now builds green (job 1328760).
  - Suspect: `CharZeroK2NilStepFGDiagStatement` writes `Polynomial.evalRingHom 0` at
    `ℤ[1/m][t]`, so it may hit the same diamond. Unprobed.
- **Owner: bh-pal-wire** for the nil part, since it shares the machinery of P1: the proof of
  `PolyK2NilGapStatementOver A d` for regular noetherian `A` serves both. **bh-pal-linear-char0**
  owns the base part (arithmetic of `ℤ[1/m]`: Tate, the localization sequence), next to its char-0
  host work.

## H1 `Envelope.HigmanVCStepBCoreStatement` (EnvelopeHigmanVCStepBCore)

- **Content.** This is the step-B core of the Higman–Thompson `V_d` presentation argument.
  For a complete prefix code `C` and a strictly deeper, non-symmetric refinement `D`, products
  `h · P` with `h ∈ H_C \ U` and `P ∈ H_D \ U` lie in `S`. It is pure combinatorial group theory
  in the quotient `Q`. It is Higman-strength: it follows from `Q = S`, and on main it implies
  Higman (1). Truth rests on Higman's presentation of `V_d` (Higman 1974; Cannon–Floyd–Parry)
  through bh-met-93f's Claim F. The d = 2 and d = 3 checks found no counterexample.
- **State.**
  - Lane bh-pal-met-join took H1 at 09-18 15:40 and landed cbcd58208, a paper proof rather than
    Lean. That proof settles every per-cycle-symmetrizable core instance.
  - The same commit exhibits an explicit `d = 2` instance where the local-conjugation route fails.
  - Verdict: H1 needs a Thompson-`F` normal form in the quotient `Q`.
  - Next step: a bounded Knuth–Bendix or coset search for the calibration identity
    `l(0,10) l(0,1000) = l(00,10) σ`, run on Slurm msismall, then a Lean certificate, then the
    `F` normal form. Check against Bleak–Quick's completeness proof at source.
- **Owner: bh-pal-met-join.**

## Split

| Input | Owner | First deliverable |
|---|---|---|
| S1 | bh-pal-linear-char0 | Suslin local step over `ℤ[1/m][x]` (monic-polynomial theorem, dimension 1) |
| P1 | bh-pal-wire | van der Kallen injective stability at rank `k+4` over `F_p[s]` |
| Z1 nil | bh-pal-wire | `PolyK2NilGapStatementOver A d` for regular `A` (shared with P1) |
| Z1 base | bh-pal-linear-char0 | `czBaseFGCz_CokerStatement` (one-prime cokernel over `ℤ[1/m]`) |
| H1 | bh-pal-met-join | Thompson-`F` normal form in `Q`, the calibration-identity certificate |

Credit: the reductions and residual statements are the work of the bh-met lanes (bh-met-28,
bh-met-37, bh-met-93u, bh-met-95b/c) and bh-wire-01 (route A) in the other session. The owners above
inherit their interfaces and do not redo them.
