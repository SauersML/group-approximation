# K_2 of Toeplitz harmonic rings and Cantor-crossed Q-rings (lane gq-k2-q, 2026-09-18)

## 0. Status

The coordinator asked whether `K_2(N, R_T)` is finitely normally generated in `St_N(R_T)`.
- The question is moot on the host route. `bounded-harmonic-rings-are-not-finitely-presented` (1111ca113,
  double-refereed) already shows that no `E_N(R_T)` is finitely presented.
- What is landed here is the `K`-theory that holds for any ring over a Cantor `Γ`-system containing `Q`.
  It is recorded because the next host candidates are of the same kind.

## 1. Results

- **Clopen symbols (ESTABLISHED, lane proof).** `cantor-crossed-clopen-symbols-factor-through-coinvariants`.
  - The locally constant symbols of any such ring factor through `D_X ⊗ K_2(Q)`, with `D_X` the
    dimension group.
  - They vanish at every class divisible by all integers, in particular at every odometer-saturated
    clopen.
  - Over a congruence odometer they factor through `H_0(Γ; Q_X) ⊗ K_2(Q)`, with `Q_X` the hole module.
- **K-invisibility of harmonic coefficients (ESTABLISHED, lane proof).**
  `harmonic-coefficient-rings-are-k-equivalent-to-lc`.
  - `R_T = F ⋊_alg SL_3(Z)`.
  - `LC(X,Q) -> F` is a `K`-equivalence. This is proved by excision along the singular fibres (Suslin, as
    quoted by Tamme) and by homotopy invariance of `LC(S,Q)[t]`.
  - This lands Attempt 1 of `sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget`.
- **The invariant (OPEN).** `cantor-crossed-q-rings-need-odd-divisible-coinvariants`.
  - Over a torsion-free Farrell–Jones group, the odd part of `D_X ⊗ K_2(Q) -> K_2(B)` should be
    injective.
  - If so, an odd prime `ℓ` with `D_X/ℓ ≠ 0` gives infinitely many independent clopen symbols, one per
    prime `p ≡ 1 mod ℓ`.

## 2. What the invariant says about the next Cantor-crossed candidates

In the homotopy-orbit spectral sequence `E^2_(p,q) = H_p(Γ'; LC(X,Z) ⊗ K_q(Q)) ⇒ K_(p+q)`:

| Term | Group | Budget meaning |
|---|---|---|
| `E_(0,2)` | `D_X ⊗ K_2(Q)` | clopen symbols; need `D_X` ℓ-divisible for every odd `ℓ` |
| `E_(1,1)` | `H_1(Γ'; LC(X,Z)) ⊗ Q^x` (+ 2-torsion) | symbols `{λ, v}`; heuristically need `H_1(Γ'; LC(X,Z))[1/2] = 0` |
| `E_(2,0)` | `H_2(Γ'; LC(X,Z))` | not a symbol obstruction; enters `K_2` finite generation only |

For the `SL_3(Z)` congruence odometer itself:
- `H_0 = Q` is divisible;
- `H_1 = colim_transfer Γ(m)^ab = 0` (`sl3-congruence-transfer-kills-abelianization`);
- so the odometer passes both symbol tests.

Every obstruction comes from the hole module `Q_X = LC(X,Z)/π^*LC(K,Z)` of the expansive extension. By
Shapiro and the long exact sequence, `D_X/ℓ ≅ H_0(Γ;Q_X)/ℓ` and `H_1(Γ; LC(X,Z)) ≅ H_1(Γ; Q_X)`.

## 3. Proof sketch for the OPEN node

The steps and gaps are listed in the node's Attempts.
- The key point is that every differential entering `E_(0,2)` is induced by the Postnikov invariants of
  `K(Q)`, since `K(LC(X,Q)) ≃ K(Q) ∧ S[LC(X,Z)]`.
- Those invariants live in stable cohomology groups of Eilenberg–MacLane spectra in degrees 2 and 3,
  which carry no odd torsion.
- So only 2-primary classes can be killed, and odd-primary clopen symbols survive.

## 4. Calibration: the obstruction is not automatic

- Consider a Cantor `Γ`-system in which one free orbit of points of `K` is doubled, cut so that clopen
  sets separate each doubled pair at finitely many points, with signed jumps summing to zero.
- Then `Q_X` is the augmentation ideal `I_Γ ⊆ Z[Γ]`, and
  `H_0(Γ; I_Γ) = I_Γ/I_Γ^2 = Γ^ab`, `H_1(Γ; I_Γ) = H_2(Γ; Z)`.
- For `Γ = SL_3(Z)` these are `0` and a finite 2-group (`H_2(SL_3(Z); Z) = (Z/2)^2`, not re-read). So
  both symbol tests pass.
- For `Γ = Z` the analogous Sturmian system has `D_X = Z^2`. There the clopen symbols are infinitely
  generated, matching the Laurent-type failure in `laurent-rational-symbols-block-fp-elementary-groups`.

Perfectness of `SL_3(Z)` therefore helps; whether a given Toeplitz subshift passes depends on its hole
module.

## 5. Design lesson

A Cantor-crossed `Q`-host over `SL_3(Z)` should be built on a Cantor system whose dimension group is
divisible, or at least ℓ-divisible for every odd `ℓ`, and whose `H_1` has no odd or free part.
Two sources of such systems:
- bounded-width Toeplitz systems whose incidence counts are divisible by every prime infinitely often;
- hole modules that are induced from augmentation-type modules of perfect groups.

Finite presentation of the ring, which bounded harmonic rings lack, is a separate requirement.
