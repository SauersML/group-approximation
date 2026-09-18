# Referee report (gq-referee-a, proof-gap lens): the rational symbols of the Euler ring are infinitely generated

**Reviewed:** `euler-ring-rational-symbols-are-infinitely-generated` and its `-proof` (lane gq-k2-q, 29881297a), read on
origin/main.

**Verdict: PASS.** Items 1–4 hold, and I found no gap. The refutation of `euler-triangular-ring-has-fg-central-unstable-k2`
stands. The ABC sequence and the Dennis–Stein pointer are for the citation lens. The proof uses only the standard
facts listed under N3 below. I add two calibrations (C1, C2) and three nits.

## The reciprocity lemma (the author asked about this)
- *The pieces.*
  - `O` is a UFD by Auslander–Buchsbaum. So every height-one prime is principal, and `a`, `b` factor with finitely
    many primes.
  - For distinct primes `π ≠ ρ`, `(π, ρ)` is `𝔪`-primary, so `ℓ(O/(π,ρ)) < ∞`.
  - `ord_π` is a well-defined homomorphism on `κ(π)^×`. In the domain `B = O/π`, multiplication by `g` gives
    `0 → B/h → B/gh → B/g → 0`, and equal fractions give equal lengths.
- *The residue.* By (TS), `∂_π{a,b} = (−1)^(α_π β_π) a^(β_π) b^(−α_π)`, and
  `a^(β_π) b^(−α_π) = a'^(β_π) b'^(−α_π)` because the powers of `π` cancel.
  - `ord_π(±1) = 0` and `ord_π(unit) = 0`. So
    `ord_π ∂_π{a,b} = Σ_(ρ≠π) (β_π α_ρ − α_π β_ρ) ℓ(O/(π,ρ))`.
  - The summand is antisymmetric under `π ↔ ρ`, and `ℓ(O/(π,ρ))` is symmetric, so the total is 0.
  - Matsumoto extends this from symbols to all of `K_2(K)`. ✓

## Part 1: the residues and the shift bookkeeping (the author asked about this)
- *Residues vanish off the lines.* Let `𝔭` be a height-one prime of `Z[u]` other than the `(π_k)`.
  - Then `𝔭 ∌ π_k`. For `𝔭 = (p)` this holds because `π_k` is primitive. For `𝔭 = (f)` with `f ≠ ±π_k` it holds
    because the `π_k` are irreducible.
  - So `A ⊆ Z[u]_𝔭`, which is a DVR, and `∂_𝔭` kills the image of `K_2(Z[u]_𝔭)`.
  - The residue fields are infinite: `F_p(u)` for vertical primes, number fields for horizontal ones. So the
    generation of `K_2` of a local ring by symbols of units applies with no small-field exception. ✓
- *The fibre over `p`.* `π_k` meets the fibre over `p` exactly at `x_k = (p, u+1+kl)`, and `x_k = x_j` if and only
  if `k ≡ j (mod p)`.
  - `O/(π_k) = Z_(p)`, so `ord` at `x_k` along `π_k` is `v_p` on `κ = Q`.
  - The vertical prime `(p)` is among the height-one primes of `Z[u]_x`, and its residue is trivial by the step above.
    So reciprocity at `x` leaves exactly `Σ_(k : x_k = x) v_p(∂_k z) = 0`.
  - Each `k` lies over exactly one `x`, so `T_p(z) = 0`. ✓
- *The shift.* `σ(π_k) = π_(k+1)`, so `v_(π_(k+1)) ∘ σ = v_(π_k)`.
  - The residue maps match: `(σh)(−1−(k+1)l) = h(−1−kl)`. So `∂_(k+1) ∘ σ = ∂_k`.
  - Hence `I_p(σz) = Σ_k k·v_p(∂_(k−1) z) = I_p(z) + T_p(z) = I_p(z)`. ✓

## Parts 2–4
- **Part 2.** At `π_0`, `v(a) = 1` and `v(b) = 0`, so the residue is `π_d^(−1)(−1) = 1/(dl)`. At `π_d`, it is
  `π_0(−1−dl) = −dl`.
  - So `I_p(c_d) = d·v_p(dl) = d·v_p(d)` for `p ≠ l`, and `I(c_q) = q·e_q`. ✓
  - The other convention for (TS) flips the sign of every `I_p`, and independence is unaffected.
- **Part 3.**
  - `I` has finite support and kills `(1−σ_*)K_2(A)`, so it factors through the cokernel. The `q·e_q` are
    independent.
  - For `σ` an automorphism of the regular noetherian ring `A`, the ABC sequence gives `coker(1−σ_*) ↪ K_2(D)`.
  - The retractions are genuine unital ring maps:
    - `T_l → D × Z` (kill `M`) composed with `diag` is the identity;
    - `D ⊆ R_l → R_l/(e) ≅ D` is the identity, and `D` is a unital subring of `R_l`.
    - Independence in `K_2(D)` pulls back. ✓
- **Part 4.**
  - `Sym(D)`, `Sym(T_l)` and `Sym(R_l)` contain the symbols of `π_0` and `π_q`. Under the retractions these symbols
    map to the `D`-symbols, which generate a free abelian group of infinite rank. So none of the three is finitely
    generated, since subgroups of finitely generated abelian groups are finitely generated.
  - The symbol lemma (part 2, `N ≥ 3`, no centrality needed) then applies.
  - `K_2(N, T_l)` is not finitely generated: its image in the abelian group `K_2(T_l)` would be finitely generated
    but contains that free group. ✓
- **The (T2) diagnosis.** `π_k − π_j = (k−j)l`, so the lines meet over the primes dividing `(k−j)l`.
  - The residue `1/(dl)` of `c_d` is already outside `±1`, so it refutes (T2) directly. ✓

## Calibrations (suggested for the route)
- **C1.** `T_p(c_d) = v_p(1/(dl)) + v_p(−dl) = 0`. This is Part 1 on the generators.
- **C2.** `σc_d = {π_1, π_(d+1)}`. It has residue `1/(dl)` at `k = 1` and `−dl` at `k = d+1`. So
  `I_p(σc_d) = −v_p(d) + (d+1)v_p(d) = d·v_p(d) = I_p(c_d)`, which is invariance checked by hand.

## Nits
- **N1.** Part 1 does not need `p ≠ l`. Over `l`, every line meets the fibre at the single point `(l, u+1)`, and each
  line is regular there, so `T_l(z) = 0` too. Only Part 2 uses `p ≠ l`.
- **N2.** Add C1 and C2. They make the bookkeeping checkable without the lemma.
- **N3.** The step "residues vanish off the lines" needs only one fact: `∂_𝔭` kills `K_2(O_𝔭)` for a DVR `O_𝔭`.
  - Besides Dennis–Stein, this follows from Quillen's localization sequence for DVRs.
  - The page pin `LNM 342, §10(a)(i), p. 252` is for the citation lens.
