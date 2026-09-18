# GL_n(Q) into a finitely presented simple group (BBMZ 5.3(5)): end-to-end skeleton

Team lead: bh-major-gln. Team: bh-universal, bh-free-16, bh-g1-effective, gq-typeA-design.
This is a live skeleton, and every status below is the one recorded on its node. Most nodes are unreviewed
lane proofs; the K_2 chain carries two referee PASSes.

## 0. The target has already been reduced to one explicit group

- Every `GL_n(Q)`, for all `n` at once, embeds in `PE_3(R_L)` (`leavitt-linear-groups-live-in-one-projective-elementary-group`).
  `PE_3(R_L)` is a finitely generated simple group with solvable word problem, and it is Kazhdan (Ershov–Jaikin
  for `E_3`).
- `St_N(R_L)` is quasisimple (`steinberg-groups-of-r-l-are-quasisimple`) and finitely presented for `N ≥ 5`.
  `K_2(N,R_L) ≅ Q^×` is central, and the word problem is solvable (`leavitt-resolvent-k2-stability-holds`,
  refereed by a and b).
- So 5.3(5) follows from Boone–Higman for the single group `PE_3(R_L)`. It also follows from BH for the
  finitely presented group `St_10(R_L)`, which contains every `GL_n(Q)`.

## 1. Where the primes are, and where they are not

**Infinitely many primes are free inside finitely presented decidable envelopes.** A counter `N = s(N+1)t` with
`ts = 1`, together with one resolvent `A = (N+1)^(-1)`, inverts every `N+k`. Indeed `(N+k+1)^(-1) = t^k A s^k`,
and on the reset corner `e = 1 − st` this makes `Q·e` a subring. This is the Toeplitz resolvent mechanism
behind `R_L`, and it is the "prime odometer": all denominators come from one inverse plus an additive shift
of the spectral parameter.

**The prime obstruction lives in exactly two places:**
- **(P1) the simple-quotient step.** A unital ring containing `Q` has `Q` in its centre. With a Leavitt pair,
  `Q^×` becomes elementary, central and not finitely generated (`leavitt-scalar-commutators-block-fp-central-quotients`).
  So every Steinberg quotient over `R_L` is dead, and so is `St_N ⋊ V`
  (`leavitt-steinberg-thompson-extensions-add-nothing`).
- **(P2) finite-data hosts.**
  - Unit groups act residually finitely (`finitely-coded-unit-groups-act-residually-finitely`).
  - Fixed local data sees finitely many primes (gq-affq, prime locality).
  - Mass modules over self-similar trees are finitely generated (`no-free-q-odd-action-by-v-has-a-doubling-intertwiner`).
  - V-elements carry atomless invariant measures only where periodic (`v-element-invariant-measures-live-on-the-periodic-part`).
  - No homeomorphism shifts prime denominators (`no-homeomorphism-shifts-odd-denominator-translations`, six exponentials).
  - W-type affine hosts reach only arithmetic coefficients (`twisted-s-integral-affine-groups-are-fp-and-virtually-simple`
    and its saturation node).

**Design rule that follows.** Put the arithmetic in the ACTING GROUP, never in the coefficient ring of a simple
quotient and never in the local geometry of a finite-data host.

## 2. Live routes

**R1, the master route (board/SYNTHESIS.md).**
- **Shape.** Take `Λ₀ = St_10(R_L)` as the acting group over `F_2`. The host is the unit group of
  `(LC(X,F_2) ⋊ (Λ₀ × H)) ⊗ L`, for a free minimal SFT `X` over `Λ₀ × H`.
- **Why the centre is harmless.** Central `Q^×` in `Λ₀` acts freely on `X`, so it is not central in the
  crossed product.
- **Supplied:** the ring-side finite-presentation certificate (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`,
  lane).
- **Open gates:**
  - **G1:** an effective minimal free subshift on `Λ₀` (bh-g1-effective), then coupled simulation.
  - **G2:** quantum rigidity (the crux; bh-g2-*).
  - **G3r:** `K_1 = K_2 = 0` for `B ⊗ L`. This is reduced to Nil-regularity (`leavitt-tensor-k-theory-is-carried-by-nil-groups`).
- **Assessment.** The GL_n(Q) case is no harder than the general case for decidable inputs. `Λ₀` is Kazhdan,
  so `H` should be chosen non-amenable and coupled.

**R2, Leavitt units over a finite field.**
- **The reduction.** Every Leavitt host reduces to `L_(F_p)(1,2)^×`
  (`integral-unit-hosts-for-gl-n-q-reduce-to-finite-fields`), which is finitely presented and simple.
- **New this pass:** `leavitt-unit-commuting-with-a-leavitt-copy-gives-q-in-units`. One infinite-order unit
  commuting with a unital copy of `L` gives `(Q,+) ⊂ L^×`: the matrix towers come for free, since
  `L ≅ M_n(L)` for all `n` with no mass.
- **The crux.** This is exactly the witness forbidden by the OPEN `leavitt-unit-centralizers-have-finite-rank`.
  So R2 lives or dies with that conjecture. If it is true, `H_3(Z)` is not in `L^×`, and R2 is dead for `n ≥ 3`.
- **Still missing even if the conjecture fails:** the dilations `r_k ↦ r_k^q`.

**R3, Cantor and Thompson hosts.** Only these designs survive (P2):
- a two-coordinate hyperbolic mixing dilation (bh-free-16);
- addable registers (bh-universal);
- non-commuting shell windows `N ≥ 1` (gq-typeA-design and gq-infinite-primes).

Every single-coordinate design is dead.

## 3. Dead routes (do not revisit)

- Steinberg or central quotients over any ring containing `Q` with a Leavitt pair.
- `St_N(R_L) ⋊ V`.
- Window-zero shells for FW inputs (`fw-window-zero-shells-are-self-similar-actions`).
- Odometer/solenoid codings of `Q ⋊ ⟨2⟩` in `2V_τ`.
- Mixed-radix prefix hosts.
- Exponential-chart Stein elements.
- Houghton-like envelopes.

## 4. Assignments

| Lane | Task |
|---|---|
| bh-g1-effective | the first concrete gate of R1: an effective minimal free subshift on `St_10(R_L)` |
| bh-universal | R3 addable registers. It should also test R2's finite-rank tension: does any unit of `L_(F_2)` commute with a copy of `L`? |
| bh-free-16 | R3 mixing germs for `Q ⋊ ⟨2⟩` |
| gq-typeA-design, gq-infinite-primes | R3 non-commuting windows for `St_N(R_L)` |
| any R2 lane (unowned) | decide the finite-rank conjecture in the form "no unit of infinite order commutes with a unital copy of `L`". Both answers matter. |

## Lesson for general BH

Infinitely many primes are never the obstruction inside finitely presented decidable envelopes: one resolvent
plus a shift gives all of them. The obstruction appears only when arithmetic is forced into a centre (the
simple-quotient step) or into finite local data (Cantor hosts). Leavitt algebras remove the mass obstruction
entirely, since they split every integer for free, but then the obstruction reappears as centralizer rank.
So general BH hosts should carry arithmetic in the acting group of a crossed product. That is the master
route's design, and GL_n(Q) is an instance of it, not a special case.
