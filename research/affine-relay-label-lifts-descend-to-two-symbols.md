---
rg: 2
id: affine-relay-label-lifts-descend-to-two-symbols
kind: claim
title: A strict one-rest automaton with an odd number of active symbols and an integral affine phase relay gives binary strict automata over G × C_q for infinitely many primes q
distinct_from:
  donor-covering-strict-automata-descend-to-two-symbols: that carries each output phase from one donor site and needs every active input to be some donor (a local matching); this lets the output phase be an integral affine combination of the window phases and needs only that the resulting linear maps are injective mod every prime, which implies a matching globally but not locally. Donor-covering with one rest symbol is the special case of unit-vector relays. The proof here uses neither that node nor its items.
  free-orbit-label-lifts-need-count-raising-label-automata: that is a necessary condition for every lift; this is a sufficient condition for a class of lifts that is strictly larger than the donor lifts.
  binary-shifts-over-odd-fibers-split-off-the-augmentation-shift: that reduces binary witnesses over G × C_q to ζ-homogeneous automata on R_q^G; this builds such automata from a label automaton and an affine relay.
  strict-automata-reduce-to-few-rest-self-relaying-ones: that asks for death-free witnesses with at most two rest symbols; this asks for one rest symbol with an odd number of active symbols and allows deaths, provided the phases of dying sites are kept in affine combinations nearby.
artifacts:
  - experiments/affine-relay-lifts-2026-09-17/check.py
---

**ESTABLISHED** by `affine-relay-label-lift-proof`.

**Setting.** `G` is a group, `L = {0} ⊔ B`, and `τ` is an automaton on `L^G` with memory `M ∋ 1` and local rule `μ`,
so `τ(ℓ)(g) = μ(ℓ_g)` with `ℓ_g(m) = ℓ(gm)`. For `ℓ ∈ L^G` let `act(ℓ)` be its set of non-`0` sites. An **integral
affine relay** for `τ` is a map `a: L^M → Z^M` with:
- **(R1)** `a_m(u) = 0` whenever `u(m) = 0`;
- **(R2)** `Σ_m a_m(u) = 1` whenever `μ(u) ∈ B`;
- **(R3)** for every `ℓ ∈ L^G` and every prime `p`, the linear map
  `A_ℓ: (Z/p)^act(ℓ) → (Z/p)^act(τ(ℓ))`, `(A_ℓ φ)(g) = Σ_m a_m(ℓ_g) φ(gm)`, is injective on all vectors (not only
  finitely supported ones).

By (R1) the sum only involves active sites of `ℓ`. By (R2) an active output window has an active entry.

**Theorem.**
1. **Affine lift.** Let `n >= 2`, `C_n = {0} ⊔ B × Z/n` with `Z/n` acting on the second coordinate, and `σ` the orbit
   map. Put `θ_n(c)(g) = 0` if `τ(σc)(g) = 0`, and otherwise
   `θ_n(c)(g) = (τ(σc)(g), Σ_m a_m((σc)_g) φ_c(gm))`, where `φ_c(h)` is the `Z/n`-coordinate of `c(h)` at active
   sites. Then `θ_n` is an automaton on `C_n^G` that commutes with `Z/n`, satisfies `σθ_n = τσ`, and has the integral
   affine relay `a∘σ`. If `τ` is injective, so is `θ_n`. If `τ` is not surjective, neither is `θ_n`.
2. **Donors are unit relays.** A donor-covering `τ` with one rest symbol has the relay `a(u) = e_(d(u))`, and (R3) is
   then exactly (D2).
3. **Binary witnesses.** Suppose `τ` is strict, `|B|` is odd, and `τ` has an integral affine relay. Let `q` be a prime
   with `q > |B|` and `q ≡ 1 mod ord_|B|(2)` (take `ord_1(2) = 1`). There are infinitely many such primes, and for each
   of them `G × C_q` carries a binary strict automaton. So `2 ∈ NS_all`.
4. **Necessary shape.** If `τ` is injective with an integral affine relay, then for every `ℓ` and every finite
   `S ⊆ act(ℓ)` at least `|S|` active output sites `g` of `τ(ℓ)` have `a_m(ℓ_g) ≠ 0` for some `gm ∈ S`. So a global
   injection `act(ℓ) → act(τ(ℓ))` along nonzero relay coefficients exists (Hall, 1948). It need not be locally
   defined. If `τ` is strict, then by `free-orbit-label-lifts-need-count-raising-label-automata` applied to `θ_2`,
   `τ` never lowers the finite active count and raises it somewhere.

**What this changes.** For one rest symbol, the donor route needs a *locally defined* surjection from active outputs
onto active inputs. Locally defined matchings are exactly what Hilbert-hotel mechanisms cannot compute from symmetric
data (the firewall of `nonamenable-groups-carry-arrow-shift-strict-automata`, Step 6). Affine relays drop locality of
the matching: dying phases may be kept in combinations such as `2φ(g) - φ(gs)`, and only injectivity of a sparse
linear map mod every prime is needed. This splits the label-lift route to universal descent
(`universal-binary-descent-via-affine-relay-hotels`) into two prerequisites, each of which can fail:
- `strict-automata-yield-odd-one-rest-hilbert-hotels`: a strict one-rest automaton of odd type that never lowers the
  finite active count. By `free-orbit-label-lifts-need-count-raising-label-automata` this is necessary for every label
  lift.
- `odd-one-rest-hilbert-hotels-carry-affine-relays`: such an automaton, over some group, with an integral affine relay.

**Heuristic remark, not a claim.** On a region where all windows carry one fixed label pattern, the rows of `A_ℓ`
come from a single element `α = Σ_m a_m m` of `Z[G]` with augmentation `1`, and (R3) there asks `α` to act injectively
on `(Z/p)^G` for every `p`. A non-donor relay therefore uses, locally, elements of `F_p[G]` other than monomials that
act injectively. Over groups where every such element is a monomial, affine relays reduce to donors on those regions.
This links the relay problem to unit and zero-divisor questions for `F_p[G]`.

**Calibration** (`experiments/affine-relay-lifts-2026-09-17/check.py`). Over `C_n`, exhaustively, for lifts of label
shifts `ℓ ↦ π∘ℓ(·+1)` with random integer relays, `θ_n` commutes with translation and with `Z/n` and lifts `τ`. It is
injective exactly when every `A_ℓ` is injective mod `q`. Both outcomes occur: 23 of 30, 15 of 30, 5 of 20, 4 of 20 and
0 of 5 relays are injective at `(n,|B|,q) = (3,1,3), (4,1,3), (3,2,3), (4,1,5), (3,3,5)`.
