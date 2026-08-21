# A relative-commutant reduction of the non-hyperlinear group problem

**2026-08-21.** This note records, self-containedly, the sharpest reduction
obtained this session of the open problem *"does a non-hyperlinear group
exist?"* to a single operator-algebra statement about an explicit
commensurated arithmetic inclusion, together with the closure of the near
sector of the Dogon--Vigdorovich question. Nothing here produces a
non-hyperlinear group unconditionally; the point is that the entire
remaining obstacle is now one clean, recognizable conjecture.

## 1. The HNN construction and its reduction

Let `A` be a finitely generated group and `C <= A` a finitely generated
**co-dense** subgroup: `rho(C)' = rho(A)'` for every finite-dimensional
unitary representation `rho` of `A` (equivalently, `C` surjects onto every
finite quotient through which the finite-dimensional representations of `A`
factor). Fix `a_1 in A \ C` and form the HNN extension

    G = < A, t | [t, c] = 1  (c in C) >  =  A *_C (C x Z).

By Britton's lemma `w := [t, a_1] != 1` in `G`.

**Reduction theorem.** Let `M = prod_U M_{d_n}` be a tracial matrix
ultraproduct and suppose `G` is hyperlinear, so there is a trace-preserving
embedding `L(G) -> M`. Write `pi : A -> U(M)` for the restriction (its trace
is the regular trace `tau_A`) and `k = image of t in U(M)`. Then `[k,
pi(c)] = 0` for all `c in C`, i.e. `k in pi(C)' cap M`. Consequently, if

    pi(C)' cap M  =  pi(A)' cap M                                    (RCC)

then `k` commutes with `pi(a_1)`, so `pi(w) = [k, pi(a_1)] = 1`; but `w` is
a nontrivial group element, so its regular trace is `0`, whereas `tau(1) =
1`. Contradiction. **Hence `(RCC)` implies `G` is not hyperlinear.**

The inclusion `pi(A)' cap M subseteq pi(C)' cap M` is automatic; the content
of `(RCC)` is the reverse. This is exactly the Kun--Thom / Alekseev--Thom
approximate relative-commutant collapse (Open Problem 6.2), here for the
pair `(A, C)`.

## 2. The explicit arithmetic instances

**`SL_2` instance.** `C = SL_2(Z) <= A = SL_2(Z[1/2])`. Co-density holds:
every finite-dimensional unitary representation of `A` factors through a
congruence quotient `SL_2(Z/m)`, `gcd(m,2) = 1` (a unipotent is conjugate to
its square by `diag(2,1/2)`, forcing finite odd order; Serre's congruence
subgroup property), and `SL_2(Z)` surjects onto each by strong
approximation. `C` is **commensurated** by `A`, with Schlichting completion
`SL_2(Q_2) supseteq SL_2(Z_2)`. So `(RCC)` is a statement about the Hecke
inclusion `L(SL_2(Z)) subseteq L(SL_2(Z[1/2]))` realized in `M`. Caveat:
`SL_2(Z)` has the Haagerup property, so `L(SL_2(Z))` has no intrinsic
spectral gap, and `(RCC)` for this pair may be delicate or false.

**`SL_3` instance (better).** `C = SL_3(Z) <= A = SL_3(Z[1/2])`,
`h = diag(2,1,1/2)`. Now `C` has **property (T)**, so `L(C)` has a genuine
spectral gap in any ambient `M`. Two simplifications:

- `A = <C, h>`: every half-integer elementary matrix `e_{ij}(1/2^m)` is an
  `h`-power conjugate of an integer one, so `(RCC)` for this pair holds iff
  every `k in pi(C)' cap M` commutes with `pi(h)` -- a **single**
  commutation.
- `h` expands the upper unipotent `U_+(Z) subseteq C` into itself, so both
  `k` and `k^h = pi(h) k pi(h)^{-1}` commute with a finite-index subgroup of
  `pi(U_+(Z))`.

The open point is sharp: the single expanding automorphism `h` must fix the
`(T)`-rigid space `pi(C)' cap M` pointwise. This route uses no central
extension, so unlike Dogon--Vigdorovich it is **not** constrained to groups
with `pi_1(G(R))` infinite; every higher-rank `SL_n`, `Sp_{2g}`, etc. is
admissible.

## 3. Why the near-sector obstruction is gone (the DV branch)

The Dogon--Vigdorovich question (flexible HS-stability of `SL_2(Z[1/2])`,
equivalently their Iwahori local-global problem) splits at the compatible
(congruence) locus:

- **Near sector -- now a theorem.** For a congruence representation `rho`,
  the Mayer--Vietoris mismatch map on `Z^1(SL_2(Z), Ad rho) (+) Z^1(SL_2(Z)^t,
  Ad rho)` has kernel exactly the diagonal coboundaries (so `H^1(SL_2(Z[1/2]),
  Ad rho) = 0`) and a **uniform** smallest nonzero singular value `sigma_0`:
  the cuspidal part is bounded by Deligne's `|a_2| <= 2 sqrt 2 < 3` through
  the degeneracy-map Gram identity `3||f||^2 + 3||g||^2 - 2 Re<f, T_2 g>`,
  the Eisenstein part has Gram matrix `5I - 2[[0,A],[A^T,0]]` with `A` a
  degree-two cusp incidence (singular values exactly in `[1,3]`, verified for
  all primes up to 101), and the cochain-vs-harmonic norm comparison is
  rank-uniform (Whitney/de Rham on a fixed orbifold). Newton--Kantorovich,
  using this dimension-free right inverse and the fixed-word second-derivative
  bound `L`, gives `D(pi) <= (2/sigma_0) def(pi)` for every representation
  within the tube of radius `sigma_0^2/(8L)` of the compatible locus.

- **Far sector.** Representations of small defect far from every congruence
  representation. Two facts make this purely a non-amenable-coupling problem:
  the parabolic spectral measure lives on the 2-adic solenoid and is
  approximately invariant under the `x4` automorphism `alpha`, whose measure
  rigidity holds unconditionally for a *single* automorphism (Marcus; dense
  periodic measures, Levit--Vigdorovich), because `Z[1/2]` inverts only one
  prime; and every character is a limit of finite-dimensional traces
  (Peterson--Thom character rigidity), so the trace side is settled. The
  far sector is therefore the SAME statement as `(RCC)`: the collapse of the
  relative commutant of the non-amenable `L(SL_2(Z[1/2]))`.

## 4. Landscape

Every published route to a non-hyperlinear group -- Dogon's central
extensions of `Sp_{2g}(Z)` / random `(T)` groups / infinitely-presented
`(T)` groups (needing flexible HS-stability, or the weaker weak
ucp-stability), Dogon--Vigdorovich's `SL_2(Z[1/p])`, and this
relative-commutant route -- reduces to the same open core: a stability /
ucp / relative-commutant rigidity for a property-(T) or -(T;FD) group.
`LLP => weak ucp-stability`, but no infinite `(T)` group is known to have
`LLP` or to be weakly ucp-stable (and a hyperlinear `(T)` weakly-ucp-stable
group is residually finite, Dogon Prop 1.11), so this is not a shortcut but
the same difficulty. The tools flagged for `(RCC)` are Popa deformation/
rigidity for the commensurated Hecke inclusion, proper proximality of
`SL_n(Z)`, and property-(T) spectral gap in the `SL_3` instance.

**Status: open.** The goal is now a single named conjecture, `(RCC)`, for
an explicit commensurated arithmetic inclusion, with the Dogon--Vigdorovich
near sector fully closed.

## 5. The 1-bounded-entropy analysis of `(RCC)` (`SL_3` instance)

For `A = L(SL_3(Z)) subseteq B = L(SL_3(Z[1/2])) subseteq M` the following
are all worked out and correct; together they locate the exact open point.

1. **`A` is an irreducible subfactor of `B`.** `SL_3(Z)` is *relatively icc*
   in `SL_3(Z[1/2])` (every non-central `g` has finite `SL_3(Z)`-centralizer,
   hence infinite `SL_3(Z)`-conjugacy class), so `A' cap B = C`. Thus `(RCC)`
   `A' cap M = B' cap M` is a **commutant-absorption**: the relative commutant
   of `A` must not grow, on passing from `B` to `M`, beyond `B' cap M`.

2. **Both algebras are strongly 1-bounded.** `SL_3(Z)` and `SL_3(Z[1/2])`
   have property (T), so `h(A) = h(B) = 0` (Jung; Hayes, arXiv:1505.06682).

3. **The relative commutant sits in an `h = 0` algebra.** `SL_3(Z)` is
   commensurated by `SL_3(Z[1/2])`, so every `g in SL_3(Z[1/2])`
   wq-normalizes `SL_3(Z)`; and any `u in A' cap M` satisfies `u^* A u = A`,
   so it wq-normalizes `A`. Hence both `B` and `A' cap M` lie in
   `W^*(wqN_M(A))`, and by Hayes' monotonicity
   `h(W^*(wqN_M(A)) : M) <= h(A : M) = 0`. In particular `A' cap M` is
   strongly 1-bounded and contains no free-group-factor as a regular piece --
   the rigidity the Haagerup `SL_2(Z)` cannot supply, and the reason the
   `SL_3` instance is the promising one.

4. **`A = <SL_3(Z), h>` reduces `(RCC)` to one commutation.** With
   `h = diag(2,1,1/2)`, every half-integer elementary matrix is an
   `h`-conjugate of an integer one, so `SL_3(Z[1/2]) = <SL_3(Z), h>` and
   `(RCC)` holds iff every `k in A' cap M` commutes with `pi(h)`.

5. **Where it stops (the exact open point).** `h = 0` alone does NOT force
   `A' cap M subseteq B' cap M`: an amenable extension `B <= <B, k>` with
   `k in A' cap M setminus B' cap M` also has `h = 0`. So the entropy
   invariant constrains the size of `A' cap M` without delivering the
   absorption. `(RCC)` for the `SL_3` pair is therefore equivalent to:

   > the expanding commensuration `Ad(h)` acts trivially on the
   > strongly-1-bounded relative commutant `A' cap M`.

   This is a 1-bounded-entropy **absorption** statement of the exact kind
   proved (with heavy machinery, over years) for free group factors in the
   Peterson--Thom programme, now for a commensurated property-(T)
   arithmetic inclusion. It is open, and it is the whole remaining obstacle
   between this reduction and a non-hyperlinear group.

**Caveat proved along the way.** One cannot strengthen `(RCC)` to
`A' cap M = C`: in the hyperlinear scenario the HNN letter forces
`L(<t>) = L(Z) subseteq A' cap M`, since `C_G(SL_3(Z)) = <t>`. The content
is only the inclusion `A' cap M subseteq B' cap M`, which the single element
`k = u_t` violates precisely when `G` is hyperlinear.

## 6. A new flagship conditional route: the plain lattice `SL_n(Z)`

(Added 2026-08-21, from a literature survey; all citations verified.)

The HNN reduction of Section 1 applies to `A = SL_n(Z)` itself (`n >= 3`),
giving the cleanest conditional statement in the program.

**Theorem (citation assembly + the HNN theorem).** Let `n >= 3` and let
`C = <g_1, g_2> <= SL_n(Z)` be a saturated Zariski-dense free subgroup (thin;
surjecting onto `SL_n(Z/m)` for every `m`). Then `(SL_n(Z), C)` satisfies
every hypothesis of the HNN theorem:

- Every finite-dimensional unitary representation of `SL_n(Z)` factors
  through a congruence quotient `SL_n(Z/m)` (Margulis superrigidity: a
  homomorphism to a compact group has finite image; Bass--Milnor--Serre
  congruence subgroup property).
- Co-density: `C` saturated surjects onto every `SL_n(Z/m)` (strong
  approximation, Matthews--Vaserstein--Weisfeiler/Nori, + generator choice),
  so `rho(C) = rho(A)` for every finite-dimensional `rho`.
- Uniform gap `= (tau)`: **Bourgain--Varju**, *Expansion in `SL_d(Z/qZ)`,
  `q` arbitrary* (Invent. Math. 188 (2012) 151--173): the Cayley graphs of
  `pi_m(C) = SL_n(Z/m)` are uniform expanders over ARBITRARY modulus, which
  is exactly property `(tau)` of `C` over the family of quotients through
  which all finite-dimensional representations of `A` factor.

Consequently, **if `SL_n(Z)` is flexibly Hilbert--Schmidt stable, then**
`G = <SL_n(Z), t | [t, C] = 1>` **is a finitely presented non-hyperlinear
group.** (Permutation twin: flexible permutation stability of `SL_n(Z)`
implies `G` is non-sofic -- the HNN analogue of Bowen--Burton, from `n = 3`.)

**Why it is new and central.** Neither published route reaches the plain
lattice: Dogon (arXiv:2211.10492) needs a central extension by a torsion-free
`Z`, but `K_2(Z) = Z/2` is finite and there is no Deligne extension;
Dogon--Vigdorovich (arXiv:2506.20843) needs an archimedean factor with
`pi_1 = Z`, but `pi_1(SL_n(R)) = Z/2`. The commutant/HNN route uses neither.
So this converts the program's single open hypothesis into the flexible
HS-stability of the most-studied lattice in the subject, on which any future
progress by anyone -- either direction -- resolves the conditional.

**The definitive obstruction census.** Two independent literature surveys
confirm: no published group is flexibly HS-stable (or weakly ucp-stable),
non-amenable, and equipped with an infinite co-dense Kazhdan subgroup. Two
fences show no known permanence operation produces one -- (A) an infinite
residually finite amenable quotient kills the uniform gap via Folner
deformations; (B) LERF kills co-density via separability -- and every
published non-amenable stable group (free / virtually free, one-relator with
center, chordal graph products, amalgams over finite subgroups, products with
amenable groups) hits A or B, with its (T) subgroups provably finite. Hence
the goal genuinely requires a NEW flexible-stability theorem for a
congruence-rigid group; the candidate list is `SL_2(Z[1/p])`,
`SL_2(Z[1/pq])`, `SL_3(Z[1/p])`, `Sp_4(Z)`, and `SL_n(Z)` (`n >= 3`), all
carrying the identical single open hypothesis.

**The sharpest published tools toward that hypothesis.** de la Salle
(arXiv:2204.07084): finite groups are flexibly stable with a linear
dimension-free modulus in any tracial target (so inside the matrix
ultraproduct), with a subgroup-relative correction (Lemma 1.7) and an
almost-commuting-to-commuting corollary -- reducing the far sector, with
explicit constants, to a length-control estimate for the congruence relator
family against the exponential Dehn function of the S-arithmetic group
(Taback, arXiv:math/0302191). Dogon--Vidick (arXiv:2607.20135, 2026):
effective approximate-invariant-measure machinery, the natural route to a
polynomial stability modulus for the `BS(1,4)` skeleton that controls the
parabolic direction.

**Status: open, and now optimally reduced.** A non-hyperlinear group exists
if any one of the listed congruence-rigid lattices is flexibly HS-stable;
`SL_n(Z)` is the cleanest and most central target. No shortcut exists in the
literature through August 2026.
