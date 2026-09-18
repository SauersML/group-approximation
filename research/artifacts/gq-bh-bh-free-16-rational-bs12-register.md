# Rational BS(1,2) in a twisted Brin–Thompson group over 2V_τ: an attempt and its exact gap (lane bh-free-16, 2026-09-18)

Target: `Q ⋊ ⟨2⟩` (the group of maps `x ↦ 2^k x + q`, `q ∈ Q`) inside a finitely presented simple group. It is the first
non-abelian stepping stone of `Aff(Q)` and of BBMZ Problem 5.3(5), and it contains `BS(1,2)`. Nothing here is a claim;
it records one design, what checks, and where it stops. No local compute; nothing reviewed.

## 1. Setup (all ingredients are on main)

- Actor `G = 2V_τ` (`odometer-2v-is-fp-simple-and-contains-bs12`): finitely presented, simple, a topological full group
  (hence full), containing `2V` (hence clopen-transitive), and containing `BS(1,2) = ⟨s, u | u s u^-1 = s^2⟩` with
  `s = τ × id` and `u` the inverse baker map.
- Type (A): by `fp-clopen-transitive-full-cantor-groups-have-type-a-actions` (lane proof), `G` acts on its clopen sets
  with finitely many orbits of pairs and finitely generated stabilizers. Adjoin one global fixed point `*`
  (the fixed-point remark in `twisted-bt-point-fixing-actor-elements-are-divisible`): still type (A), so
  `SV_G` with `S = Clopen(C²) ⊔ {*}` is finitely presented and simple (`twisted-brin-thompson-finite-presentation-criterion`).
- Every element of `G` fixes `*` and acts on coordinate `*` as the identity without reading it. So by
  `twisted-bt-point-fixing-actor-elements-are-divisible`, every infinite-order `g ∈ G` has a register tower
  `R_n(g)` on coordinate `*` ("add 1 in the first `n` mixed-radix digits of coordinate `*`; on overflow apply `g`"),
  with `R_n(g)^(n+1) = R_(n-1)(g)`, `R_0(g) = g`, and `∪⟨R_n(g)⟩ ≅ Q`. Call this copy `Q_g`.

So `SV_G` contains `BS(1,2)` and a copy of `Q` through `s`. This much answers the objection recorded in
`research/artifacts/gq-bt-kojima-mechanism.md` §4.2 ("that actor action is not of type (A)"): the actor can be of
type (A) and still contain the dilation.

## 2. What conjugation by the dilation does (checked by hand)

- Since `u` fixes coordinate `*` and ignores it, `u R_n(g) u^-1 = R_n(u g u^-1)` for all `n` and all `g`.
- Hence `u Q_s u^-1 = Q_(s^2)`: the dilation carries the register tower of `s` to the register tower of `s^2`, not to
  the squares of the tower of `s`. The two copies of `Q` share `s^2`, but `R_1(s^2) ≠ R_1(s)^2` (the first cycles the
  register at unit speed with double overflow, the second at double speed with single overflow). So `u` does not
  normalize `Q_s`, and `⟨Q_s, u⟩` is not `Q ⋊ ⟨2⟩` in any evident way.

## 3. Why the natural corrections fail

To get `Q ⋊ ⟨2⟩` one must replace `u` by `u' = u ∘ ψ` with `ψ` acting on the register so that `u' R_n(s) u'^-1 = R_n(s)^2`.
On values `f ∈ [0,1)` of the register this forces `ψ` to be `f ↦ 2f` with the integer part fed to the overflow.

- **Radix-2 first digit.** Then `{2f}` is a one-digit shift and `⌊2f⌋` is the first digit, so `ψ` is bounded. But the
  map `(x, f) ↦ (s^(d_1(f)) u(x), {2f})` is a bijection of `C² × C` only if the rest space splits as
  `X = u(X') ⊔ s u(X')` for a clopen `X'`, i.e. only if `s` acts with a clopen fundamental domain ("translation-like").
  For `s = τ × id` it does not: `τ` is minimal on every fibre. The formal identity `u' R_1(s) = s u'` holds, but `u'`
  is not injective.
- **Odd radices.** For a register with infinitely many odd radices, `f ↦ 2f` changes the tail of the digit string at
  points of unbounded carry depth, so it is not a bounded prefix rewrite anywhere; this is the carry obstruction of
  the Kojima artifact §4.2, here in the precise form "within the register coordinate". Moving the register's digits
  across several coordinates permuted by `u` changes the radix pattern at each dilation (the first even radix is
  halved), and a fixed register space invariant under this with infinitely many odd radices needs a radix conversion
  with unbounded look-ahead.

## 4. Exact remaining gap (a precise next question)

The design works if and only if the actor supplies a copy of `BS(1,2) = ⟨a, u⟩` in which `a` is translation-like on
the rest space: a clopen `D` with `a^k(D)` pairwise disjoint and `u(D) = D ⊔ a(D)` up to a clopen correction. In
Cantor hosts such an `a` has attracting and repelling behaviour, which is the V-type dynamics that
`thompson-v` undistortion forbids for `BS(1,2) ≤ V`. So the question becomes:

> Does some finitely presented full clopen-transitive Cantor group (a type (A) actor) contain `BS(1,2) = ⟨a, u⟩` with
> `a` translation-like on some clopen set?

A yes gives `Q ⋊ ⟨2⟩` in a finitely presented simple group by §1–§3 (radix-2 dilation plus the odd-radix tower on a
second fixed coordinate, still to be checked). A no would show that this whole family of twisted Brin–Thompson
designs cannot reach `Q ⋊ ⟨2⟩`.

## 5. Checked along the way, not new

- `V` contains every countable locally finite group (Higman; the free cone-permutation direct limit gives a short
  proof). Already used on main in `countable-virtually-abelian-groups-embed-in-2v`.
- `VA` (Belk–Hyde–Matucci) is full, contains `V`, and contains `⊕_ω(A ⊕ V)` with `A` Brin's group. Combining it with
  `DV_F` adds nothing beyond `one-fp-simple-group-contains-every-brin-thompson-subgroup`.
