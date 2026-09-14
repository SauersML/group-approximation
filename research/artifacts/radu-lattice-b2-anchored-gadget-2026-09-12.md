# Radius-two gadgets on Radu's lattice: only the mark folds

Lane `w7-radu-gadget-b4`, 2026-09-12. Handwritten proofs; nothing was run.
Supports `radu-lattice-radius-two-pairs-force-the-mark-into-the-radical`. Extends Section 5 of
`radu-lattice-anchored-linear-gadgets-2026-09-12.md` (the survivor shape) and Section 5 of
`radu-lattice-strict-automaton-screens-2026-09-12.md`.

**Directive.** Decide the smallest nonlinear anchored gadget on `Gamma_R`: both memories in `B_2`, an
anchored identification, and a Garden of Eden in `B_4` separating `(zx)^2` from `(xz)^2`.

**Outcome.**
* Proved on paper, given Remark 3.6. The claim is held OPEN until w7-vf-nonlinear passes it. The survivor shape is forced. With both memories in `B_2`, exactly one
  cell pair folds over `Gamma_R / Gamma_0`. So `xz` and `zx` are addresses of both memories and both
  rules read them. The image of `tau` contains every `delta^4`-invariant configuration. Every strict
  pair of this size puts `delta^4` in the sofic radical of `Gamma_R`.
* Refuted: nothing. No rule pair was proposed, so there is no collision certificate.
* Open: whether any rule pair of this size is strict. Every blocker known at this size is a quotient
  of `Gamma_R` in which `delta^4` survives.

## 0. Setting

* `Gamma_R = < a,b,c,x,y,z | a^2,b^2,c^2,x^2,y^2,z^2, axax, ayay, azbz, bxbx, bycy, cxcz >`, with horizontal
  letters `a,b,c` and vertical letters `x,y,z`. Every element has a unique normal form `alpha omega`:
  `alpha` is a reduced word in `a,b,c`, `omega` is a reduced word in `x,y,z`, and the length is
  `|alpha| + |omega|`. Read backwards, the square table gives `v h = h' v'` for every vertical `v` and
  horizontal `h`, because all letters are involutions.
* Every relator has even length. So length parity is a homomorphism `Gamma_R -> Z/2`, and the finite
  residual `Gamma_0` consists of even-length elements.
* **(R)** Remark 3.6 of Titz Mite--Witzel, imported by `radu-bmw-lattice-embeds-in-titz-witzel-kernel`, in
  the reading of `radu-lattice-one-sided-pairs-need-residual-coincidences`: the nontrivial elements of
  `Gamma_0` of length at most eight are `delta^4` and `delta^-4`, where `delta = xz`. Every step below
  that uses `Gamma_0 ∩ B_8` depends on this reading.
* Designs `D = (A,S,M,nu,mu)`, the forward table `E_rho` on `S x M`, the reverse table `F_rho` on
  `M x S`, the up-sets `𝓕_D`, `𝓡_D`, the table groups `U_E` and Lemmas 1, 2, 3, 5 are those of
  `canonical-table-groups-for-automaton-designs-2026-09-12.md`. Here addresses are group elements and
  `rho` is the inclusion. Write `Psi_F` for the reverse composite and `e` for the marked class.
* `Rad(G)` is the sofic radical of `sofic-radical-localizes-garden-of-eden-windows`: the intersection
  of the kernels of all homomorphisms from `G` into sofic groups. For `H <= Gamma_R`, `Rad(H)` lies in
  the finite residual of `H`, because `H` modulo that residual is residually finite, hence sofic. That
  residual lies in `Gamma_0`, because every finite-index subgroup of `Gamma_R` meets `H` in a
  finite-index subgroup.

## 1. The canonical window

**Lemma 1.1.** Let `sigma tau = id` over a group `G` with `tau` not surjective. Then some `y` and `g`
have `tau sigma(y)(g) != y(g)`, and the restriction of `y` to `g(MS ∪ {1})` is a Garden of Eden.

*Proof.* If `tau sigma = id`, then `tau` is surjective, so such `y, g` exist. The value `tau sigma(y')(g)`
depends only on `y'` on `gMS`. If `y'` agrees with `y` on `g(MS ∪ {1})`, then
`tau sigma(y')(g) != y'(g)`. But every `y' = tau x` has `tau sigma y' = tau(sigma tau x) = y'`. QED

With `S, M ⊆ B_2` the window `MS ∪ {1}` lies in `B_4`.

## 2. Folding at radius four

**Lemma 2.1 (normal forms).**
1. If `g` and `g delta^4` lie in `B_4`, then `g = (zx)^2` and `g delta^4 = (xz)^2`. If `g` and
   `g delta^-4` lie in `B_4`, then `g = (xz)^2`.
2. If `m, s in B_2` and `ms = (zx)^2`, then `m = s = zx`. If `ms = (xz)^2`, then `m = s = xz`.

*Proof.* 1. Write `g = alpha omega`. Since `delta^4 = xzxzxzxz` is vertical, `g delta^4` has normal form
`alpha omega'`, where `omega'` is the reduction of `omega xzxzxzxz`. Reduction cancels at most
`|omega|` letters from each side, so `|omega'| >= 8 - |omega|`. From `|alpha| + 8 - |omega| <= 4` and
`|alpha| + |omega| <= 4` we get `alpha = 1`, `|omega| = 4`, and all four letters of `omega` cancel.
So `omega = (xzxz)^-1 = zxzx` and `g delta^4 = xzxz`. For `delta^-4`, apply this to `g delta^-4`.

2. Write `m = alpha_m omega_m` and `s = alpha_s omega_s`. Moving the letters of `alpha_s` leftwards
through `omega_m` with `v h = h' v'` gives `omega_m alpha_s = alpha' omega'`, with `|alpha'| = |alpha_s|`
and `|omega'| = |omega_m|`. So `ms` has normal form `red(alpha_m alpha') red(omega' omega_s)`. For
`ms = zxzx` the horizontal part is empty, and

    4 = |red(omega' omega_s)| <= |omega_m| + |omega_s| <= 4 - |alpha_m| - |alpha_s|.

So `alpha_m = alpha_s = 1`. Then `|omega_m| = |omega_s| = 2`, `omega' = omega_m`, and `zx zx` arises with
no cancellation, so `m = s = zx`. The case `(xz)^2` is symmetric. QED

**Theorem 2.2 (radius-two pairs).** Let `S, M ⊆ B_2` contain `1`, let `sigma tau = id` over `Gamma_R`,
and let `tau` not be surjective. Put `c_+ = (zx,zx)` and `c_- = (xz,xz)` in `M x S`, and let
`q : Gamma_R -> Q = Gamma_R / Gamma_0`.
1. **Addresses.** `zx` and `xz` lie in `M ∩ S`, and `c_+`, `c_-` are singleton classes of `F_rho`.
2. **One fold.** `F_(q rho)` is `F_rho` with `c_+` and `c_-` merged. It lies in `𝓡_D`, and `F_rho` does not.
3. **Essential coordinates.** `mu` depends on its coordinates `zx` and `xz`, and so does `nu`.
4. **Pointwise image.** `tau sigma(y)(g) = y(g)` whenever `y(g(zx)^2) = y(g(xz)^2)`. So the image of
   `tau` contains every `y` with `y(h delta^4) = y(h)` for all `h`.
5. **Garden of Eden shape.** A pattern on a window `Omega ⊆ g B_4` is a Garden of Eden only if
   `Omega` contains `g(zx)^2` and `g(xz)^2` and the pattern differs there.

*Proof.* 1 and 2. `Q` is residually finite, hence surjunctive (`residually-finite-groups-are-surjunctive`).
`E_(q rho) >= E_rho` lies in `𝓕_D` (Lemma 2). So `tau` over `Q` is injective (Lemma 3), hence surjective,
so `F_(q rho)` lies in `𝓡_D`. Lemma 3 over `Gamma_R` gives that `F_rho` does not.
* Two cells `(m,s)`, `(m',s')` fold under `q` iff `(ms)^-1 m's'` lies in `Gamma_0`. Both products lie in
  `B_4`, so the difference lies in `B_8`, and by (R) it is `1` or `delta^(+-4)`.
* A cell joins the marked class under `q` iff `ms` lies in `Gamma_0 ∩ B_4 = {1}`, so the marked class
  does not change.
* A fold by `delta^(+-4)` pairs `(zx)^2` with `(xz)^2` (Lemma 2.1(1)). The only cells with these
  products are `c_+` and `c_-` (Lemma 2.1(2)).

So `F_(q rho)` is either `F_rho` or `F_rho` with `c_+ ~ c_-`. The first is excluded, so both cells exist
and fold.

3. Suppose `mu` ignores its coordinate `zx`. The singleton class `c_+` is read only through that
coordinate, so `Psi_(F_rho)(y)` does not depend on `y[c_+]`. Replace `y[c_+]` by `y[c_-]`. The new
assignment is constant on the classes of `F_(q rho)`, so by the proof of Lemma 2
`Psi_(F_rho)(y) = y[e]`. Then `F_rho` lies in `𝓡_D`, a contradiction. The same argument handles `xz`
with `c_-`, and handles `nu`, which reads `c_+` through its coordinate `zx` inside the slot `m = zx`.

4. By Lemma 1, `tau sigma(y)(g) = Psi_(F_rho)(y_g)` with `y_g[(m,s)] = y(g ms)`. The assignment `y_g`
is a function of the product `ms`, and it agrees on `c_+` and `c_-` by hypothesis. So it is constant on
the classes of `F_(q rho)`, and `Psi_(F_rho)(y_g) = Psi_(F_(q rho))(y_g) = y_g[e] = y(g)`. For the second
sentence put `h = g(zx)^2`, so that `h delta^4 = g(xz)^2`.

5. If `h` and `h delta^(4k)` lie in `Omega` with `k != 0`, then `8|k| = |delta^(4k)| <= 8`, so `k = +-1`.
By Lemma 2.1(1) the pair is `{g(zx)^2, g(xz)^2}`. If the pattern does not separate that pair, it is
constant on each set `Omega ∩ h<delta^4>`. So it extends to a configuration constant on every coset
`h<delta^4>`, which lies in the image of `tau` by item 4. QED

**Remark 2.3.** The same proof applies to `S ⊆ B_r` and `M ⊆ B_(4-r)` for `r = 1` or `3`. It forces the
prefixes of length `4 - r` of `zxzx` and `xzxz` into `M`, and their suffixes of length `r` into `S`.
For `r = 0` or `4` one rule acts letter by letter, and no strict pair exists.

## 3. The mark and the sofic radical

**Theorem 3.1.** Let `sigma tau = id` over `Gamma_R` with `tau` not surjective. Suppose some Garden of Eden
window `Omega` has `Omega^-1 Omega ⊆ B_8`; for example `S, M ⊆ B_2`, by Lemma 1.1. Then `delta^4` lies in
`Rad(<M>)`, which lies in `Rad(Gamma_R)`. In particular `Gamma_R` is not sofic.

*Proof.* By `sofic-radical-localizes-garden-of-eden-windows`, some nontrivial `k` in `Omega^-1 Omega`
lies in `Rad(<M>)`, and that node also gives `Rad(<M>) ⊆ Rad(Gamma_R)`. By Section 0, `Rad(<M>)` lies in
`Gamma_0`. Since `|k| <= 8`, (R) gives `k = delta^(+-4)`. QED

**Corollary 3.2 (what blocks the family).** The following equivalent conditions exclude every strict
pair with a Garden of Eden window of diameter at most eight, in particular every pair of Theorem 2.2:
1. some homomorphism from `Gamma_R` into a sofic group does not kill `delta^4`;
2. `delta^4` does not lie in `Rad(Gamma_R)`.

Soficity of `Gamma_R` implies both. Conversely, a single strict pair of Theorem 2.2 proves that `delta^4`
lies in `Rad(Gamma_R)`. That is the membership which `radu-commutator-collapse` would give through
`radu-mark-is-controlled-by-one-commutator`, and it would show that nonsofic groups exist.

**Known quotients.** Three quotients of `Gamma_R` are on record.
* **Residually finite quotient.** `Q = Gamma_R / Gamma_0` kills `delta^4`.
* **Horizontal tree group.** `Gamma_R / Lambda_v` kills `delta^2`
  (`radu-horizontal-projection-kills-delta-squared`).
* **Vertical tree group.** `Gamma_R / Lambda_h` keeps `delta^4`, where `T_v = Gamma_R / A` and
  `Lambda_h = ker(Gamma_R -> Aut(T_v))`. Indeed `Lambda_h` fixes the root `A`, so it lies in `A`. By
  normal forms `A ∩ V = 1`, and `delta^4` is a nontrivial element of `V`.

So the vertical tree group is the one candidate blocker on record.
* If it is sofic, no pair of Theorem 2.2 exists.
* If a pair of Theorem 2.2 exists, it is nonsofic.
* Whether `Lambda_h` is nontrivial is not recorded. If `Lambda_h = 1`, the candidate is `Gamma_R` itself.
  In the level data of `titz-witzel-radu-sublattice-2026-09-11.md`, Section 4, no reduced word in
  `a,b,c` of length at most ten acts trivially on level ten.

**Proposition 3.3 (no exact blocker short of the mark).** Suppose `B_1 ⊆ S ∩ M ⊆ B_2`.
1. `U_(E_rho)` is isomorphic to `Gamma_R`, by `x_t -> t` on letters.
2. Take the canonical window `Omega = MS ∪ {1}`, and let `phi` be a map into a group `K` as in the
   Theorem of `strict-pairs-transfer-to-table-realizations`, with `phi((zx)^2) != phi((xz)^2)`. Then
   `t -> phi(t)` extends to a homomorphism `psi : Gamma_R -> K` with `psi(delta^4) != 1`.

By Theorem 2.2(5) every Garden of Eden in `B_4` distinguishes `(zx)^2` from `(xz)^2`. So a transfer
into any group that kills `delta^4` cannot exclude such a design; finite and residually finite groups
kill it. A transfer blocker gives a quotient of `Gamma_R` in which `delta^4` survives, and when that
quotient is sofic this is Corollary 3.2(1).

*Proof.* 1. For a letter `t`, the classes `(t,1) ~ (1,t)` and `(t,t)` in `e` give `x_t^S = x_t^M` with
square `1`. Each square `hv = v'h'` gives cells `(h,v) ~ (v',h')` in `S x M`, so all six relators hold.
An address `g = t_1 t_2` of length two gives `(g,1) ~ (t_1,t_2)` or `(1,g) ~ (t_1,t_2)`, so `x_g` is a
product of letters. Hence `t -> x_t` is a surjective homomorphism `Gamma_R -> U_(E_rho)`, and the
homomorphism of Lemma 5 inverts it.

2. `phi(1) = phi(1)^2` gives `phi(1) = 1`. Every letter lies in `S` and in `M`, so `phi(t)^2 = phi(tt) = 1`
and `phi(h) phi(v) = phi(hv) = phi(v'h') = phi(v') phi(h')`. So `psi` exists. Since `zx = zx·1` lies in
`Omega` and `zx` lies in `M`, `phi((zx)^2) = phi(zx)^2 = (phi(z) phi(x))^2 = psi((zx)^2)`, and likewise
for `(xz)^2`. Hence `psi(delta^4) = psi((zx)^2)^-1 psi((xz)^2) != 1`. QED

**Proposition 3.4 (table groups).** Under Theorem 2.2, let `E` lie in `𝓕_D` with `E <= E_rho`. Let

    h_E = (x^S_xz)^-1 (x^M_xz)^-1 x^M_zx x^S_zx

be the hinge of `c_+ ~ c_-` in `U_E`. Then `h_E` maps to `delta^-4` and lies in `Rad(U_E)`, so `U_E` is not
sofic. So a rule pair is excluded once one forward-sufficient partition below `E_rho` has a table
group with a sofic quotient that does not kill `h_E`.

*Proof.* Lemma 5 gives `pi : U_E -> Gamma_R` with `pi rho_E = rho` and `F_(rho_E) <= F_rho`. Put
`K = U_E / Rad(U_E)`, which is sofic, hence surjunctive (`sofic-groups-are-surjunctive`).
* The induced realization has forward table `>= E`, so `tau` over `K` is injective and its reverse
  table `F_K` lies in `𝓡_D`.
* Since `F_rho` does not, Lemma 2 gives `F_K ≰ F_rho`. Either a cell pair folds in `K` but not in
  `Gamma_R`, or a cell joins the marked class in `K` but not in `Gamma_R`.
* The corresponding word, a hinge or `x_m x_s`, lies in `Rad(U_E)`. `pi(Rad(U_E))` lies in
  `Rad(pi(U_E))`, since `U_E -> pi(U_E) -> pi(U_E) / Rad(pi(U_E))` maps into a sofic group, and
  `Rad(pi(U_E))` lies in `Gamma_0` (Section 0).
* The image of the word is a nontrivial element of `Gamma_0 ∩ B_4` or of `Gamma_0 ∩ B_8`. The first is
  impossible, so by (R) and Lemma 2.1 the pair is `{c_+, c_-}`. QED

## 4. The template `G_4`

The survivor shape, made concrete.
* **Alphabet.** Any finite `A` with `|A| >= 2`.
* **Memories.** `S = M = B_1 ∪ {xz, zx} = {1, a, b, c, x, y, z, xz, zx}`. This set contains all five
  generating letter sets of item 4 of `radu-lattice-one-sided-pairs-need-residual-coincidences`. By
  Theorem 2.2(1), no memory inside `B_2` can omit `xz` or `zx`.
* **Consistency with the subgroup screens.** By Theorem 3.1, `Rad(<M>)` contains `delta^4`, so `<M>` is not
  sofic. So `M` lies in no conjugate of `P_y` or `P_xz` (`radu-bmw-coordinate-subgroups-are-sofic`): some
  address has `y` in its vertical part, beyond the forced `xz` and `zx`. And `<M>` meets conjugates of `A`
  and of `V` in nonabelian free groups (`nonsofic-subgroups-of-radu-lattice-have-nonamenable-edge-groups`).
  The template satisfies both.
* **Anchored identifications.** Besides `(t,1) ~ (1,t)` and `(1,1) ~ (t,t)`, `E_rho` contains
  `(xz,1) ~ (x,z)`, `(zx,1) ~ (z,x)` and `(1,1) ~ (xz,zx)`.
* **Tables.** Both tables are read from normal forms in `B_4`. `S = M` is closed under inverses, so
  `(s,m) -> (m^-1, s^-1)` carries `E_rho` onto `F_rho`. Over `Q` each table gains exactly one fold:
  `c_+ ~ c_-` in `F`, and `(zx,zx) ~ (xz,xz)` in `E`.
* **Window.** `Omega = MS ∪ {1} ⊆ B_4`. Every Garden of Eden in `B_4` separates `(zx)^2` from `(xz)^2`.
* **Rules.** Not fixed.
  * A pair `(nu, mu)` is strict over `Gamma_R` iff `Phi_(E_rho)` is the projection and `Psi_(F_rho)` is
    not (Lemmas 1 and 3).
  * `Psi` then becomes the projection once `c_+ = c_-`, and `mu` and `nu` must read `xz` and `zx`.
  * Both conditions are finite checks: `|A|^(#classes)` evaluations over tables of 81 cells. No search
    was run, under the no-compute rule.

**Standard tools on `G_4`.**
* **Two- and three-site collisions.** They need a rule, and none was fixed, so there is no certificate.
* **Quotient folding.** It gives Theorem 2.2: the shape, but no certificate.
* **Balance in amenable quotients.** `Gamma_R^ab = (Z/2)^3` is finite and already covered by `Q`. An
  amenable quotient in which `delta^4` survives would be a blocker (Corollary 3.2(1)). None is known.
* **Local embeddings into finite groups.** Impossible (Proposition 3.3(2)).
* **Table groups.** Proposition 3.4 applies to each rule pair separately. For `E = E_rho`,
  `U_E = Gamma_R` (Proposition 3.3(1)).

## 5. Next size

* **Parity.** Residual elements have even length (Section 0). So windows with `Omega^-1 Omega ⊆ B_9` add
  nothing beyond `B_8`. The next size is total radius five, for instance `S ⊆ B_2` and `M ⊆ B_3`, with
  window diameter up to ten.
* **Folds at that size.** Rerunning the proof of Lemma 2.1(1) with bound five forces `|alpha| <= 1`. The
  elements `h` with `h, h delta^4` in `B_5` are seven: `t(zx)^2` for `t = a, b, c`, and `xzx`, `(zx)^2`,
  `yzxzx`, `xzxzx`. Further pairs differ by residual elements of length ten, among them
  `y delta^(+-4) y`. Remark 3.6, as imported, does not list the residual elements of length ten.
* **Radical gate.** At total radius five some nontrivial element of `Gamma_0 ∩ B_10` must lie in
  `Rad(Gamma_R)`. `Rad` is normal. So the gate is still `delta^4` whenever every such element is
  conjugate to `delta^(+-4)`. Escaping the mark needs total radius at least five, together with a
  residual element of length ten outside those two conjugacy classes. Whether such an element exists
  is not decided here.

## 6. Where it stops

* **Proved on paper,** given (R): Lemma 2.1, Theorem 2.2, Theorem 3.1, Propositions 3.3 and 3.4. The claim is
  held OPEN until w7-vf-nonlinear passes these.
* **Not attempted:** a rule search on `G_4`. It is finite for each alphabet but is compute.
* **Open:** whether any rule pair with `S, M ⊆ B_2` is strict. A strict one proves `delta^4` lies in
  `Rad(Gamma_R)`. Any sofic quotient of `Gamma_R` in which `delta^4` survives excludes them all.
* **No weaker blocker:** no invariant weaker than the sofic visibility of `delta^4` is known to block
  the family. Among exact transfers with all letters present there is none (Proposition 3.3).
* **Nothing held for `w3-vf-nonlinear`:** no strict automaton was found.
* **Next lead:** soficity of the vertical tree group `Gamma_R / Lambda_h`, the only quotient on record in which
  `delta^4` survives (Section 3). If it is sofic, the whole family dies. A strict pair would make it
  nonsofic. First decide whether `Lambda_h` is trivial.

## 7. Route held until verification

The claim `radu-lattice-radius-two-pairs-force-the-mark-into-the-radical` is held OPEN. Verification was
requested from w7-vf-nonlinear. After a PASS, add the route `radu-lattice-radius-two-mark-forcing-proof` with

    requires: radu-bmw-lattice-embeds-in-titz-witzel-kernel,
              radu-lattice-one-sided-pairs-need-residual-coincidences,
              strict-automata-live-on-canonical-table-groups,
              strict-pairs-transfer-to-table-realizations,
              residually-finite-groups-are-surjunctive,
              sofic-groups-are-surjunctive,
              sofic-radical-localizes-garden-of-eden-windows

Title: "Fold the tables over the residually finite quotient, read the fold in normal forms, and localize the
Garden of Eden". Why sufficient:
1. **Canonical window** (Lemma 1.1). If `tau sigma(y)(g) != y(g)`, then `y` on `g(MS ∪ {1})` is a Garden of
   Eden, because the value at `g` depends only on `gMS` and `tau sigma` fixes the image of `tau`.
2. **Normal forms** (Lemma 2.1). If `g` and `g delta^4` lie in `B_4`, then `g = (zx)^2`. If `ms = (zx)^2`
   with `m, s in B_2`, then `m = s = zx`.
3. **One fold** (Theorem 2.2(1)-(3)).
   * Over the residually finite quotient the pair is two-sided, so the reverse table becomes sufficient.
   * Folds come from `Gamma_0 ∩ B_8 = {1, delta^(+-4)}`, so the only one is `(zx,zx) ~ (xz,xz)`.
   * It must occur, and rules that ignore `zx` or `xz` cannot see it.
4. **Image** (Theorem 2.2(4)-(5)). Agreement on the two folded cells makes the local assignment constant on
   the folded classes. A pattern not separating the pair extends to a `delta^4`-invariant configuration.
5. **Mark** (Theorem 3.1). Localization puts a nontrivial element of `Omega^-1 Omega ⊆ B_8` in
   `Rad(<M>) ⊆ Gamma_0`, and (R) identifies it.
6. **Table groups** (Propositions 3.3 and 3.4).
   * Over `U_E / Rad(U_E)` the pair is two-sided, so some new fold is a hinge in `Rad(U_E)`.
   * Its image lies in `Gamma_0 ∩ B_8`, so it is the mark hinge.
   * With all letters present, the relators are cells, so `U_(E_rho) = Gamma_R`.

**Points for the verifier.**
* the reading (R) of Remark 3.6;
* the address step of Lemma 2.1(2): moving `alpha_s` through `omega_m` preserves both lengths;
* item 3 of Theorem 2.2 for `nu`;
* the inclusion `pi(Rad(U_E)) ⊆ Rad(pi(U_E))` in Proposition 3.4;
* Proposition 3.3(2): `phi(zx) = phi(z) phi(x)` needs `z in S` and `x in M`, which holds when all letters
  are addresses of both memories.
