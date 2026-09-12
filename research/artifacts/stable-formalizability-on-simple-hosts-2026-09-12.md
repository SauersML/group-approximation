# Formalizability on finitely generated simple hosts: what transfers and what does not

Lane `w3-stable-simple`, 2026-09-12. Family F (formalizability), verifier `w3-vf-nonlinear`.

The Kaplansky payoff of family F needs formalizations only on the hosts that Gottschalk reduces to:
finitely generated infinite simple groups (`gottschalk-reduces-to-fg-simple-kazhdan-groups`). This
artifact records which formalizability obstructions reach those hosts. Everything is on paper.

## 0. Setup

- `G` is a group, `k = F_q`, and an automaton `tau` on `(k^n)^G` has finite memory `M` and local rule
  `mu`, so `tau(x)(g) = mu((x(gm))_(m in M))`.
- A *representative* `tau~` is a polynomial over `k` in variables `X_(m,i)`, `m in M~`, `i in [n]`,
  on a finite memory `M~ ⊇ M`, whose value at every point of `k^(M~ x [n])` is `mu` of the restriction.
- The translate at a cell `g` is `tau~_g = tau~(X_(gm,i))`.
- `(tau~, sigma~)` is a *formal pair* when the decoder representative `sigma~`, with memory `N`,
  satisfies `sigma~((tau~_v)_(v in N)) = X_(1,i)` in `k[X_(G x [n])]` for every track `i`.
  Translation gives the same identity at every cell.
- A stable formalization is a formal pair for `tau x id_m`; everything below applies to it verbatim,
  with the ancilla tracks carried along as extra tracks.

## 1. Formal pairs push forward along quotients of the encoder memory group

**Theorem 1.** Let `(tau~, sigma~)` be a formal pair for `tau` on `(k^n)^G`. Suppose the encoder
representative's memory `M~` lies in a subgroup `H <= G`, and `rho : H -> Q` is a surjective
homomorphism. Put `tau_rho(y)(q) = mu((y(q rho(m)))_(m in M))` on `(k^n)^Q`. Then `tau_rho` has a
formal left inverse on `(k^n)^Q`, with the representative `tau~_rho` obtained from `tau~` by the
substitution `X_(m,i) -> X_(rho(m),i)`.

*Proof.*
1. **Collapse to `H`.** Choose representatives `c` of the left cosets `cH`, with representative `1`
   for `H`. The substitution `psi : X_(ch,i) -> X_(h,i)` (`h in H`) is a ring homomorphism
   `k[X_(G x [n])] -> k[X_(H x [n])]` with `psi(X_(1,i)) = X_(1,i)`.
   - For `v in N` write `v = c_v h_v`. Every `v m` with `m in M~ ⊂ H` lies in `c_v H`, so
     `psi(tau~_v) = tau~(X_(h_v m,i)) = tau~^H_(h_v)`, the `H`-translate at `h_v`.
   - Applying `psi` to the formal identity gives `sigma~((tau~^H_(h_v))_(v in N)) = X_(1,i)` in
     `k[X_(H x [n])]`.
   - Define the `H`-decoder at cell `1` by feeding slot `v` of `sigma~` from cell `h_v`. It is a
     polynomial rule on the memory `{h_v}`, and its composite with `tau_H` is `X_(1,i)` formally.
     Translating over `H` gives a formal pair on `(k^n)^H`.
2. **Push along `rho`.** The substitution `phi : X_(h,i) -> X_(rho(h),i)` is a ring homomorphism
   `k[X_(H x [n])] -> k[X_(Q x [n])]` fixing `X_(1,i)`. It sends `tau~^H_h` to the `Q`-translate at
   `rho(h)` of `tau~_rho`, and the `H`-identity to a `Q`-identity at cell `1`. So `tau~_rho` has a
   formal left inverse on `Q`.
3. **What `tau~_rho` represents.** At a point `y` of `k^(Q x [n])`, `tau~_rho(y) = tau~(y o rho)`,
   and `tau~` agrees with `mu` at points. So `tau~_rho` represents `tau_rho`, which depends only on
   the functional rule `mu`, on `H` and on `rho`. ∎

**Remarks.**
- With `H = G` and `rho` the quotient by a normal subgroup `K`, this is the substitution of
  `formalizable-pairs-restrict-to-finite-quotients`. That substitution works for every normal `K`, not
  only finite-index ones.
- The decoder memory `N` is unrestricted. Only the encoder representative's memory matters.
- **Formalizability passes up.** A formal pair on `H` is a formal pair for the induced automaton on
  every `G ⊇ H`, with the same polynomials. So refutations pass only down, to subgroups, and only
  through Theorem 1.

**Corollary 2 (bi-orderable quotient obstruction).** Let `tau` be a one-track automaton that is not a
translation composed with an affine map. Suppose `(tau~, sigma~)` is a formal pair whose encoder
memory generates `H`. Then `tau_rho` is affine for every surjection `rho` from `H` onto a bi-orderable
group.

*Proof.* Theorem 1 gives a formal pair for `tau_rho` on `Q`, one track. By
`formalizable-binary-pairs-over-biorderable-groups-are-affine`, in its every-finite-field form,
`tau_rho(y)(q) = a y(q m_0) + b`. ∎

**Corollary 3 (induced marker involution).** Let `g in G` have infinite order and let `tau_g` flip
cell `h` exactly when `(x(hg^(-3)), x(hg^(-2)), x(hg^(-1)), x(hg), x(hg^2), x(hg^3)) = (0,0,1,1,0,0)`.
Every formalizing encoder representative of `tau_g` has memory generating a subgroup `H` such that
`rho(g) = 1` for every homomorphism `rho` from `H` to a bi-orderable group. In particular `g` has
finite order in `H^ab`. So the encoder memory must leave `<g>`, and every subgroup such as
`<g> x F` that retracts onto `<g>`.

*Proof.*
- If `rho(g) = t ≠ 1`, then `t` has infinite order, since bi-orderable groups are torsion-free. So
  `tau_rho` is the marker involution along `<t>` on `Q`. It fixes the zero configuration, and it
  changes cell `q` of the configuration with ones exactly at `q t^(±1)`. It fixes the configuration
  with a single one at `q t`. No map `y -> a y(q m_0) + b` does all three, so `tau_rho` is not affine,
  contradicting Corollary 2.
- If `rho(g) = 1`, all six memory cells merge, the marker condition asks one value to be both `0` and
  `1`, and `tau_rho` is the identity. That is consistent. ∎

## 2. Affine rigidity never reaches a finitely generated simple host

**Theorem 4.** No nontrivial finitely generated simple group is bi-orderable.

*Proof.*
- An abelian simple group is `Z/p`, which has torsion, so it is not bi-orderable.
- Let `G ≠ 1` be finitely generated and bi-ordered. It suffices to find a nontrivial homomorphism
  `G -> (R, +)`; then `G` is not perfect, hence not nonabelian simple.
  1. **Convex subgroups form a chain.** This holds in every ordered group.
  2. **A maximal one exists.** Let `C` be the union of all proper convex subgroups. `C` is a convex
     subgroup. It is proper: otherwise the finitely many generators lie in one proper convex subgroup,
     which is then all of `G`.
  3. **`C` is normal.** Conjugation preserves a bi-order, so `gCg^(-1)` is a proper convex subgroup,
     hence `gCg^(-1) ⊆ C`.
  4. **`G/C` is Archimedean.** The order on `G/C` given by `aC < bC` iff `a < b` and `aC ≠ bC` is a
     well-defined bi-order, by convexity and normality. For `a > 1` in `G/C`, the set of `x` with
     `a^(-n) <= x <= a^n` for some `n` is a convex subgroup: products stay bounded because the order is
     invariant on both sides. Its preimage is a convex subgroup of `G` strictly containing `C`, so it is
     `G`. That is the Archimedean property.
  5. **Hölder.** An Archimedean bi-ordered group embeds in `(R, +)` (Hölder, 1901, imported at
     statement level). `G/C ≠ 1` gives the homomorphism. ∎

**Consequences for the payoff hosts.**
- `formalizable-binary-pairs-over-biorderable-groups-are-affine` never applies to a finitely generated
  simple host, even at one track.
- **Corollary 2 is void when the encoder memory generates the whole simple host.** Its only bi-orderable
  quotient is trivial. So a formalization over a simple `G` may read everywhere, and no pushforward
  obstruction remains.
- **Every landed refutation of plain formalizability misses those hosts:**
  - the marker involution over `Z` and over `Q`: bi-orderable groups;
  - finite quotients: a host without proper finite-index subgroups has only the constant level, and over
    `F_2` every permutation of `F_2^n` is induced by a tame map (`AGL(1,2) = Sym(2)`, and
    `tame-maps-induce-every-permutation-of-prime-field-cubes` for `n >= 2`);
  - normal subgroups: a simple host has no nontrivial proper quotient.
- **Torsion.** The canonical hosts `L_(F_2)(1,2)^x` and Thompson's `V` contain torsion. So `F_2[G]` has
  zero divisors, and step 1 of the affine rigidity proof (domain, hence direct finiteness, hence
  algebraic independence of the encoder translates) is not available either.

## 3. Zero divisors give one-track formal automorphisms

For `u in M_(r x n)(k[G])`, write `L_u : (k^n)^G -> (k^r)^G`, `L_u(x)(h) = sum_m u_m x(hm)`. As
polynomial maps these compose exactly: `L_u L_v = L_(uv)`.

**Theorem 5 (zero-divisor shears).** Let `A in M_(n x r)(k[G])` and `B in M_(r x n)(k[G])` satisfy
`BA = 0`, and let `Gamma` be any automaton `(k^r)^G -> (k^r)^G` with any representative `Gamma~`. Then
`T(x) = x + L_A(Gamma(L_B x))` and `T'(x) = x − L_A(Gamma(L_B x))` form a two-sided formal pair.

*Proof.* Formally, `L_B(x ± L_A w) = L_B x ± L_(BA) w = L_B x`. So
`T'(T(x)) = x + L_A Gamma~(L_B x) − L_A Gamma~(L_B x) = x`, and symmetrically. ∎

**Remarks.**
- **Track shears are a special case.** `track shear x_i += f(x_j, j != i)` is `A = e_i`, `B` the
  projection off track `i`, with `BA = 0` by matrix units. So Theorem 5 extends
  `structurally-reversible-automata-are-formalizable` from matrix-unit zero divisors to zero divisors
  of the group algebra itself.
- **Odd characteristic.** If `s` has order `p = char k`, then `N = 1 − s` has `N^p = 0`, so
  `A = N^(p−1)`, `B = N` qualify.
- **Always bijective.** Words in these gates and units of `M_n(k[G])` are bijections. A strict automaton
  is never such a word.

**Corollary 6 (non-affine one-track formal involutions).** Let `s in G` have order two and let `m in G`
with `m^(-1) s m ≠ s`. On `{0,1}^G` put `S(h) = x(h) + x(hs)` and
`tau(x)(h) = x(h) + S(h)·(S(hm) + S(hsm))`. Then `tau` is a formal involution that is not affine.

*Proof.*
1. **It is a zero-divisor shear.** Take `N = 1 + s`, so `N^2 = 0`, and `Gamma(z)(h) = z(h) z(hm)`.
   Then `L_N(x) = S`, `Gamma(S)(h) = S(h) S(hm)`, and `L_N(Gamma(S))(h) = S(h)S(hm) + S(hs)S(hsm)`,
   which equals `S(h)(S(hm) + S(hsm))` because `S(hs) = S(h)`. So `tau = T` with `A = B = N`, and
   Theorem 5 applies; in characteristic two `T' = T`.
2. **The cells are distinct.** `S(hm) + S(hsm) = x(hm) + x(hms) + x(hsm) + x(hsms)`. The hypothesis
   `m^(-1) s m ≠ s` makes `hm, hms, hsm, hsms` pairwise distinct, and distinct from `h` and `hs`.
3. **Not affine.** The rule is a multilinear polynomial of degree two in distinct cell variables. Over
   `F_2` the multilinear representative of a function is unique, so `tau` is not affine. ∎

**Worked case: the infinite dihedral group.** Take `D_inf = <g, s | s^2, sgs = g^(-1)>` and `m = g`.
Write `a(k) = x(g^k)`, `b(k) = x(g^k s)` and `S = a + b`. Then
`tau(a, b) = (a + c, b + c)` with `c(k) = S(k)(S(k−1) + S(k+1))`.

**Where these gates live.**
- **Every finitely generated simple host with 2-torsion** has trivial centre, so every involution is
  non-central. This covers Thompson's `V` and `L_(F_2)(1,2)^x`, whose swap `w = s0 t1 + s1 t0` is an
  involution. By induction to overgroups, non-affine one-track formal involutions exist on those hosts.
- **Consistency with Corollary 2.** If `s` is central, `S(hm) + S(hsm) = 0` and `tau = id`. On a host
  such as `Z x Z/2`, which retracts onto `Z`, the pushforward of any zero-divisor shear to `Z` is affine,
  as Corollary 2 requires.
- **One-track affine rigidity is a torsion-free phenomenon.** It holds over bi-orderable groups and
  fails on every group with a non-central involution.

## 4. The restricted formalizability target and its payoff

**Open claim** `binary-left-inverse-pairs-over-fg-simple-groups-are-formalizable`: every binary
left-inverse pair `(tau, sigma)` over a finitely generated simple group admits representatives with
`sigma~ o tau~ = id` formally.

- **Payoff.** By `formal-polynomial-strict-pairs-need-unstable-linearization`, it gives
  `stably-finite-simple-hosts-are-binary-power-surjunctive`: a finitely generated simple `S` with
  `F_2[S]` stably finite is surjunctive over every alphabet of size `2^n`.
  - **Every group.** Together with stable finiteness of `F_2[S]` for every such `S`, and
    `gottschalk-reduces-to-fg-simple-kazhdan-groups`, this gives Gottschalk over binary-power alphabets.
  - **Per host.** For instance, stable finiteness of `F_2[L_(F_2)(1,2)^x]` would make that unit group
    surjunctive over binary-power alphabets.
- **Not refuted by any landed result:**
  - the marker refutations live on bi-orderable groups (Theorem 4);
  - finite quotients reach only constants, where every permutation is tame over `F_2`;
  - Corollary 2 is void for encoder memory generating the host;
  - one-track rigidity fails on these hosts (Corollary 6).
- **What a proof for strict pairs must supply.** A strict pair needs a formal pair whose encoder pullback
  `tau~*` on `k[X_(G x [n])]` is surjective but not injective. No word in formal automorphisms has this
  property, so gate constructions, including zero-divisor shears, cannot produce one.

## 5. Test objects on Thompson's `V`

**A dihedral pair inside `V`.** Let `a in F <= V` have infinite order, acting on Cantor space
`{0,1}^N` by prefix replacement. Put
- `g(0w) = 0 a(w)` and `g(1w) = 1 a^(-1)(w)`;
- `s(0w) = 1w` and `s(1w) = 0w`.

Both lie in `V`, `s^2 = 1`, and `sgs = g^(-1)`: on `0w`, `sgs(0w) = s(1 a^(-1)(w)) = 0 a^(-1)(w)`, and
symmetrically on `1w`. Also `s` is not in `<g>`, because `g` preserves the two halves and `s` swaps them.
So `D = <g, s>` is infinite dihedral. Since `V <= L_(F_2)(1,2)^x` (the Leavitt tower), everything below
induces up to the binary Leavitt unit group.

**The object.** `tau_g` flips cell `h` exactly when
`(x(hg^(-3)), x(hg^(-2)), x(hg^(-1)), x(hg), x(hg^2), x(hg^3)) = (0, 0, 1, 1, 0, 0)`. It acts on every
left coset `h<g>` as the integer marker involution, so it is a bijective involution and its own unique
left inverse.
- **Open:** `thompson-v-marker-involution-is-formalizable`, and the smaller
  `dihedral-marker-involution-is-formalizable`.
- **Passing up.** A formalization over `D` induces one over `V`, with the same polynomials.
- **Specialization.** The restricted target `binary-left-inverse-pairs-over-fg-simple-groups-are-formalizable`
  specializes to the `V` object, so a refutation of the `V` object refutes it.

**What is known about the object.**
1. **Where the encoder memory must go.** By Corollary 3, every bi-orderable quotient of the encoder memory
   group kills `g`. So the memory leaves `<g>` and every subgroup that maps onto `Z` nontrivially on `g`.
   `D` evades this: a bi-orderable image of `D` is torsion-free, so it kills `s`, and then
   `g = s g^(-1) s` maps to its own inverse, hence to `1`.
2. **Over `D` it is two tracks over `Z`.** Write `a(k) = x(g^k)` and `b(k) = x(g^k s)`.
   - A rule at cell `1` reads `g^j` and `g^j s`. At `a`-cells it reads `a(k+j)` and `b(k+j)`. At `b`-cells
     it reads `b(k−j)` and `a(k−j)`.
   - So one-track `D`-automata are exactly two-track `Z`-automata whose `b`-rule is the `a`-rule reflected
     with the tracks swapped, and the formal identity on `b`-cells follows from `a`-cells by the symmetry
     `s`.
   - The marker is palindromic, so `tau_g = tau_Z x tau_Z`. Formalizing the `D` object means formalizing
     `tau_Z x tau_Z` over `Z` with reflection symmetry.
   - Theorem A needs one track, and here a top variable can cancel between the two components.
3. **Zero-divisor gates on `D`.** For each reflection `r_i = g^i s`, `N_i = 1 + r_i` pairs `a(k)` with
   `b(k+i)`.
   - The shears of Theorem 5 built on `N_i` add one bit to both members of each pair, while reading only
     linear functionals of the pair sums `a(k') + b(k'+i)`. So they preserve those pair sums.
   - `tau_Z x tau_Z` changes the pair sums at marked cells, so no single gate realizes it. Whether words
     in gates for several `i`, together with units of `F_2[D]`, realize it is open.
4. **Two-sidedness.** `M_2(F_2[Z])` is directly finite, by determinants. So any formalization of the `D`
   object is two-sided, and the translates of the encoder components are algebraically independent.
5. **Regrouping.** `<g^4>` is normal of finite index in `D`, and the regrouped object is two copies of
   the regrouped integer marker. So the `D` object is formalizable after regrouping. What is open is full
   `D`-equivariance.
6. **Finite quotients of `D`.** Refutations through the dihedral quotients `D_n` would refute the `D`
   object but not pass up to `V`, since `V` has no nontrivial finite quotient.
