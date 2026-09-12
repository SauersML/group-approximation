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
