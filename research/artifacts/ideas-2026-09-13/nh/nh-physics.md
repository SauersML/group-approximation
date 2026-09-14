# Idea lane nh-physics: mathematical physics as a source for a non-hyperlinear group

Lane `nh-physics`, 2026-09-13. Target: `non-hyperlinear-group`. This is an ideas file. It claims no
theorem, and no Cairn node is edited. Every citation below is marked either checked (and at what level)
or unchecked.

## Standing kill patterns used here

- **(K1) Global tracial positivity.** An inequality that holds in every tracial von Neumann algebra
  cannot separate the group trace from matrix models (`global-tracial-positivity-cannot-separate-group-trace`,
  on main).
- **(K2) Marked limits.** Limits in the space of marked groups add nothing
  (`local-approximation-properties-are-marked-closed`, on main).
- **(K3) Normalization.** In normalized Hilbert–Schmidt distance, integrality invariants of index, Bott or
  determinant type disappear.

**What survives normalization.** A physics mechanism has to count at finite dimension. In matrices the count
must stay bounded below after dividing by the dimension, and it must fail in some tracial von Neumann
algebra. Otherwise (K1) kills it.

## A. Spin-lattice physics: undecidable spectral gap and the quasi-local algebra

**Idea.** Cubitt–Pérez-García–Wolf build translation-invariant nearest-neighbour Hamiltonians on Z^2 with
constant local dimension, for which "gapped or gapless" is undecidable (arXiv:1502.04573; abstract checked
through the arXiv listing). Use such a family as the source of an object whose infinite-volume behaviour
has no finite-volume approximation, then pass to a group.

**What it would prove.** A computability separation between matrix approximations and the infinite-volume
object, forcing a non-hyperlinear group.

**Kill test.**
1. Is the undecidable quantity visible in normalized HS?
2. Where does the infinite-volume object live?

**Result.**
- The spectral gap is an absolute spectral-edge quantity and has no normalized-trace meaning. The normalized
  quantity, energy density, is bounded above by finite periodic volumes and from below by Anderson-type bounds
  and semidefinite hierarchies that converge for translation-invariant systems. Checked at abstract/summary
  level: arXiv:2301.06142 and arXiv:2605.06784. So it gives no computability separation.
- More basically, the quasi-local algebra of any lattice with finite local dimension is UHF. UHF ⋊ Z^d with
  an invariant trace generates an injective von Neumann algebra, since it is an amenable crossed product of a
  hyperfinite algebra. So every tracial object built this way embeds in R^ω. This is standard (Connes); I only
  re-derived it here.

**Verdict: killed as a source.** It leaves one constraint, (C1): any physics witness must bring either a
non-amenable symmetry, or operator relations that aren't tensor-local (the Tsirelson setting). Finite local
dimension together with amenable translations is always embeddable.

## B. Anomalies and indices: trace of commutators, spectral flow, QCA index, edge anomalies

**Idea.** Anomalies are the physics of "exists at infinite volume, impossible at finite dimension":
- Wintner–Wielandt [P,Q] = i·1;
- Schwinger terms and spectral flow;
- the GNVW index of one-dimensional quantum cellular automata (arXiv:0910.3675; abstract checked);
- symmetry that can't act on-site at an edge, classified by H^{d+1}(G,U(1)) (Else–Nayak, arXiv:1409.5436;
  abstract checked).

Encode an anomalous relation into a finitely presented group, so that matrix models are forced to violate it
by a normalized amount.

**What it would prove.** A normalized defect floor for every matrix model of a group whose regular
representation satisfies the relation exactly.

**Kill test.** Sort each invariant by kill pattern, and try to realize nontrivial-index QCA exactly on finite
rings.

**Result.**
- **Trace of a commutator.** tr[A,B] = 0 holds in every tracial von Neumann algebra, so (K1) kills it.
- **Determinant and Bott integrality.** Killed by (K3), since almost-commuting unitaries in normalized HS are
  close to commuting ones (the kill pattern on main).
- **GNVW and Else–Nayak.** These obstruct locality-preserving or on-site realizations, not finite-dimensional
  realizations. By hand, a two-species chain with qubits moving left and qutrits moving right (index 2/3) is
  realized exactly on every finite ring by sublattice translations. So the index never forces a normalized
  defect.

**Verdict: killed.** Physics anomalies are either tracial, so (K1) applies, or constraints on locality
rather than dimension.

## C. Anyons, Temperley–Lieb towers and Jones' Thompson-group representations

**Idea.** Fusion categories with irrational quantum dimensions (Fibonacci, A_k), and Jones' unitary
representations of Thompson's groups F and T built from subfactor planar algebras. Checked through arXiv
listings: arXiv:1901.10597 (representations of F from Temperley–Lieb–Jones algebras) and arXiv:1710.06972
(Jones subgroup of T). These produce positive-definite functions and traces that live only at infinite
volume.

**What it would prove.** A trace on a Thompson-type group that no matrix model reproduces.

**Kill test.** Is the resulting tracial object AF-embeddable? And is it the regular trace?

**Result.**
- Temperley–Lieb and Jones towers with the Markov trace are AF, hence embeddable in R^ω. This is standard;
  I didn't re-read a source.
- Jones' vacuum-vector functions are coefficients or characters, not the regular trace. On main,
  `non-ce-trace-on-sofic-racg` exhibits a non-embeddable trace on a sofic group, so a bad character proves
  nothing about hyperlinearity.

**Verdict: killed.**

## D. Lattice gauge theory with an infinite discrete gauge group

**Idea.** In a Kogut–Susskind lattice gauge theory with gauge group G, the strong-coupling electric vacuum
|δ_e⟩ on each link gives Wilson-loop expectations equal to the regular trace τ_G of the holonomy. So the
regular trace appears as a physical state. The Gauss-law constraint and flatness might then make finite
truncations fail.

**What it would prove.** Non-hyperlinearity of a gauge-theory group built from G.

**Kill test.** Compute what finite-dimensional approximations of the gauge algebra reduce to.

**Result.** By hand: the link and site groups are restricted products of copies of G, and the gauge action
is a direct limit of finite products. HS approximations of the whole system therefore reduce to HS
approximations of G, and hyperlinearity passes to direct products, subgroups and directed unions (standard
permanence). The theory is exactly as hyperlinear as G.

**Verdict: killed as tautological.**

## E. Hyperbolic holographic quantum tilings over a Fuchsian base (best survivor)

**Idea.**
- **Setup.** Put a translation-invariant quantum constraint rule on a hyperbolic tessellation {p,q} instead of
  Z^2: the geometry of the HaPPY holographic codes (arXiv:1503.06237; abstract checked). Let Δ be the
  cocompact triangle or surface group acting on the tiling. Let Sol be the solution group of a Δ-invariant
  binary constraint rule with a central sign J, and set Γ = Sol ⋊ Δ.
- **Why hyperbolic.**
  - (i) Non-amenable geometry, meaning region boundaries are proportional to volume, removes the Følner
    patching that makes classical tiling obstructions vanish in normalized density on Z^d.
  - (ii) Surface groups are flexibly stable in permutations (Lazarovich–Levit–Minsky, arXiv:1901.07182;
    abstract and JEMS 27 (2025) listing checked). So the base action of a model might be rounded to a genuine
    compact hyperbolic surface cover.
- **Rounding.** Gowers–Hatami-type rounding of each finite gadget would then turn an approximate model into an
  exact finite-dimensional quantum tiling on a compact surface.
- **Target rule.** J ≠ 1 in Γ (a commuting-operator infinite-volume solution), but no finite-dimensional
  solution with J = −1 on any compact quotient surface.

**What it would prove.** Γ is finitely presented and not hyperlinear, provided a unitary substitute for (ii)
exists.

**Kill tests run.**
1. **Amenable reduction.** It doesn't apply: Δ is non-amenable, so a hyperlinear Sol settles nothing. That is
   consistent with the plan.
2. **Stabilizer rules.** For stabilizer rules such as HaPPY's five-qubit perfect tensors, the code cut to any
   compact surface is a genuine finite stabilizer code with finite Pauli realizations at every scale. So
   stabilizer rules are **killed** as witnesses, and the rule has to use contextual, non-Clifford gadgets
   (Slofstra-type embeddings; not re-read).
3. **HS stability of the base.** Flexible stability here is for permutation models. A search turned up no
   flexible Hilbert–Schmidt stability result for surface groups, only Akhtiamov–Dogon on uniform HS stability
   (arXiv:2010.10304) and the amenable HS-stable characterization (arXiv:2207.01089), both at abstract level.
   So this input is open, and it is the main gap.
4. **Overlap with main.**
   - The 09-13 Z^2 program (`zd-derived-full-group-fp-excludes-periodic-quantum-tilings`, periodic quantum
     tilings, wall rigidity) is about Z^2 shifts of finite type and derived full groups, not a Fuchsian base
     for non-hyperlinearity.
   - `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` needs a Kazhdan base, and Δ is not Kazhdan. So
     neither covers this, and this route needs its own rounding.

**Verdict: unclear, survives.**

**Missing inputs.**
- (a) A unitary, flexible HS-stability theorem for Fuchsian bases inside Γ-models, or a monomial-rounding
  substitute.
- (b) A Δ-invariant contextual rule with J ≠ 1 in Γ and no compact-surface solution with J = −1.

**First concrete test.** Take a Magic-Square / Mermin–Peres-type contextual gadget on each face of {5,4}.
Decide whether the Z/2 obstruction class of the rule on a genus-g quotient complex is forced to be nonzero for
every g, while the infinite tiling carries an operator solution.

## Summary

| # | Approach | Verdict |
|---|---|---|
| A | Undecidable spectral gap / quasi-local lattice physics | killed; constraint C1 (UHF wall) |
| B | Anomalies, spectral flow, QCA index, edge anomalies | killed (K1, K3, locality not dimension) |
| C | Anyons, TL towers, Jones' Thompson representations | killed (AF; characters are not the regular trace) |
| D | Lattice gauge theory with infinite gauge group | killed (tautological) |
| E | Hyperbolic holographic quantum tilings over a Fuchsian base | unclear, best survivor; needs flexible HS stability for Fuchsian bases plus a contextual rule |
