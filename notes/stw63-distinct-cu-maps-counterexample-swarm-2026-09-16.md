# stw63-distinct-cu-maps-counterexample: swarm attack, 2026-09-16

Target: the root `stw63-distinct-cu-maps-counterexample`. It asks for a unital `B` and
unital embeddings `phi,psi:Z->B` with `Cu(phi) != Cu(psi)`.
Hole worked: the root itself, locked by `swarm-stw63-distinct-cu-maps-counter`.
Outcome: no counterexample. One elementary obstruction was proved and landed as a node
pair. The existence step of the LXIV-to-LXIII lifting route was re-checked. Several
direct constructions were tested and dismantled.

## 1. Setup

`Cu(Z) = N disjointUnion (0,infinity]`, with compact `e_n = n[1_Z]` and soft `sigma_t`.
The order and mixed sums follow Robert (arXiv:1007.1964v3, Section 6.1 before (6.1);
Proposition 6.1.1; Section 6.3):

- `e_n <= sigma_s` iff `n<s`, and `sigma_t <= e_n` iff `t<=n`.
- `e_n + sigma_t = sigma_(n+t)`.

A unit-preserving Cu-morphism `f:Cu(Z)->S`, with `u = f(e_1)` compact, is the same thing
as a **soft scale** `g(t) = f(sigma_t)` on `(0,infinity]` with these properties:

- (a) `g(t)+g(s) = g(t+s)`;
- (b) `g` preserves suprema of increasing sequences;
- (c) `t<s` implies `g(t) << g(s)`;
- (d) `g(t+1) = u + g(t)`;
- (e) `g(1) <= u`.

**Check of the converse.** Put `f(e_n) = nu` and `f(sigma_t) = g(t)`.

- *Additivity* is (a) together with (d).
- *`e_n <= sigma_s` with `n<s`.* Here `g(s) = g(s-n) + nu >= nu`.
- *`sigma_t <= e_n` with `t<=n`.* Here `g(t) <= g(n) = (n-1)u + g(1) <= nu`.
- *Suprema.* `g(infinity) = sup_k g(k)`, and `ku <= g(k+1) <= (k+1)u`.
- *Compact containment in `Cu(Z)`.* It is: `e_n << y` iff `e_n <= y`; `sigma_t << e_n`
  iff `t<=n`; `sigma_t << sigma_s` iff `t<s`. Each case is preserved because `u << u`,
  and for the last case by (c).

Consequences: `w = g(1)` satisfies `w+w = u+w`, and `q*g(p/q) = (p-1)u + g(1)`.

## 2. What was proven (landed as nodes, check.sh exit 0)

- `research/stw63-distinct-z-cu-maps-need-perforation-witness.md` (claim).
- `research/stw63-perforation-witness-direct-proof.md` (route, `requires: []`).

Let `S` be an arbitrary Cu-semigroup and `f,f':Cu(Z)->S` generalized Cu-morphisms with
`f(e_1) = f'(e_1)`. Three statements hold.

1. **Eventual domination.** `(m+1)f(sigma_t) <= m f'(sigma_s)` for `0<t<s` and
   `m >= (1+t)/(s-t)`. Proof: bridge through the integer `ceiling((m+1)t)`.
2. **Localization.** `f != f'` iff some rational pair `0<t<s<=1` has `f(sigma_t)` not
   below `f'(sigma_s)`, or the same with `f,f'` swapped. The integer-bridge case is
   automatic. The no-integer case translates down by `floor(t)` compact units. Suprema
   then finish.
3. **Obstruction.** If `S` is almost unperforated (or only "`(m+1)x <= my` for all large
   `m` implies `x <= y`"), then `f = f'`.

Hence any witness `B` for the target has `Cu(B)` not almost unperforated. The failure is
witnessed by a pair `x = Cu(phi)(sigma_t)`, `y = Cu(psi)(sigma_s)` (or swapped) with
`t<s` rational in `(0,1]`.

Literature relation (corrected by the referee, see the end of this note).
Antoine--Perera--Thiel (arXiv:1410.0483v3) Theorem 7.3.11 and Proposition 7.1.7(4) give
uniqueness when `S` is almost unperforated and almost divisible. But their
**Proposition 7.3.10** already proves uniqueness of a generalized Cu-morphism
`Z -> S` with prescribed `alpha(1)` for any almost unperforated `S`, with no
divisibility assumption and no ≪-preservation. So the almost-unperforated obstruction is
known. The node only adds parts 1–2 in arbitrary `S`, the weaker "for all large `m`"
hypothesis, and the rational unit-interval form of the witness. No novelty is claimed.

## 3. Further derived observations (not landed; recorded for the next agent)

- **Level periodicity in stable rank one.** Suppose `Cu(B)` has the weak cancellation
  `x+z <= y+z'`, `z' << z` implies `x <= y`. This is the APRT import recorded in
  `stw64-supersoft-calculus` for simple unital sr1 targets. With `z = z' = u` compact,
  `f(sigma_(t+n)) <= f'(sigma_(s+n))` iff `f(sigma_t) <= f'(sigma_s)`. So a witness
  persists at every unit level. For non-simple sr1 algebras I did not re-verify the
  general APRT statement.
- **Gap bound.** In a simple unital sr1 target with nonempty normalized 2-quasitraces,
  `f(sigma_t)^ = t*u^` (artifact `stw64-supersoft-comparison-gap-2026-09-04`, eq. (4)).
  So comparison with gap `R > rc(B)` forces `f(sigma_t) <= f'(sigma_s)` once
  `s-t > rc(B)`. Witnesses therefore need `s-t <= min(1, rc(B))`.
- **Additive defect invariants cannot separate.** Let `delta:S->G` be additive into an
  abelian group or `[0,infinity)`, with `delta(u)` fixed. From
  `g(1)+g(t) = u+g(t)` and `q*g(1/q) = g(1)` one gets `delta(g(p/q))` = `(p/q)delta(u)`
  whenever `G` is torsion-free (cancellative, uniquely divisible hull). The difference
  `delta*g - delta*h` is a homomorphism `Q->G` killing `Z`. It factors through `Q/Z`, so
  it vanishes unless `G` has divisible torsion (Prüfer type). A distinguishing mechanism
  must be non-additive, or `Q/Z`-valued.

## 4. Approaches tried and exactly where each dies

1. **Meet of two scales in sr1.** APRT (arXiv:1809.03984) make `Cu(B)` an
   inf-semilattice with `+` distributing over meets. I recalled this and did not
   re-verify the theorem number this session. Then `k(t) = g(t) ∧ h(t)` satisfies
   `k(t+1) = u + k(t)`. It only gives `k(s)+k(t) <= k(s+t)`, not additivity, so `k` is
   not a scale. Dies at (a).
2. **Determining a scale by `g(1)`.** The identity `q*g(p/q) = (p-1)u + g(1)` does not
   pin `g(p/q)`: q-th roots in `Cu(B)` need not be unique. So "equal `g(1)`" does not
   reduce the problem. Dies at root uniqueness.
3. **Idempotent-ideal perturbation.** Put `h(t) = g(t)+w` with `w+w = w`. This keeps
   (a), (b) and (d). Condition (e) needs `g(1)+w <= u`. Condition (c) needs
   `g(t)+w << g(s)+w`, which cannot be obtained from `w << w` when `w` is noncompact.
   In the examples I tried, either `w` was absorbed (so `h = g`) or (c) or (e) failed.
   No general impossibility is claimed. Dies at (c) and (e) in every tested case.
4. **Canonical supersoft family.** It is not a morphism, and every unital map lies
   strictly below it when `rc>0` (landed earlier as `stw64-z-maps-avoid-supersoft-classes`).
5. **Abstract label-gap semigroups.** I tried soft classes `(t,label)` with a
   translation-invariant gap `c(a,b)>0` between labels. The integer bridge
   `g(t) <= nu <= h(s)` for `t <= n < s` forces the gap to depend on the fractional
   position of `t`. Order compatibility with adding `(r,a)` or `(r,b)` destroys any
   position-dependent gap. Every variant I wrote failed transitivity or compatibility.
   Dies at the order/addition axiom (O3-compatible order).
6. **Villadsen Euler-class twist (heuristic only).** A twisted soft image of normalized
   rank `t` would carry an obstruction degree `w(t)`, roughly the normalized top
   nonvanishing Chern degree. Two constraints bite:
   - The integer bridge `g(t) <= u` needs a complement of rank `(1-t)n` absorbing the
     twist, so `w(t) <= 1-t`.
   - Additivity with `g(1)+g(t) = u+g(t)` forces `w(g(1)) = 0`, so `w(g(p/q)) = 0`
     unless saturated at the dimension cap. The cap is excluded near `t=1` by the bridge.

   So Euler-class perforation, the standard Villadsen mechanism, cannot directly
   separate two Z-images. Separation must come from torsion-type or genuinely
   non-additive data. This is a heuristic: "twist degree" is not a Cuntz invariant.
7. **C(X)-algebras with Z fibres, and twisted dimension-drop maps.** Over
   finite-dimensional `X` these are trivial and Z-stable (repo nodes on locally
   Z-stable and Z-stable-hull codomains give uniqueness). I found no computable Cu
   obstruction for the infinite-dimensional-base examples. Dies for lack of a Cu
   computation.

## 5. Existence step of `stw99-lxiv-pair-lifts-to-lxiii-refuter`

Robert (arXiv:1007.1964v3) was checked by direct text extraction of the PDF.

- **Theorem 1.0.1.** The domain is a 1-dim NCCW complex with trivial `K_1`, a sequential
  limit of such, or stably isomorphic to one. The codomain has stable rank one. A `Cu~`
  morphism `alpha` with `alpha([s_A]) <= [s_B]` lifts to `phi` with `Cu~(phi) = alpha`,
  unique up to approximate unitary equivalence.
- **Theorem 3.2.2(i).** For unital `A`, `Cu~` classifies homomorphisms from `A` iff `Cu`
  does. The proof covers existence. Given `alpha` with `alpha([1]) <= [s_B]`, choose a
  projection `p` with `[p] = alpha([1])`. Then
  `alpha~([a]-n[1]) = alpha([a]) + n[1-p] - n[1]` is a `Cu~` morphism (Robert eq. (3.5)).
- **Section 6.3.** It uses exactly this with domain `Z`.

A unit-preserving pair therefore lifts to *-homomorphisms. In a finite (sr1) target,
`phi(1)` Murray--von Neumann equivalent to `1` forces `phi(1) = 1`, and simplicity of `Z`
makes the lifts embeddings. The route's only open input is the LXIV pair itself.

## 6. Literature gate (dated, 2026-09-16)

- Schafhauser--Tikuisis--White, *99 problems*, arXiv:2506.10902v2: Problems LXIII and
  LXIV are stated as open.
- Gardella--Perera, arXiv:2212.02290v2, Problem 16.3: asks for two distinct
  unit-preserving `Cu(Z)->Cu(A)` for Toms or Villadsen `A`. The context sentence
  (checked) recalls uniqueness in the Z-stable case; unperforated non-Z-stable targets
  are not discussed.
- AGKP, arXiv:2412.06031: LXIII is still described as open.
- Elliott--Li--Niu, arXiv:2209.10649v4: Theorem 3.4 gives `rc = mdim/2`. Theorem 5.1 is
  point-evaluation uniqueness, not about Z. Corollary 7.9 classifies by `rho(K_0)` plus
  `rc`.
- Elliott--Niu II, arXiv:2510.13695v2: classifies AF-/UHF-Villadsen algebras by
  `(Cu,[1])` via comparison-radius functions, but computes neither Cu nor
  `Cu(Z)`-maps.
- Antoine--Perera--Thiel, arXiv:1410.0483v3: Definition 5.2.16, Theorem 5.2.18,
  Paragraph 3.2.5, Proposition 7.1.7 and Theorem 7.3.11 were checked by text extraction.
  Proposition 7.1.14 (uniqueness of unital maps `R->S` into Cu-*semirings* `S`) is
  adjacent but concerns semirings.
- Abstracts checked, none claiming a resolution:
  - Vaccaro 2604.24682
  - Fu 2605.21655
  - Toms 2609.09535
  - Ara--Perera--Quingles 2609.15670
  - Hirshberg--Phillips 2312.11203
  - Asadi-Vasfi 2505.05764
- arXiv API search `all:unperforated AND all:Jiang` (2026-09-16) returned no paper
  treating uniqueness of unital `Cu(Z)`-maps under almost unperforation alone.
  (Referee correction: this uniqueness is APT arXiv:1410.0483v3 Proposition 7.3.10,
  which the keyword search did not surface.)

This is not an exhaustive certification of the literature.

## 7. What remains open

- Existence of two distinct unit-preserving Cu-morphisms into any perforated target,
  in particular Villadsen or Toms algebras (LXIV, locked by another agent this session).
- By the landed node, such a pair must produce a perforation witness at rational ranks
  in `(0,1]`. By Section 3, it cannot be seen by additive torsion-free defect invariants.
- A concrete next test: look for `Q/Z`-type (Prüfer) twisting in soft classes, for
  instance via the unitary Cuntz semigroup `Cu_1`. Abstract "label-gap" models do not
  work.

## Referee (2026-09-16)

**Checked.**

- Read both nodes and this note in full, plus the root
  `stw63-distinct-cu-maps-counterexample`, `stw63-strict-comparison-sr1-uniqueness`,
  its proof route, `stw64-z-maps-avoid-supersoft-classes` and
  `stw99-lxiv-pair-lifts-to-lxiii-refuter`. `git status` shows no unlisted stw63 files
  from this solver.
- Re-derived every step of `stw63-perforation-witness-direct-proof` by hand:
  - Step 0: the supremum of `sigma_(r_k)`, including the case of a compact upper bound.
  - Step 1: the integer bridge needs `t <= n < s`, which forces `n >= 1`.
  - Step 2: `m(s-t) >= 1+t` gives `ms-(m+1)t >= 1`, so `ceiling((m+1)t)` lies in
    `[(m+1)t, ms)`. Checked exactly over 193000 rational triples with `q <= 24`; no
    failures.
  - Step 3: the case split on whether an integer lies in `[t,s)`, the translation by
    `floor(t)` compact units, and the supremum step. Both directions of the iff hold.
  - Step 4: the obstruction follows from part 1.

  I found no gap and no hidden hypothesis. The proof uses only additivity, order,
  `0 -> 0`, sequential suprema and `f(e_1)=f'(e_1)`. It needs no separability,
  simplicity, stable rank or ≪-preservation.
- The order structure of `Cu(Z)` was checked against the arXiv TeX sources:
  - Robert, arXiv:1007.1964v3. Section 6.1 gives the mixed order `[p]-[q] <= alpha` iff
    `hat < alpha`, and `alpha <= [p]-[q]` iff `alpha <= hat`. The proof of
    Proposition 6.1.1 gives `V(A) disjointUnion LAff_+`, where `Aff_+` requires
    `f(tau) > 0` for `tau != 0`. Section 6.3 gives `Cu(Z) = N disjointUnion [0,infinity]`.
    All three are confirmed.
  - APT arXiv:1410.0483v3, Paragraph 7.3.2, states `Z = N disjointUnion (0,infinity]`
    with `n <= a` iff `n' < a` and `a <= n` iff `a <= n'`. This confirms the solver's
    reading of the soft part and the strict mixed order, so the "weakest step" worry is
    resolved.
  - Theorem 7.3.11 and Proposition 7.1.7(4) are correctly numbered and quoted. I
    recomputed the numbering from the shared counter in the TeX source.

**Problem found and fixed (overclaimed relation to the literature).** The solver wrote
that its argument "drops almost divisibility" compared with APT. That is wrong. APT
arXiv:1410.0483v3 **Proposition 7.3.10** (label `prp:zembed`) already states the
following. For an almost unperforated Cu-semigroup `S`, a generalized Cu-morphism
`alpha_a: Z -> S` with `alpha_a(1) = a` exists iff `a` is almost divisible, and *if it
exists it is unique*. So the almost-unperforated case of part 3, and the C-star
consequence that a witness has `Cu(B)` not almost unperforated, are already known.

I rewrote the "Relation to the literature" section of the route to credit APT 7.3.10
and Lemma 7.3.9. The route now lists what remains as additions:

- parts 1–2 in an arbitrary `S`;
- the weaker "for all large `m`" hypothesis;
- the rational unit-interval form of the witness.

I added the attribution to the claim body and corrected §2 and §6 of this note. I also
added APT Paragraph 7.3.2 to the route as an independent source for (Z1)–(Z3).

**Duplicates.** `bin/cairn search --similar` finds no landed duplicate. The in-flight,
unlanded node `stw64-unital-z-maps-rc-shift-close`, from another agent, overlaps in
spirit: its "rc(A)=0 implies f=h" is a functional-comparison analogue. It is not a
duplicate, because this node is purely order-theoretic in arbitrary `S` and uses no
functionals. Whichever lands second may want a `distinct_from` entry.

**Not verified.** Sections 3–5 of this note are heuristics or recalled imports (APRT
arXiv:1809.03984 theorem numbers). They stay in notes and were not promoted.

**Verdict.** The direct proof is sound and complete. The status of the claim is honest
after the attribution fix. The root stays OPEN. Landed with fixes.
