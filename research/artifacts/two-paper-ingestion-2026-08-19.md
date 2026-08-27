# Ingestion audit: Dogon--Vigdorovich v2 and Chornomaz--Wagner

Date: 2026-08-19

Two source files handed over: `arXiv:2506.20843v2` (Dogon--Vigdorovich,
*Hyperlinearity, stability and asymptotic spectral gap of higher rank
lattices*, `Sigma_submission.tex`) and `arXiv:2304.07603v1` (Chornomaz--Wagner,
*Quasilinear emulation of Turing machines by S-machines*, `S_machine_arXiv.tex`).
Both read at source; statements below are transcribed from those files, not
from abstracts or secondary reports.

## 1. Dogon--Vigdorovich: what the graph already had

The paper is already heavily ingested. Before authoring, the sweep found:

- `el-r-polynomial-robust-spectral-gap` cites DV Def 7.5 / Prop 7.6 / Cor 7.7
  and Lem 8.2 for property `(T;FD)_rob`;
- `steinberg-hyperfinite-hs-stable` uses DV's hyperfinite Hilbert--Schmidt
  stability;
- `hs-normalization-via-robust-spectral-gap` cites DV Lem 3.1 / Prop 3.3
  (intertwiner transport);
- a nine-node `iwahori-*` lane attacks the repair problem in DV's Iwahori
  sector, ending at `iwahori-sector-closure -> non-hyperlinear-group`.

## 2. What was missing, and it is the load-bearing half

**None of DV's numbered main results were nodes.** The Iwahori lane attacks the
technique; the theorem that converts a success there into a non-hyperlinear
group existed only as prose inside `iwahori-sector-closure`. Added:

- **Theorem 1.1** (`hs-stability-forces-nonhyperlinear-central-extension`):
  `Gamma` with property (T;FD), a central extension `1 -> Z -> Gamma~ -> Gamma -> 1`
  with `Gamma~` of finite abelianization, and `Gamma` Hilbert--Schmidt stable,
  force some finite central extension `Gamma~/(N Z)` to be **not hyperlinear**.
- **Theorem 1.5** (`dv-s-arithmetic-hs-stable-nonhyperlinear-extension`), the
  S-arithmetic instance, which is what applies to `SL_2(Z[1/p])`.
- **Question 1.2** (`iwahori-local-global-defect-question`), stated in DV's own
  local-defect/global-defect form. This is the actual object the repo's
  `iwahori-*` lane has been attacking, and it now exists as a node with the
  lane feeding it.
- **Theorem 1.4** (`character-rigidity-equals-hyperfinite-hs-stability`), the
  four-way equivalence for higher rank lattices with (T;FD).
- The candidate's rigidity profile (`sl2-half-central-extension-not-residually-amenable`):
  Deligne and Raghunathan make `Gamma~` non-residually-finite, and Margulis'
  normal subgroup theorem upgrades that to non-residually-amenable.

**Two transcription cautions**, both about what is *live* in the v2 source:

1. The statements "Question 1.2 is equivalent to Hilbert--Schmidt stability of
   `SL_2(Z[1/p])`" and "`SL_2(Z)` is Hilbert--Schmidt stable [MR4661092]" are in
   **commented-out** blocks of `Sigma_submission.tex` (lines around 349). They
   are not printed. Only the implication direction is live: "a positive answer
   to Question 1.2 implies the existence of a non-hyperlinear group. In fact:
   [Corollary 1.3]". The nodes cite Corollary 1.3, never the equivalence.
2. Theorem 1.4 makes character rigidity equivalent to *hyperfinite* HS
   stability, not to HS stability; HS stability implies character rigidity but
   not conversely. Since `SL_2(Z[1/2])` is already known to be character rigid
   (Peterson--Thom), **character rigidity cannot refute Question 1.2**. That is
   a real constraint on the lane: the cheap negative route is closed.

## 3. Chornomaz--Wagner: nothing in the graph, and the relevance is quantitative

No node mentions S-machines, Dehn functions or distortion. The paper proves
(Theorem, `main-theorem`) that a non-deterministic Turing machine of time
complexity `T(n)` is emulated by an S-machine of time-space complexity
`(T^(1+eps), T)`, against `(T^3, T)` in Sapir--Birget--Rips. The group-theoretic
export (their refinement of Birget--Ol'shanskii--Rips--Sapir Theorem 1.1) is:

> `G` finitely generated with word problem solvable by a non-deterministic
> Turing machine of time function `<= T(n)`, `T(n)^2` superadditive. Then for
> every `eps>0`, `G` embeds into a finitely presented `H_eps` with Dehn function
> `<= n^2 T(n^2)^(2+eps)`, with `G` boundedly distorted in `H_eps`, and **the
> Dehn function of `G` in `H_eps` is at most `T(n)^(2+eps)`**.

**Scope limit, stated so nobody mistakes it for a Higman replacement.** This
needs a *decidable* word problem with a time bound. Higman and Chiodo
(`torsion-free-higman-embedding`) need only a recursive presentation. The
repo's finitely-presented step (`finitely-presented-nonsofic-group-exists`,
via the finite-table cover) is therefore not superseded, and must not be
rewritten to depend on this.

**What is genuinely new for this repo** is the last clause, because the Dehn
function of `G` in `H` is exactly the modulus at which almost-representations
descend. Proved here as `subgroup-dehn-function-is-the-hyperlinearity-modulus`:
if `H=<A|R>` is finitely presented and `pi` has normalized-HS relator defect
`delta`, then every `w` of `G`-length `<= n` with `w =_G 1` obeys

```text
||pi(w) - 1||_2 <= delta_(G,H)(n) . delta,
```

because `w` is a product of at most `delta_(G,H)(n)` conjugates of relators and
conjugation is a `||.||_2`-isometry. So the qualitative fact "subgroups of
hyperlinear groups are hyperlinear" acquires an explicit modulus, and
Chornomaz--Wagner make that modulus `n^(2+eps)` for a group with quasilinear
word problem. Their §implications note the bound is quasi-optimal: for
non-hyperbolic `G` the isoperimetric gap of Gromov and Ol'shanskii forbids a
subquadratic Dehn function of `G` in any finitely presented host under a
quasi-isometric embedding.

Composite, established here as `effective-fp-nonhyperlinearity-transfer`: an
effective non-hyperlinearity certificate for a finitely generated `G` at scale
`(n, epsilon, alpha)` becomes one for a finitely presented `H_eps` at relator
defect `epsilon / delta_(G,H)(n)`.

## 4. Deliberately not authored

- No node re-states DV's Schramm-type theorem for marked von Neumann algebras
  (Thm 5.2 in the source). It is used only inside their proof of Theorem 1.4,
  which is imported as a whole.
- No node re-states Bader's proof that (T) equals its robust variant; that
  implication is already inside `el-r-polynomial-robust-spectral-gap`.
- No claim that Chornomaz--Wagner improves any existing repo result. It
  improves a *modulus* that the repo had never written down.
