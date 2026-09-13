# Nonsofic actions of sofic groups: containment seeds and the Bernoulli no-go (2026-09-13)

Lane `solve-sofic-actions`, working on the roots `sl3z-admits-nonsofic-action`,
`mixing-free-nonsofic-action-of-sofic-group` and `hyperlinear-nonsofic-free-action`.
None of the three roots is settled. This file records the sources, and the two
transfer and rigidity results landed as nodes.

## 0. Sources, verbatim

* **Păunescu**, arXiv:1002.0605v5 (J. Funct. Anal. 261 (2011)). Definition 1.4,
  Definition 1.12 and Proposition 1.15 are quoted verbatim in
  `research/artifacts/free-nonsofic-action-sources-verified-2026-09-11.md` (lines
  112–121) and `research/artifacts/paunescu-class-measure-equivalence-2026-09-12.md`
  §0. In particular:
  > **Proposition 1.15.** Let α be a free action. Then E_α is a sofic equivalence
  > relation if and only if α is a sofic action.
* **Cordeiro**, arXiv:1608.05608v2, Proposition 3.2(a), from the ME artifact §0:
  > If R is sofic and A ⊆ X is any (non-null) subset, then R|_A is sofic.
* **Popa**, *Cocycle and orbit equivalence superrigidity for malleable actions of
  w-rigid groups*, arXiv:math/0512646. The TeX source was fetched on MSI
  (`/scratch.global/sauer354/solve-sofic-actions/popa/p`). Abstract, verbatim:
  > We prove that if a countable discrete group $\Gamma$ is {\it w-rigid}, i.e. it
  > contains an infinite normal subgroup $H$ with the relative property (T) (e.g.
  > $\Gamma= SL(2,\Bbb Z) \ltimes \Bbb Z^2$, or $\Gamma = H \times H'$ with $H$ an
  > infinite Kazhdan group and $H'$ arbitrary), and $\Cal V$ is a closed subgroup
  > of the group of unitaries of a finite separable von Neumann algebra (e.g.
  > $\Cal V$ countable discrete, or separable compact), then any $\Cal V$-valued
  > measurable cocycle for a measure preserving action $\Gamma \curvearrowright X$
  > of $\Gamma$ on a probability space $(X,\mu)$ which is weak mixing on $H$ and
  > {\it s-malleable} (e.g. the Bernoulli action $\Gamma \curvearrowright
  > [0,1]^\Gamma$) is cohomologous to a group morphism of $\Gamma$ into $\Cal V$.

  Terminology 5.6.0 (verbatim): *"We say that $\Gamma \curvearrowright^\sigma
  (X,\mu)$ is $\mycal U$-cocycle superrigid if any $\Cal V$-valued cocycle for
  $\sigma$ is cohomologous to a group morphism of $\Gamma$ into $\Cal V$, $\forall
  \Cal V\in \mycal U$. If $\mycal U$ is the family of all discrete groups, we
  simply say that $\sigma$ is cocycle superrigid."*
* **Facts about the binary Leavitt unit group `K`**, all from main:
  * simple: `binary-leavitt-unit-group-is-simple`;
  * property (T) for `EL_4(L)` and nonsoficity of the unit group:
    `universal-leavitt-el4-nonsofic`, Lean `ambient_full_profile` and
    `universalLeavittUnits_not_isSofic`;
  * `GL = EL`: `leavitt-gl-equals-el-and-perfect-unit-group`.

## 1. Containment transfer

`free-action-containing-nonsofic-group-relation-is-nonsofic`, route
`nonsofic-subrelation-transfer-proof`. Suppose a free action of a nonsofic group
lives inside a restricted orbit relation of a free `G`-action. Then that
`G`-action is not sofic. The proof restricts a sofic embedding (Definition 1.12)
to the subrelation's Feldman--Moore algebra, and uses Proposition 1.15 twice
together with Cordeiro 3.2(a). This is folklore-level and no novelty is claimed.

## 2. The Bernoulli no-go

`simple-kazhdan-bernoulli-relation-hosts-contain-the-group`, route
`simple-kazhdan-bernoulli-host-via-popa-superrigidity`. Let `H` be infinite,
simple and Kazhdan, and suppose its Bernoulli relation sits inside a restricted
orbit relation of an essentially free `G`-action. Then:
- the containment cocycle `H × Y → G` is cohomologous to a morphism `ρ` (Popa);
- `ψ = φ^(-1)·θ` is `ρ`-equivariant;
- `ker ρ = H` would make `ψ` essentially constant, putting `A` in one countable
  orbit, which is impossible;
- so `ρ` is injective.

The argument is the one behind Popa's OE superrigidity, specialized to
containment; no novelty is claimed.

Corollary for `K`: `leavitt-unit-bernoulli-relations-have-no-sofic-host`.

## 3. What this gives the three roots

* **`sl3z-admits-nonsofic-action`.** New sufficient condition: one free
  `SL_3(Z)`-action whose restricted orbit relation contains a free action of any
  nonsofic group. For the known nonsofic Kazhdan witness `K`, malleable seeds are
  dead: they force `K ≤ SL_3(Z)`, which is impossible because `SL_3(Z)` is
  residually finite. Seeds would have to be non-s-malleable free actions of `K`,
  or nonsofic groups that aren't simple Kazhdan, e.g. the torsion-free nonsofic
  groups on main.
* **`mixing-free-nonsofic-action-of-sofic-group`.** The same containment seeds
  feed the Howe--Moore transfer (`howe-moore-lattice-nonsofic-action-transfers-to-mixing`).
  Any lattice of a Howe--Moore group with such a containment gets a free mixing
  nonsofic action. The Bernoulli no-go applies verbatim.
* **`hyperlinear-nonsofic-free-action`.** Containment gives nonsoficity but also
  the inclusion `L(R_H) ⊆ L(R_G|_A)`. A hyperlinear host would therefore need a
  hyperlinear seed relation of a nonsofic group, which is Pestov's Question 3.4
  lifted to relations. No new route.

## 4. Not done

* No non-s-malleable free action of `K` was analysed (e.g. actions weakly mixing
  only on subgroups, or Gaussian actions of non-orthogonal representations).
* No other nonsofic group (non-Kazhdan or non-simple) was tested as a seed.
* Popa's main theorems in the body (5.2, 5.3) were not re-read; only the abstract
  and Terminology 5.6.0 were quoted.
