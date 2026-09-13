# Zaremsky Problem 2.8: infinite-dimensional torsion-free F_∞ groups without F (part 1)

Lane z2-08-tf-finf-no-f, 2026-09-13. Root: `zaremsky-2-08-infinite-dim-torsion-free-f-infinity-without-f`.

Problem (Zaremsky, *Some open problems*, July 12, 2026, §2 Problem 8, verbatim): "Find an infinite
dimensional torsion-free group of type F∞ that does not contain F."

Literature access was bounded: the web-search budget was spent, and the arXiv API was rate-limited (HTTP 429/503)
during this pass. Every citation below that is not re-read is marked "not re-read".

## 1. Reading

- **Type F_∞**: a K(G,1) with finitely many cells in each dimension.
- **Infinite dimensional**: `cd G = ∞`. For torsion-free `G` this is equivalent to having no finite-dimensional
  K(G,1):
  - `gd >= cd` always;
  - Eilenberg–Ganea gives `gd <= max(cd, 3)`.

  The Wall obstruction concerns finite complexes, so it does not separate the two readings.
- **Omits F**: no subgroup isomorphic to Thompson's `F`.

Calibration:
- `F` is of type F_∞ with infinite cd (Brown–Geoghegan 1984, not re-read), torsion-free, and contains `F`.
- `Z^n` omits `F` and is of type F, but `cd Z^n = n`.

## 2. Firewall: what an answer cannot be

**2.1 Kropholler's theorem** (Kropholler, "On groups of type (FP)∞", J. Pure Appl. Algebra 90 (1993)): torsion-free
groups of type FP_∞ in Kropholler's class H𝔉 have finite cohomological dimension.

Read so far only second-hand, from Januszkiewicz–Kropholler–Leary, arXiv:0908.3669v1:
- p. 1 defines `H_α𝔛`: `H_0𝔛 = 𝔛`; `H_{α+1}𝔛` is the class of groups admitting a finite-dimensional contractible
  G-complex with stabilizers in `H_α𝔛`; unions at limit ordinals; `H𝔉` is the union over all ordinals.
- p. 1, verbatim: "until recently the key known example of a non-H𝔉 group was Thompson's group F, known to be of type
  FP∞ [5] and yet having infinite cohomological dimension and so failing the key finiteness theorem for H𝔉-groups of
  type FP∞ established in [15]".
- p. 2: "The torsion-free groups in H₁𝔉 are precisely the groups of finite cohomological dimension".
- p. 2: it is "an open problem whether there are torsion-free H𝔉-groups which are not in H₃𝔉".
- p. 1: other non-H𝔉 groups exist, namely infinite groups all of whose finite-dimensional contractible complexes have
  a global fixed point (their reference [1], Arzhantseva–Bridson–Januszkiewicz–Leary–Minasyan–Świątkowski). None is
  known to this lane to be of type F_∞.

The original theorem statement is not yet re-read.

Consequences:
- For finitely generated groups, LH𝔉 = H𝔉.
- H𝔉 is closed under subgroups (a G-complex restricts to any subgroup), so H𝔉-groups omit `F`.
- Any answer to 2.8 lies outside H𝔉.

Classes inside H𝔉 by definition: groups acting cellularly on a finite-dimensional contractible complex with
stabilizers in H𝔉 (transfinitely iterated). In particular:
- elementary amenable groups: see 2.2;
- groups acting properly on finite-dimensional contractible complexes (finite stabilizers), which is already cd
  finite for torsion-free groups;
- graphs of H𝔉-groups (Bass–Serre trees are 1-dimensional).

**2.2 Elementary amenable groups.** Kropholler–Martínez-Pérez–Nucinkis (not re-read; recorded by lane z1-12 at
`zaremsky-1-12-f-infinity-amenable-non-elementary-amenable`): elementary amenable groups of type FP_∞ are virtually
soluble of finite Hirsch length. Torsion-free ones have finite cd. Dead.

**2.3 Subgroups of F.** A subgroup `H <= F` answering 2.8 is torsion-free of type FP_∞ with infinite cd, so by 2.2
it is not elementary amenable. Omitting `F`, it would refute the Brin–Sapir conjecture (Problem 2.3, "every subgroup of
F is elementary amenable or contains F"). Conversely, Brin–Sapir would exclude every subgroup of `F`. Not attacked
here; peer lane z2-03-brin-sapir.

**2.4 `SL_n(Z[t])`.**
- The congruence subgroup for the ideal `(p, t)` (p odd) is torsion-free. A torsion element evaluates at `t = 0` to
  a torsion element of the level-`p` congruence subgroup of `SL_n(Z)`, which is torsion-free, so it evaluates to `I`.
  It is then unipotent, since the characteristic polynomial has coefficients in `Z[t] ∩ Qbar = Z`, and of finite
  order, so it is `I`.
- Its cd is infinite: the elementary matrices `e_12(t^k)` generate `⊕_k Z`.
- But `SL_n(Z[t])` is not FP_{n−1} (Bux–Mohammadi–Wortman, Comment. Math. Helv. 85 (2010), not re-read), and neither
  are its finite-index subgroups. Dead.

## 3. Sufficient conditions for omitting F

- **Residual finiteness (PROVED, landed).** `thompson-f-is-not-residually-finite`: a displacement argument puts a
  fixed nontrivial commutator of `F` into every finite-index normal subgroup. Open reduction:
  `some-rf-torsion-free-f-infinity-group-has-infinite-cd`.
- **Tits alternative.** A group whose finitely generated subgroups contain `F_2` or are virtually soluble omits `F`:
  - `F` has no free subgroups (Brin–Squier; repo `thompson-f-has-no-free-subgroups`);
  - `F` is not virtually soluble.
    - Proof sketch (to be written as a node): the commutator step of the residual-finiteness proof shows that every
      finite-index normal subgroup `N` contains `[F_[a,b], F_[a,b]]`, where `F_[a,b] ≅ F` for a dyadic `[a,b]`.
    - So `N` contains a copy of `F'`. If `N` were soluble, then so would be `F'`, hence `F` (as `F/F'` is abelian).
    - `F` is not soluble, since it is not elementary amenable (Cannon–Floyd–Parry §4, not re-read).
- **Coherence.** `F` contains `Z ≀ Z`. Take `g ≠ 1` supported in `[a, x_0^{-1}(a)]`.
  - The conjugates `x_0^{-k} g x_0^k` have supports with pairwise disjoint interiors, so they generate `⊕_k Z`.
  - Every element of that subgroup is supported in a compact subinterval of `(0,1)`, while no nonzero power of `x_0`
    is. So `⟨x_0, g⟩ = ⊕_k Z ⋊ ⟨x_0⟩ ≅ Z ≀ Z`.
  - `Z ≀ Z` is not finitely presented (Baumslag 1961, not re-read). So `F` is incoherent, and coherent groups omit `F`.

Each of these classes meets H𝔉 in examples of finite cd. So an answer from them would be a new non-H𝔉 group of type
FP_∞ inside a "tame" class: residually finite, Tits alternative, or coherent. None is known to this lane.

## 4. Candidate families

| family | torsion-free | F_∞ | cd | omits F | verdict |
|---|---|---|---|---|---|
| `F`, `F_n`, `F_{n,r}`, Stein `F_{2,3}` | yes | yes | ∞ | no | dead |
| `T`, `V`, `V_{n,r}`, `nV` | no | yes | ∞ | no | dead |
| braided / pure braided `F`, cloning-system groups | yes (pure) | yes (known cases) | ∞ | no | dead (trivially decorated elements give `F`) |
| Lodha–Moore, Monod `H(A)` | yes | Lodha–Moore yes | ∞ | no | dead |
| Houghton `H_n` | no | F_{n−1} not F_n | — | — | dead |
| elementary amenable | — | FP_∞ ⇒ | finite | yes | dead by 2.2 |
| linear char 0, e.g. `SL_n(Z[t])` | virtually | not F_∞ in known infinite-vcd cases | — | yes | dead by 2.1/2.4 |
| hyperbolic, finite-dim CAT(0), RAAGs, MCG, `Out(F_n)` | — | — | finite | yes | dead (finite vcd) |
| topological full groups of Cantor minimal systems | no | — | — | — | dead (torsion) |
| branch / self-similar groups | varies | branch groups not fp | — | yes (RF) | open: torsion-free F_∞ self-similar group of infinite cd |
| Guba–Sapir diagram groups | yes | F_∞ over finite complete presentations (Farley, not re-read) | often ∞ | ? | open direction, §5 |

## 5. Diagram groups: why lengthening without shifting fails

Worked example: `P = ⟨x, a, b, c | x = xa, a = b, b = c, c = a⟩`, base word `x`.
- The words derivable from `x` are `x s` with `s ∈ {a,b,c}^*`.
- Fix `|s| = n`. Letter changes at distinct positions give squares, so this part of the Squier complex is a product of
  `n` triangles, an `n`-torus.
- The moves `x s ↔ x a s` commute with every letter change at the old positions. They attach a mapping cylinder of the
  subtorus inclusion `T^n → T^{n+1}`.
- So the Squier component is a mapping telescope of `T^0 ⊂ T^1 ⊂ T^2 ⊂ …`, and `D(P, x) ≅ ⊕_{n>=1} Z`. It has
  infinite cd, but it is infinitely generated.

Lesson:
- Infinite cd in diagram groups needs unboundedly long words with independent spherical pieces.
- Finite generation needs a derivation that shifts pieces back, as `x = x^2` does for `F`, where the splitting is
  binary.
- The crux: does every finite complete presentation whose diagram group is finitely generated and infinite-dimensional
  contain the binary splitting that produces `F`? Recorded as an open direction, not a node, until Farley's theorem is
  re-read.

## 6. Landed (this pass)

- 080ca929d6: root, both answer claims, both answer routes.
- 69c9513252: `thompson-f-is-not-residually-finite` (+proof), `some-rf-torsion-free-f-infinity-group-has-infinite-cd`,
  `tf-finf-infinite-cd-omits-f-via-residual-finiteness`.
