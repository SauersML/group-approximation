# Thompson's F, Problem P_(2,2): what a proof that a pair has no common multiple must look like

Lane `hl-f-p22-invariant`, 2026-09-13. Target: a structural invariant showing that some pair of Guba's Problem
`P_(2,2)` has no nonzero common right multiple, which would make `thompson-f-is-not-amenable` true. Result:
no such invariant was found. Four families of candidate invariants are ruled out or reformulated, and one
sufficient combinatorial certificate is stated and tested on natural orders. Nothing here decides either
amenability root.

Nodes landed with this artifact:
- `monoid-ring-no-common-multiple-iff-harmonic-splitting` and its proof route;
- `thompson-f-ore-obstructions-must-see-finite-support` and its proof route;
- `thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs` and `thompson-f-private-pivot-orders-proof`.

MSI directory: `/scratch.global/sauer354/hl-f-p22-invariant/`.

## 1. Pins used (already verbatim on main)

- **Guba's alternative** (arXiv:2305.07113v4, after Problem `P_(d,m)`), pinned in
  `research/artifacts/thompson-f-ore-over-f2-2026-09-13.md` §1: "If this Problem has negative solution for at
  least one case, then $F$ is not amenable."
- **Lemma `gig`** (l.615), pinned in `research/artifacts/thompson-f-monomial-doubling-2026-09-13.md` §1.
- **Kielak's criterion**, pinned in `thompson-f-ore-criterion-citation`.
- The survey TeX is on MSI, e.g. `/scratch.global/sauer354/thompson-f-lit/x2305.07113/jgcc-template.tex`.

## 2. Candidate invariants and why each fails

| candidate | fate | reason |
|---|---|---|
| Leading term / valuation for a bi-order | dead | leading terms are multiplicative, and any two monomials of `M` have a common right multiple (Lemma `gig`), so the leading-term equation is always solvable |
| Ring homomorphism into an overring where `aR ∩ bR = 0` | dead for division rings | `K[F]` embeds in Malcev–Neumann series for a bi-order of `F`, where `a(a^-1 b) = b` |
| Abelianization / Newton polygons | dead | `K[F] -> K[Z^2]` is a ring map into a commutative domain, which is Ore |
| Grading and finite linear counts | only certify multiples | `dim(aV + bV) < dim aV + dim bV` forces `aV ∩ bV ≠ 0`; the grading gives finite blocks and nothing more |
| L²-dimension in an affiliated algebra | dead as an obstruction | for zero-divisor-free `a, b` the right ideals they generate there have full dimension, so their intersection is large |
| Configuration splitting (dual) | exact reformulation | `aK[M] ∩ bK[M] = 0` iff every `f : M -> K` is `g + h` with `a* g = 0` and `b* h = 0` |
| Private-pivot order on `M` | sufficient, local | two private points per `m` gives doubling (hence non-amenability), and with nonzero minors an explicit non-Ore pair; natural orders fail at degree 1 |

The L²-dimension row is a remark, not a landed claim: its hypotheses (injectivity of `a`, `b` on `ℓ²F` and
dimension additivity in the algebra of affiliated operators) were not pinned at source.

## 3. The splitting reformulation

For `a = Σ α_s s`, the transpose `(a* f)(m) = Σ_s α_s f(s m)` satisfies `⟨a u, f⟩ = ⟨u, a* f⟩`. So
`(aK[M])^⊥ = ker a*`, and `aK[M] ∩ bK[M] = 0` iff `K^M = ker a* + ker b*`. The proof extends a functional
from `aK[M] ⊕ bK[M]`. Over `F_2`, with `a` and `b` sums of monomial sets `A` and `B`: every `F_2`-configuration
is the XOR of an `A`-even and a `B`-even configuration.

This is where a non-amenability proof through `P_(2,2)` has to live. It needs a construction, for every
configuration, of a harmonic splitting on the infinite monoid. No finite window certifies it, since any
finite failure of splitting is dual to a finitely supported common multiple.

## 4. Private pivots

Left multiplication by `x_p` inserts the letter `p+k` at the least 0-based position `k` with `m[k] >= p+k`,
and leaves every other letter unchanged. Left division by `x_p` is unique when it exists. For `S = S_(3,5)`
and a total order `<` on each degree layer:
- `m_<(w)` is the largest `m` with `w ∈ S m`;
- `w` is private for `m` if `m_<(w) = m`.

Two private points for every `m` gives `|S Y| >= 2|Y|` for every finite `Y`. The claim node gives the
triangular argument that turns such an order into explicit non-Ore pairs.

**Computation** (`experiments/thompson-f/p22inv/pivot_orders.py`, md5 `cfed287544116fa0aa3de5856a82eb61`,
run on MSI with `/usr/bin/python3.12`, arguments `4 7`; output `run_d4_L7.json`, md5
`47c8f2678adf58406fef57a5ca245133`):

```
formula_check True
lex {'m': [0], 'private': 1} [1, [0]]
revlex {'m': [0], 'private': 1} [1, [0]]
sum_lex {'m': [0], 'private': 1} [1, [0]]
sum_revlex {'m': [0], 'private': 1} [1, [0]]
colex_neg {'m': [4], 'private': 1} [1, [4]]
lex_neg {'m': [4], 'private': 1} [1, [4]]
sum_neg_lex {'m': [4], 'private': 1} [1, [4]]
```

**How to read it.**
- Increasing orders fail at `x_0`: of the nine points of `S x_0`, only `x_0^3` has `x_0` as its largest
  factor.
- Decreasing orders fail at `x_4`.
- A working order would have to be adapted to the factor structure of `S_(3,5)` on every layer. It would
  exist only if `S_(3,5)` is doubling, which by `thompson-f-nonamenable-iff-some-monomial-set-doubles` is at
  least as hard as the root.

## 5. Exact gap

Either route to a non-Ore pair of `P_(2,2)` stands open:
- **(a) Splitting:** for a fixed pair `(a, b)` and every configuration `f`, a construction of `h ∈ ker b*`
  with `a* h = a* f`;
- **(b) Private pivots:** an order on `M` giving every `m` two private points in `S_(3,5) m`, with a pair
  whose minors on the chosen private pairs are nonzero.

Route (b) implies doubling of `S_(3,5)`. By item 1 of `thompson-f-nonamenable-iff-some-monomial-set-doubles`,
doubling can hold only if `F` is not amenable. Natural lexicographic orders fail at degree 1. Nothing here
bears on the amenable side.
