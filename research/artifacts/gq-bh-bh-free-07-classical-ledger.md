# Classical embedding techniques vs. the live Boone–Higman gates (bh-free-07, 09-18)

Free lane, seed "older literature". No new theorem is claimed here. This is a ledger of
classical (1958–2004) techniques, how much of each main already uses, and three concrete
technique-to-gate proposals, each with its exact gap. Source status is marked on every
line: **[src]** means read at source this session; **[mem]** means from memory, not
re-read (paywalled or offline). Repo coverage is the number of research/*.md files on
origin/main that mention the author (git grep, 09-18).

## 1. Ledger

| Technique (source) | Statement (short) | Status | Repo files | Live gate it touches |
|---|---|---|---|---|
| Higman 1961, benign subgroups | f.g. recursively presented ⇒ subgroup of f.p.; r.e. subgroups of free groups are benign | [mem] | many | none new; shell envelopes are recursively presented, so Higman gives an f.p. OVERgroup, never f.p. of E_ν itself |
| Boone–Higman 1974 (J. Austral. MS 18) | solvable WP ⟺ embeds in a simple subgroup of an f.p. group | [mem] | root + `boone-higman-thompson-simple-envelope` | owned by bh-higman-classic |
| Thompson 1980 (Word Problems II) | the simple subgroup can be taken f.g. (via V-type groups) | [mem] | 14 | owned by bh-higman-classic |
| Kuznetsov 1958 | recursively presented simple ⇒ solvable WP | [mem] | 57 | bh-refute (Kuznetsov profile) |
| Macintyre 1972; B. H. Neumann 1973 | f.g. G has solvable WP ⟺ G embeds in every existentially closed group | [mem] | 2 (Macintyre), 36 (e.c.) | none: e.c. groups are never f.g., so no host |
| **Sacerdote 1977** (J. Algebra 49, 212–221), "The Boone–Higman theorem and the conjugacy problem" | a conjugacy-problem refinement of Boone–Higman (exact statement NOT recovered; Elsevier bot wall from MSI) | **not read** | **0** | P1 below |
| Higman 1974 (ANU notes) | G_{n,r} f.p. simple; Ω-algebra (Cantor algebra) method | [mem] | many | background |
| E. Scott 1984 (J. Algebra) | GL_n(Z) ↪ f.p. simple; an f.p. simple group with unsolvable conjugacy problem | [mem] | 58 | bh-refute: CP gives no obstruction |
| **K. S. Brown 1987** (J. Pure Appl. Algebra 44), finiteness properties | Houghton H_n is F_{n−1} but not F_n; H_1, H_2 are not f.p. | [mem] | Houghton appears via gq-houghton-q only | **P2 below (shell germ gate)** |
| Röver 1999; Nekrashevych 2004/2018 | V(G) f.p. simple for Grigorchuk / contracting G | [mem] | 326 | background |
| Wilson 1971; Grigorchuk 2000 | trichotomy for just-infinite groups | [mem] | used in `boone-higman-iff-fp-just-infinite-hosts` | background |
| **Bridson 1998** (arXiv math/9810188, GTM 1) | if a class of f.g. groups is closed under isometric amalgamation along free subgroups, each member q.i.-embeds in a member with no proper finite-index subgroups | **[src: abstract]** | 147 (Bridson) | P3 below |
| Birget–Ol'shanskii–Rips–Sapir 2002 | WP in NP ⟺ embeds in f.p. group with polynomial Dehn function | [mem] | 44 | bh-free-02, bh-refute |
| Ol'shanskii–Sapir 2004 (Memoirs) | Higman embeddings preserving solvable conjugacy problem | [mem] | many | none new |
| Clapham 1967; Valiev 1975 | decidable f.g. ↪ decidable f.p.; Valiev's universal f.p. group | [mem] | 91; **1** | P4 below |

## 2. Proposals (technique → gate), each with its gap

**P1 (Sacerdote 1977, absent from main).** It is the only classical Boone–Higman refinement
with zero repo mentions. If it controls the conjugacy problem of the simple envelope, it
bears on bh-refute's decision-problem list (which already shows CP gives no obstruction via
Scott 1984), and possibly on how "tame" Thompson's envelope can be made (bh-higman-classic).
**Gap:** the paper was not obtained (J. Algebra, Elsevier bot wall from MSI, like Kolster).
Expected impact: low. Needs a browser download by the user.

**P2 (Brown's Houghton theorem as a template for the shell germ gate).**
- By `shell-germ-group-has-index-two-fiber-product`, Q_ν is f.p. iff F_ν = R_ν ×_Z R_ν is,
  where R_ν = ⟨λ(P), s⟩ acts near-regularly on ONE ray N (η = near index).
- Houghton's groups show the classical pattern: permutation groups of n rays that are
  eventually translations are f.p. only for n ≥ 3 (H_1, H_2 are not; Brown 1987).
- The single-shift shell is a one-ray object, and F_ν is a two-ray object. So Brown's pattern
  predicts exactly the failures recorded on main: free-shift and A5*A5 fail at R_ν, and the
  Z^2 spiral gives a non-f.p. R_ν.
- Proposal: a **multi-ray shell**, whose singular point has a germ group from the base with
  at least 3 independent "ends". Then the germ-group gate becomes a Houghton-with-coefficients
  question, which Brown's Morse-theoretic method is designed for.
- **Gap (proved obstruction for the naive version, by the computation below).** With base 2V
  and singular point p = (0^∞, 0^∞), whose germ group is Z^2, cells compatible with both shifts
  are forced to be c_{(i,j)} = 0^{i+a}1C × 0^{j+b}1C. As i → ∞ with j fixed, these accumulate
  on the axis {0^∞} × C, not only at p. The singular set then contains the axes, which carry
  uncountably many 2V-orbits. That violates hypothesis (1) of BHM Theorem 2.1 (finitely many
  B-orbits on sing(G)^n).
- So a multi-ray shell needs a base whose germ at ONE point has several ends while its cells
  still shrink to that point. Coordinate shifts of nV do not provide this, and I know no base
  that does.
- Pointer posted on board/bh-shell-germ.md.

**P3 (Bridson 1998 + no-finite-quotient hosts).** Bridson gives, inside any class closed under
isometric amalgamation along free subgroups (e.g. CAT(0), hyperbolic), an overgroup Ĝ with no
proper finite-index subgroups. With `boone-higman-iff-fp-just-infinite-hosts` and the
maximal-kernel route, such Ĝ is a candidate host whose simple quotients are infinite.
**Gap:** nothing keeps G ∩ M = 1 for a maximal normal M, or makes M finitely normally
generated. That is exactly the open hypothesis of `boone-higman-via-ck-maximal-kernel`.
Pointer posted on board/bh-ck-kernel.md.

**P4 (Valiev 1975).** Main mentions Valiev once. His universal f.p. group (which contains
every f.p. group) bears on bh-universal and bh-logic (`common-decidable-hosts-iff-uniform-word-problem`).
**Gap:** the exact statement was not recovered at source. Pointer posted on
board/bh-universal.md.

## 3. Verdict
No overlooked classical technique closes a live gate as it stands. The one with a concrete
mechanism is P2. It explains the recorded shell germ-gate failures as a one/two-ray Houghton
phenomenon, and it isolates the missing object: a base whose germ group at a single point has
at least three ends while its cells shrink to that point. P1 and P4 need sources nobody on the
swarm has read.
