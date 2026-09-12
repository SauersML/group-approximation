# Products with a sofic factor: the single-fibre Garden of Eden filter and the quantitative residue

Lane `w4-free-pos-b`, 2026-09-12. Mathematics on paper; no computation.

**Setting.** `G` is surjunctive and `K` is sofic. The claim
`finite-direct-products-of-surjunctive-groups-are-surjunctive` is open when neither factor lies in the
LEF permanence closure (`products-with-lef-permanence-closure-factors-are-surjunctive`). The fibre device of
`research/artifacts/w3-products-permanence-closure-2026-09-12.md`, Section 3, stops because sofic
realizations break the decoder identity on a positive fraction of points.

**This note.**
- Section 1 repairs that loss by storing the broken coordinates in extra alphabet, which costs only an
  `epsilon` fraction.
- Section 2 proves that whenever the Garden of Eden pattern sits in one fibre `{g} x K`, the saved deficit
  beats that cost. So no strict automaton over `G x K` has a single-fibre Garden of Eden pattern.
- Section 3 isolates what multi-fibre patterns need: a quantitative form of surjunctivity for `G`, which
  sofic groups have.

## 0. Conventions

- Automata over `G x K` read `tau(x)(g,k) = mu((x(g g_m, k k_m))_(m in M))` with memory
  `M <= G x K`, `m = (g_m, k_m)`.
- The decoder `sigma` has memory `N` and rule `nu`, and `sigma tau = id`. Put `X = tau(A^(G x K))` and
  `q = |A|`.
- `M_K = { k_m }` and `N_K = { k_n }`. `P <= K` is a finite set containing `1`, `M_K`, `N_K`, their
  products `k_n k_m`, and the finite sets used below.

**Sofic models.** For a finite set `V`, a map `k |-> pi_k` from `K` to `Sym(V)` is a `(P, epsilon)`-model
if at least `(1 - epsilon)|V|` points `v` are *good*: `v.k := pi_k(v)` satisfies `(v.k).k' = v.(k k')` for
`k, k', k k'` in `P`, and `v.k != v.k'` for distinct `k, k'` in `P`. `K` is sofic iff such models exist
for all `P` and `epsilon`. The right-action form is obtained from the usual left form through `k |-> k^-1`.

## 1. The transplant and its repair

Given a model `(V, pi)`, define automata over `G` with alphabet `A^V`:

    tau_V(y)(g)(v)   = mu(( y(g g_m)(v.k_m) )_(m in M)),
    sigma_V(y)(g)(v) = nu(( y(g g_n)(v.k_n) )_(n in N)).

**Lemma 1.1 (exact at good points).** Let `P` contain `N_K M_K` and let `v` be good.
1. `sigma_V(tau_V(y))(g)(v) = y(g)(v)` for all `y` and `g`.
2. If `E <= G x K` is finite with `E_K M_K <= P` and `p` is a Garden of Eden pattern of `tau` on `E`, then
   for every `y`, the pattern `(tau_V(y)(g e_G)(v.e_K))_((e_G, e_K) in E)` differs from `p`, for every
   `g in G`.

**Proof.**
1. `sigma_V(tau_V(y))(g)(v)` evaluates `nu` on the values `mu((y(g g_n g_m)((v.k_n).k_m))_m)`. At a good
   `v`, `(v.k_n).k_m = v.(k_n k_m)`, and the points `v.k` for `k in P` are distinct.
   - So two addresses `(g g_n g_m, v.(k_n k_m))` coincide iff `g_n g_m = g_(n') g_(m')` and
     `k_n k_m = k_(n') k_(m')`. That is, iff `n m = n' m'` in `G x K`.
   - So the expression is the decoder identity of `G x K` evaluated at the configuration
     `x(g', k') := y(g')(v.k')`, defined on the needed finite set, with the same coincidence pattern.
     It returns `x(g, 1) = y(g)(v)`.
2. Suppose some `y` and `g` realize `p`. On `E M` put
   `z(e_G g_m, e_K k_m) := y(g e_G g_m)(v.(e_K k_m))`.
   - **Well defined.** Equal addresses have equal `G`-parts. Their `K`-parts are equal elements of `P`, so
     the points `v.(e_K k_m)` agree.
   - **Realizes `p`.** At a good `v`, `(v.e_K).k_m = v.(e_K k_m)`. So
     `tau(z)(e) = mu((y(g e_G g_m)((v.e_K).k_m))_m) = tau_V(y)(g e_G)(v.e_K) = p(e)` for every `e in E`.

   So `p` is not a Garden of Eden pattern, a contradiction. QED.

**The repair.** Let `V_bad` be the set of points that are not good, so `|V_bad| <= epsilon |V|`. Define
the automaton over `G`

    Psi(y)(g) = ( tau_V(y)(g), y(g)|_(V_bad) ) in A^V x A^(V_bad).

**Lemma 1.2.** `Psi` is injective.

**Proof.** The stored track gives `y(g)` on `V_bad`. At good `v`, Lemma 1.1(1) recovers `y(g)(v)` from the
first track. QED.

So the decoder's failure on bad points costs a factor `q^(|V_bad|) <= q^(epsilon |V|)` in the output
alphabet, and nothing else.

## 2. Theorem F: no single-fibre Garden of Eden pattern

**Theorem F.** Let `G` be surjunctive and `K` sofic, and let `tau` be injective over `G x K` with image
`X`. Then every pattern on a finite subset of one fibre `{g} x K` is the restriction of a point of `X`.

**Proof.**
1. **Setup.** By invariance it is enough to take `g = 1`. Suppose `p` on `E <= {1} x K` is a Garden of
   Eden pattern, with `E_K` the `K`-coordinates of `E`. Take `P` containing `1`, `M_K`, `N_K`,
   `N_K M_K`, `E_K` and `E_K M_K`. Take a `(P, epsilon)`-model `V`, with `epsilon` to be fixed.
2. **Disjoint blocks.** For good `v` the block `v.E_K` has `|E_K|` points. A point `w` lies in at most
   `|E_K|` blocks, one for each `e in E_K`, since `pi_e` is a permutation. So each block meets at most
   `|E_K|^2` others. A greedy choice gives a set `V'` of good points with pairwise disjoint blocks and
   `|V'| >= (1 - epsilon)|V| / (|E_K|^2 + 1)`.
3. **Column count.** Let `C = { tau_V(y)(1) : y }`, a subset of `A^V`. By Lemma 1.1(2) with `e_G = 1`,
   every element of `C` differs from `p`, transported to the block `v.E_K`, for each `v in V'`. The blocks
   are disjoint, so `|C| <= q^|V| (1 - q^(-|E|))^(|V'|)`. Invariance under `G` gives the same bound at
   every `g`.
4. **Compression.** `Psi` of Lemma 1.2 is an injective automaton over `G` whose output symbols lie in
   `C x A^(V_bad)`, a set of size at most
   `q^|V| · (1 - q^(-|E|))^((1-epsilon)|V|/(|E_K|^2+1)) · q^(epsilon |V|)`.
   Choose `epsilon` with
   `epsilon log q < -((1 - epsilon) / (|E_K|^2 + 1)) log(1 - q^(-|E|))`. This choice depends only on `q`,
   `E` and `K`. Then for large `|V|` this size is below `q^|V|`.
5. **Contradiction.** Compose `Psi` with a symbolwise injection of that symbol set into `A^V`. The result
   is an injective automaton on `(A^V)^G` that misses some symbols, so it is not onto. That contradicts
   surjunctivity of `G`. QED.

**Filter.** A strict automaton over `G x K`, with `G` surjunctive and `K` sofic, has every Garden of Eden
pattern meeting at least two fibres `{g} x K` and `{g'} x K` with `g != g'`. By symmetry, when `G` is
sofic and `K` surjunctive, Garden of Eden patterns meet two fibres `G x {k}`.

**What the proof does not reach.** Take a pattern on `E` with two or more `G`-coordinates. Step 3 then
constrains, at each good `v`, a configuration over `G` with alphabet `A^(E_K)`, and that configuration
lies in the proper subshift described in Section 3. It does not constrain a single output symbol. So
step 4 produces an injective automaton into a product of copies of a proper subshift. Surjunctivity of
`G` alone says nothing about such maps.

## 3. The multi-fibre residue: quantitative surjunctivity

**Definition.** A group `G` is *quantitatively surjunctive* (QS) if the following holds for every finite
alphabet `B` and every proper subshift `Y` of `B^G`. There is `delta_Y > 0` such that for every finite
alphabet `D` and all integers `n >= 1` and `j, j' >= 0` with `(j' - j) log|D| < delta_Y n`, no injective
automaton maps `(B^n x D^j)^G` into `Y^n x (D^(j'))^G`.

**QS implies surjunctive.** Take `n = 1` and `j = j' = 0`. A strict automaton on `B^G` is an injective
automaton into its proper image `Y`.

**Theorem Q.** If `G` is QS and `K` is sofic, then `G x K` is surjunctive.

**Proof.**
1. **The subshift.** Let `tau` be strict over `G x K` with Garden of Eden pattern `p` on `E`, where `E` has
   `G`-coordinates `E_G` and `K`-coordinates `E_K`. Put
   `Y = { w in (A^(E_K))^G : for every g, (w(g e_G)(e_K))_(e in E) != p }`.
   This is a proper subshift. Let `delta = delta_Y`.
2. **The transplant.** Take `P` as in Theorem F and a `(P, epsilon)`-model `V`. Take the blocks `V'` of
   Theorem F, step 2, with `n = |V'|`, and let `R` be the points outside the blocks.
3. **The map.** By Lemma 1.1(2), for good `v in V'` the configuration `g |-> (tau_V(y)(g)(v.e_K))_(e_K)`
   lies in `Y`. Put
   `Psi(y)(g) = (tau_V(y)(g)|_(blocks), tau_V(y)(g)|_R, y(g)|_(V_bad))`.
   This is the data of Lemma 1.2 rearranged, so it is injective. It maps
   `((A^(E_K))^n x A^(|R|))^G` into `Y^n x (A^(|R| + |V_bad|))^G`.
4. **Contradiction.** With `B = A^(E_K)`, `D = A`, `j = |R|` and `j' <= |R| + epsilon |V|`, QS forbids this
   as soon as `epsilon |V| log q < delta (1 - epsilon)|V| / (|E_K|^2 + 1)`. That holds for small
   `epsilon`, since `delta` depends only on `Y`. QED.

**Sofic groups are QS.**
1. **Setup.** Let `Y <= B^G` miss a pattern `r` on a finite `W`. Suppose `Phi` is injective from
   `(B^n x D^j)^G` into `Y^n x (D^(j'))^G`. It has an automaton left inverse `Lambda`: the inverse on the
   image is continuous and equivariant, and its local rule extends to all patterns.
2. **Transplant.** Transplant `Phi` and `Lambda` to a sofic model `Omega` of `G` whose fraction of good
   points is at least `1 - epsilon'`.
3. **Lower bound.** Outputs determine inputs at good points. So the number of distinct outputs is at least
   `(|B|^n |D|^j)^((1 - epsilon')|Omega|)`.
4. **Upper bound.** At good points the output windows are genuine output patterns of `Phi`. So each of the
   `n` tracks misses `r` on `c |Omega|` disjoint windows, with `c = (1 - epsilon')/(|W|^2 + 1)`. This
   gives at most `|B|^(n|Omega|) (1 - |B|^(-|W|))^(n c |Omega|) |D|^(j' |Omega|)` outputs.
5. **Conclusion.** Letting `epsilon' -> 0` with `Phi` fixed gives
   `-n log(1 - |B|^(-|W|)) / (|W|^2 + 1) <= (j' - j) log|D|`. So QS holds with
   `delta_Y = -log(1 - |B|^(-|W|)) / (|W|^2 + 1)`.

**Place in the graph.**
- **What QS buys.** QS sits between soficity and surjunctivity, and it turns the fibre device into a
  proof for every sofic second factor.
- **Status.** `surjunctive-groups-are-quantitatively-surjunctive` is open. Known surjunctive nonsofic
  groups lie in the LEF permanence closure, whose products are handled exactly, so they are no test.
  A test needs a surjunctive group outside that closure, and none is known.
- **Beyond counting.** On a nonsofic group, QS is an entropy-type deficit for proper subshifts, stable
  under taking powers. It is not supplied by any recorded invariant.
