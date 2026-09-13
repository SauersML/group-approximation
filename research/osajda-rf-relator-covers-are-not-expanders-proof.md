---
rg: 2
id: osajda-rf-relator-covers-are-not-expanders-proof
kind: route
title: A character dual to one fundamental cycle gives a test function on the Z/2-homology cover with Rayleigh quotient 4/n
target: osajda-rf-relator-covers-are-not-expanders
requires:
  - osajda-monster-hosts-for-bc-module-route
---

**1. Voltage description of the cover.**
- Fix a spanning tree `T` of `B` and orient each edge. Assign voltages in
  `A = H_1(B; Z/2)`:
  - `omega(e) = 0` for `e ∈ T`;
  - `omega(e) = [c_e]` for `e ∉ T`, where `c_e` is the fundamental cycle of `e` with respect to
    `T`.
- The classes `[c_e]`, `e ∉ T`, form a basis of `H_1(B; Z/2) ≅ (Z/2)^(b_1)`. So `omega` is
  `T`-reduced and its values generate `A`.
- The derived graph `B^` has vertex set `A × V(B)`. Each edge `e = (u -> v)` of `B` lifts to the
  `|A|` edges `((g, u), (g + omega(e), v))`, `g ∈ A`.
- The derived graph of a `T`-reduced voltage assignment in `A` is the regular cover with deck
  group `A` that corresponds to the kernel of the induced map `pi_1(B) -> A` (Gross--Tucker,
  *Topological Graph Theory*, Section 2.5). Here that map is the Hurewicz map mod 2, so `B^` is
  the Z/2-homology cover.
- `B^` is connected because the voltages generate `A`. It is `D`-regular and simplicial, since it
  covers a simplicial `D`-regular graph.

**2. The test function.**
- Since `b_1 >= 1`, there is a non-tree edge `e_0`. Let `chi : A -> {±1}` be the character with
  `chi([c_(e_0)]) = -1` and `chi([c_e]) = +1` for the other non-tree edges `e`. Tree edges have
  voltage `0`. So `chi(omega(e)) = -1` exactly when `e = e_0`.
- Define `F(g, v) = chi(g)` on `A × V(B)`.
  - `F` is orthogonal to the constants: `sum_(g,v) chi(g) = n · sum_(g ∈ A) chi(g) = 0`, since
    `chi` is nontrivial.
  - `||F||^2 = |A| · n`.
- For the Laplacian of a simplicial graph, `<F, L F> = sum_(edges xy) (F(x) - F(y))^2`. A lift
  `((g, u), (g + omega(e), v))` of `e` contributes

  ```text
  (chi(g) - chi(g) chi(omega(e)))^2  =  (1 - chi(omega(e)))^2,
  ```

  which is `4` if `e = e_0` and `0` otherwise. There are `|A|` lifts of `e_0`, so
  `<F, L F> = 4 |A|`.
- By the min-max principle,
  `lambda_1(B^) <= <F, L F> / ||F||^2 = 4 |A| / (|A| n) = 4 / n`.

**3. Cheeger.**
- For a `D`-regular graph, the discrete Cheeger inequality (Dodziuk; Alon--Milman) gives
  `h^2 / (2D) <= lambda_1`, with `h` the edge expansion.
- Hence `h(B^) <= sqrt(2 D lambda_1(B^)) <= sqrt(8 D / n)`.

**4. Application to the relators.** The following facts come from host item (4) of
`osajda-monster-hosts-for-bc-module-route` (Osajda, arXiv:1703.03791, Sections 3.1--3.3, read from
the PDF).
- The relators are `Theta^_1`, the Z/2-homology cover of `Theta_1`, and `Theta^_(i+1)`, the
  Z/2-homology cover of a finite normal cover `Theta-bar_(i+1)` of `Theta_(i+1)`.
- `(Theta_i)` is a sequence of `D`-regular graphs, `D >= 3`, taken from [Osa14]. Those graphs have
  growing girth (Osajda, arXiv:1406.5015, Introduction p. 2).
- `Cay(G, S)` contains isometric copies of every `Theta^_i`.

Put `B_1 = Theta_1` and `B_(i+1) = Theta-bar_(i+1)`.
- Each `B_i` is connected, simplicial and `D`-regular with `D >= 3`. It has `D n_i / 2` edges,
  more than `n_i - 1`, so `b_1(B_i) >= 1`.
- A covering map sends a cycle to a closed non-backtracking walk, which contains a cycle of no
  greater length. So `girth(B_i) >= girth(Theta_i)`.
- A cycle of length `girth(B_i)` has that many distinct vertices, so
  `n_i >= girth(Theta_i) -> infinity`.
- By step 2, `lambda_1(Theta^_i) <= 4 / n_i -> 0`.
- So `(Theta^_i)` is not an expander family: `inf_i lambda_1 = 0`, and equivalently
  `inf_i h = 0`.

**5. Scope of the consequence.**
- The Main Theorem of arXiv:1703.03791 gets non-exactness from girth through Willett (J. Topol.
  Anal. 3 (2011)), with no spectral gap.
- The coefficient failures of Higson--Lafforgue--Skandalis, Willett--Yu I and Finn-Sell
  (arXiv:1401.6841, Definition 3.5 and Theorem 3.7) all start from an embedded expander.
- None of these results applies to the relator family, so none gives these groups a failure of
  Baum--Connes with coefficients.
- This is an absence statement bounded to those four sources.
- The argument does not exclude other expanders in `Cay(G, S)`. It only shows that the
  construction does not supply one.
