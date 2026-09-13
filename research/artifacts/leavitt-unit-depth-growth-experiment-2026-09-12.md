# Depth growth of powers of binary Leavitt units: a numerical screen

Lane `ex-q34-leavitt-hs`, 2026-09-12. This is an exact-arithmetic screen, not a proof.
It supports the undistortion strategy recorded on
`leavitt-unit-group-has-no-integer-heisenberg-subgroup`.

## 1. Quantity measured

`R = L_(F_2)(1,2)`. For `x` in `R` put

```text
ell(x) = max over normal-form monomials S[alpha]T[beta] of x of max(|alpha|, |beta|).
```

The Diamond-lemma rewriting of `experiments/nonsofic-certificates/leavitt.py`
(`t_i s_j -> delta_ij`, `s_1 t_1 -> 1 + s_0 t_0`) never lengthens a monomial.
So `ell(x)` equals the least `N` with `x` in
`R_N = span{ S[alpha]T[beta] : |alpha|, |beta| <= N }`, and
`R_N R_M <= R_(N+M)`.

For a unit `u` the screen records `D(m) = max(ell(u^m), ell(u^-m))` for
`m = 1..24`. A Heisenberg center `c = [a,b]` would satisfy
`D_c(m^2) <= m (ell(a) + ell(b) + ell(a^-1) + ell(b^-1))`, so its depth growth is
sublinear. The screen asks whether sublinear growth ever occurs for a unit of
infinite order.

## 2. Generators and sampling

Seven generators and their inverses:

| name | unit |
| --- | --- |
| `A` | Thompson unit `0,10,11 -> 00,01,1` |
| `B` | Thompson unit `0,10,110,111 -> 0,100,101,11` |
| `C` | Thompson unit `0,10,11 -> 11,0,10` |
| `P` | Thompson unit `0,10,11 -> 10,0,11` |
| `X` | `1 + S[0]T[10]` (a transvection of degree -1) |
| `Y` | `1 + S[10]T[0]` (a transvection of degree +1) |
| `Z` | `1 + S[0]T[1]` (a degree-0 transvection) |

Uppercase letters are the units and lowercase letters their inverses. Words of
length 2 to 8 were drawn uniformly, with seeds `1,2,3` and 250 draws each; repeated
units were skipped. Powers were computed exactly in normal form, with dual-path
checking off. A run stopped when a power exceeded `1500` monomials. Script:
`/projects/standard/hsiehph/sauer354/ex/ex-q34-leavitt-hs/depth_growth.py` on MSI.
Its full text is reproduced in Section 4. All three runs finished in about 2 seconds.

## 3. Results

- **Finite order detected (`u^m = 1` with `m <= 24`):** 123 units. Their orders
  were `1` (3 units), `2` (30), `3` (20), `4` (28), `5` (6), `6` (14), `7` (20)
  and `9` (2).
- **No identity up to `m = 24`:** 546 units.
  - For 356 units at least 8 powers stayed under the monomial cap. Their late
    slope `(D(24) - D(12))/12` took the values
    `0` (4 units), `1/4`, `3/11`, `1/3`, `1/2` (2 units), `1` (236), `2` (93),
    `3` (16) and `4` (2).
  - The other 190 hit the monomial cap within 7 powers. Every one of them had
    strictly increasing depths with steps of 1 to 4 per power, for example
    `[5,7,9,11,13]` and `[6,10,14,18]`.
- **The four slope-0 units** `YaBCA`, `BPXBpcb`, `CAXb` and `BBbCY` have bounded
  depth. A separate exact check found that each has order exactly `31`. This is
  consistent with the fact that a bounded-depth unit has finite order, because
  each `R_N` is finite.
- **Slow but linear growth.** The units with slope below 1 grow by one depth
  unit every 2, 3 or 4 powers, for example `APbacA` with depths
  `5,5,5,6,6,6,7,...,12` and `BACbAaA` with `4,5,5,5,5,6,...,10`. The check
  found no identity up to `m = 2048` for `APbacA` and `bAC`.

**Reading.** Among about 550 sampled units that are either of infinite order or of
order above 24, none shows sublinear depth growth apart from bounded-depth units of
finite order. The observed slopes are small rationals, and they behave like
translation lengths. This is evidence, not a proof. Words with at most 8 letters
explore short units only, and the monomial cap hides the long-run behaviour of the
most linear units.

## 4. Script

```python
import random, sys, time
sys.path.insert(0, "/projects/standard/hsiehph/sauer354/nonsofic-certificates/current/"
                   "experiments/nonsofic-certificates")
import leavitt as L
L.set_dual(False)

def depth(e):
    return max((max(len(a), len(b)) for a, b in e.terms), default=0)

def gens():
    g = {}
    g["A"] = L.thompson_unit(["0", "10", "11"], ["00", "01", "1"])
    g["B"] = L.thompson_unit(["0", "10", "110", "111"], ["0", "100", "101", "11"])
    g["C"] = L.thompson_unit(["0", "10", "11"], ["11", "0", "10"])
    g["P"] = L.thompson_unit(["0", "10", "11"], ["10", "0", "11"])
    g["X"] = L.one_plus_nilpotent(L.parse_elem("S[0]T[10]"))
    g["Y"] = L.one_plus_nilpotent(L.parse_elem("S[10]T[0]"))
    g["Z"] = L.one_plus_nilpotent(L.parse_elem("S[0]T[1]"))
    out = {}
    for k, u in g.items():
        out[k] = (u.val, u.inv)
        out[k.lower()] = (u.inv, u.val)
    return out

def word_unit(word, G):
    val, inv = L.ONE, L.ONE
    for ch in word:
        gv, gi = G[ch]
        val = val * gv
        inv = gi * inv
    assert (val * inv).is_one()
    return val, inv

def profile(val, inv, M, cap):
    pv, pi = L.ONE, L.ONE
    prof = []
    for m in range(1, M + 1):
        pv = pv * val
        pi = pi * inv
        if pv.is_one():
            return m, prof, len(pv)
        if len(pv) > cap or len(pi) > cap:
            return None, prof, -len(pv)
        prof.append(max(depth(pv), depth(pi)))
    return None, prof, len(pv)
```

The driver loop draws a word, skips repeats, calls `profile(val, inv, 24, 1500)` and
prints the order or the depth list with the late slope. The order check multiplies
up to `m = 2048`.
