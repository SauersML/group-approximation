"""Defect-anchored lifts of s0 and t0, searched by collision depth.

Structural input: `leavitt-unit-group-carries-nontrivial-rigid-defect`.  Over
R = L_(F_2)(1,2) take the nine-leaf blocks of
`openai-nine-leaf-leavitt-configuration`, the compressor u, an element j of
J = V_(1000), an elementary matrix gamma of Gamma = EL_alpha(R), x = u j u^-1
(which lies in V_(0001) <= Gamma) and the defect c = [x, gamma] != 1.

A per-factor rigidity argument (`linear-sofic-group-algebra-is-stably-finite`)
forces each factor of a strict pair to have non-F_2-linear-sofic support, and
the only known mechanism against linear soficity here is this defect.  So the
candidate lift puts D = {u, j, x, gamma, c} in its support and completes the
evaluation to s0 (or t0) with an even correction K from the atlas ball.  The
partner of the resulting lift is then searched exhaustively by collision depth
(`left-partners-lie-in-collision-universes`).  A miss is a bounded fence.
"""

import argparse
import json
import time

from depth_one_paired_leavitt_return_search import ONE, canonical, multiply, add, equal
from kaplansky_asymmetric_atlas_search import S0, cayley_ball, evaluate_sum, key, from_key
from kaplansky_affine_lift_search import affine_leavitt_solutions
from kaplansky_joint_lift_search import descend
import kaplansky_collision_partner_search as cps

T0 = canonical((("", "0"),))
ALPHA, BETA, NU, ZETA = ("000", "001", "01"), ("1000", "1001", "101"), ("1100", "1101", "111"), ("100", "101", "11")


def unit(monomials):
    return canonical(tuple(monomials))


def prefix_map(dom, cod):
    """The element of V sending the cylinder of dom_i onto that of cod_i."""
    return unit((c, d) for d, c in zip(dom, cod))


def mul(*factors):
    value = ONE
    for f in factors:
        value = multiply(value, f)
    return value


def defect_configuration():
    dom = ALPHA + BETA + NU
    cod = tuple(a + "0" for a in ALPHA) + tuple(a + "1" for a in ALPHA) + ZETA
    u, u_inv = prefix_map(dom, cod), prefix_map(cod, dom)
    assert key(mul(u, u_inv)) == key(ONE)
    j = unit((("", ""), ("1000", "1000"), ("10000", "10001"), ("10001", "10000")))
    assert key(mul(j, j)) == key(ONE)
    x = mul(u, j, u_inv)
    candidates = [(i, k, rm, rn) for i in range(3) for k in range(3) if i != k
                  for rm, rn in (("", ""), ("0", ""), ("", "0"))]
    for i, k, rm, rn in candidates:
        gamma = unit((("", ""), (ALPHA[i] + rm, ALPHA[k] + rn)))
        assert key(mul(gamma, gamma)) == key(ONE)
        c = mul(x, gamma, x, gamma)
        if key(c) != key(ONE):
            c_inv = mul(gamma, x, gamma, x)
            elements = [("u", u, u_inv), ("j", j, j), ("x", x, x),
                        (f"gamma{i}{k}{rm}{rn}", gamma, gamma), ("c", c, c_inv)]
            assert len({key(e) for _, e, _ in elements}) == 5
            return elements
    raise AssertionError("no nontrivial defect commutator among the elementary candidates")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", choices=("s0", "t0"), required=True)
    parser.add_argument("--correction-radius", type=int, default=3)
    parser.add_argument("--pool-radius", type=int, default=2)
    parser.add_argument("--depth", type=int, default=1)
    parser.add_argument("--max-support", type=int, default=41)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    start = time.time()
    one = key(ONE)
    defect = defect_configuration()
    target_value = S0 if args.target == "s0" else T0
    side = "left" if args.target == "s0" else "right"
    generators, ball, words = cayley_ball(args.correction_radius)
    gens = tuple(key(g) for _, g in generators)
    # Atlas balls alone never reach the deep monomials of D (radii 3-5 were
    # infeasible), so the correction pool also contains d*g and g*d for d in D
    # and g in a small atlas ball.
    pool = {}
    for i, g in enumerate(ball):
        w = tuple(words[i])
        pool.setdefault(key(g), (g, w, cps.word_key(tuple(reversed(w)), gens, one)))
    _, small_ball, small_words = cayley_ball(args.pool_radius)
    for name, d, d_inv in defect:
        for i, g in enumerate(small_ball):
            w = tuple(small_words[i])
            g_inv = cps.word_key(tuple(reversed(w)), gens, one)
            left, right = mul(d, g), mul(g, d)
            pool.setdefault(key(left), (left, (name,) + w, cps.product_key(g_inv, key(d_inv))))
            pool.setdefault(key(right), (right, w + (name,), cps.product_key(key(d_inv), g_inv)))
    pool_items = list(pool.values())
    residual = add(target_value, evaluate_sum([e for _, e, _ in defect]))
    particular, dependencies = affine_leavitt_solutions([v for v, _, _ in pool_items], residual, parity=0)
    record = {"target": args.target, "side": side, "defect_labels": [n for n, _, _ in defect],
              "correction_radius": args.correction_radius, "pool_radius": args.pool_radius,
              "pool_size": len(pool_items), "depth": args.depth}
    if particular is None:
        record["status"] = "NO_EVEN_CORRECTION_IN_POOL"
    else:
        best = descend(particular, dependencies)
        chosen = [i for i in range(len(pool_items)) if (best >> i) & 1]
        support = {}
        for name, value, inverse in defect:
            support[key(value)] = ((name,), key(inverse))
        for i in chosen:
            value, w, inv = pool_items[i]
            k = key(value)
            if k in support:
                del support[k]
            else:
                support[k] = (w, inv)
        for k, (_, inv) in support.items():
            assert cps.product_key(k, inv) == one
        fixed_keys = list(support)
        assert len(fixed_keys) % 2 == 1
        assert equal(evaluate_sum([from_key(k) for k in fixed_keys]), target_value)
        record.update({"correction_support": len(chosen), "lift_support": len(fixed_keys)})
        if len(fixed_keys) > args.max_support:
            record["status"] = "LIFT_TOO_LARGE"
        else:
            roots = [(inv, w) for w, inv in support.values()]
            if side == "left":
                steps = {cps.product_key(a, support[b][1]): support[a][0] + support[b][0]
                         for a in fixed_keys for b in fixed_keys}
            else:
                steps = {cps.product_key(support[a][1], b): support[a][0] + support[b][0]
                         for a in fixed_keys for b in fixed_keys}
            universe_words, sizes = cps.universe(roots, list(steps.items()), args.depth, side)
            universe_keys = list(universe_words)
            cols = cps.columns(universe_keys, fixed_keys, side)
            live = cps.peel(cols, cps.digest(one))
            chosen_cols, n_rows, rank = cps.solve(cols, live, cps.digest(one))
            record.update({"universe_sizes": sizes, "live_after_peel": len(live),
                           "rows_live": n_rows, "rank_live": rank,
                           "status": "NO_PARTNER_IN_UNIVERSE" if chosen_cols is None else "CANDIDATE_HIT_RECHECK"})
            if chosen_cols is not None:
                record["partner_words"] = [universe_words[universe_keys[c]] for c in chosen_cols]
    record["seconds_total"] = round(time.time() - start, 1)
    with open(args.out, "w") as handle:
        json.dump(record, handle, indent=1)
    print(json.dumps({k: v for k, v in record.items() if k != "partner_words"}))


if __name__ == "__main__":
    main()
