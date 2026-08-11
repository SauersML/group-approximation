"""Find a finite quotient separating C11 from four stubborn zero classes.

Run with SageMath.  The ambient group is the free product of two copies of
S4, with chart presentations <s_j,t_j | s_j^2,t_j^3,(s_j t_j)^4>.  Exact
enumeration of admissible generator pairs avoids GAP's optional GQuotients
package and emits a directly checkable homomorphism certificate.
"""

import json

from sage.all import AlternatingGroup, DihedralGroup, PSL, SymmetricGroup


WORDS = {
    "zero_70": [
        ("s2", 1), ("t1", 2), ("s1", 1), ("t1", 1), ("s1", 1),
        ("s2", 1), ("s1", 1), ("s2", 1), ("t1", 2), ("s1", 1),
        ("t1", 1),
    ],
    "zero_90": [
        ("t2", 2), ("s2", 1), ("t2", 1), ("s1", 1), ("t1", 2),
        ("s1", 1), ("t1", 1), ("s1", 1), ("s2", 1), ("t2", 2),
        ("s2", 1), ("t2", 1), ("s2", 1), ("s1", 1), ("t1", 2),
        ("s1", 1), ("t1", 1), ("s1", 1), ("t2", 2), ("s2", 1),
        ("t2", 1), ("s2", 1), ("s1", 1), ("t1", 2), ("s1", 1),
        ("t1", 1), ("s1", 1),
    ],
    "zero_91": [
        ("t2", 2), ("s2", 1), ("t2", 1), ("s2", 1), ("s1", 1),
        ("t1", 2), ("s1", 1), ("t1", 1), ("s1", 1), ("t2", 2),
        ("s2", 1), ("t2", 1), ("s2", 1), ("s1", 1), ("t1", 2),
        ("s1", 1), ("t1", 1), ("s1", 1), ("t2", 2), ("s2", 1),
        ("t2", 1), ("s2", 1), ("s1", 1), ("t1", 2), ("s1", 1),
        ("t1", 1), ("s1", 1),
    ],
    "zero_86": [
        ("s1", 1), ("s2", 1), ("s1", 1), ("t1", 2), ("s1", 1),
        ("t1", 1), ("s2", 1), ("s1", 1), ("t1", 2), ("s1", 1),
        ("t1", 1), ("s2", 1), ("t1", 2), ("s1", 1), ("t1", 1),
        ("s1", 1),
    ],
    "phase_11": [
        ("t2", 1), ("s2", 1), ("t2", 2), ("s2", 1), ("t2", 1),
        ("t1", 1), ("s1", 1), ("t1", 2), ("s1", 1), ("t1", 1),
        ("s2", 1), ("t1", 1), ("s1", 1), ("t1", 2), ("s1", 1),
        ("t1", 1), ("t2", 1), ("s2", 1), ("t2", 2), ("s2", 1),
        ("t2", 1), ("t1", 1), ("s1", 1), ("t1", 2), ("s1", 1),
        ("t1", 1), ("s2", 1), ("t1", 2), ("s1", 1),
    ],
}


def evaluate(word, images, identity):
    value = identity
    for generator, exponent in word:
        value *= images[generator] ** exponent
    return value


def chart_pairs(group):
    identity = group.one()
    elements = list(group)
    return [
        (s, t)
        for s in elements
        for t in elements
        if s ** 2 == identity
        and t ** 3 == identity
        and (s * t) ** 4 == identity
    ]


def search_target(name, group):
    identity = group.one()
    pairs = chart_pairs(group)
    tested = 0
    zero_names = [name for name in WORDS if name.startswith("zero_")]
    for s1, t1 in pairs:
        for s2, t2 in pairs:
            tested += 1
            images = {"s1": s1, "t1": t1, "s2": s2, "t2": t2}
            if any(evaluate(WORDS[word], images, identity) != identity
                   for word in zero_names):
                continue
            phase = evaluate(WORDS["phase_11"], images, identity)
            if phase == identity:
                continue
            generated = group.subgroup(list(images.values()))
            return {
                "target": name,
                "target_order": int(group.order()),
                "chart_pairs": len(pairs),
                "pair_pairs_tested": tested,
                "images": {key: str(value) for key, value in images.items()},
                "generated_subgroup_order": int(generated.order()),
                "phase_image": str(phase),
                "phase_order": int(phase.order()),
                "zero_checks": {
                    word: evaluate(WORDS[word], images, identity) == identity
                    for word in zero_names
                },
            }
    return {
        "target": name,
        "target_order": int(group.order()),
        "chart_pairs": len(pairs),
        "pair_pairs_tested": tested,
        "separating_map": None,
    }


def main():
    targets = [
        ("S3", SymmetricGroup(3)),
        ("D8", DihedralGroup(4)),
        ("A4", AlternatingGroup(4)),
        ("S4", SymmetricGroup(4)),
        ("A5", AlternatingGroup(5)),
        ("S5", SymmetricGroup(5)),
        ("PSL(2,7)", PSL(2, 7)),
    ]
    results = []
    for name, group in targets:
        result = search_target(name, group)
        results.append(result)
        print(json.dumps(result), flush=True)
        if "phase_image" in result:
            break
    print(json.dumps({"results": results}, indent=2))


if __name__ == "__main__":
    main()
