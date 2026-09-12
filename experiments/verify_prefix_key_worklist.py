"""MSI-only comparison against the original exact prefix reducer."""
import hashlib
import json
from pathlib import Path
import random
import sys
import time

sys.path.insert(0, sys.argv[1])
import kaplansky_asymmetric_atlas_search as search
from depth_one_paired_leavitt_return_search import canonical, binary_words, equal, multiply


def reference(canonical_terms):
    terms = set(canonical_terms)
    changed = True
    while changed:
        changed = False
        parents = {}
        for mu, nu in terms:
            if mu and nu and mu[-1] == nu[-1]:
                parents.setdefault((mu[:-1], nu[:-1]), set()).add(mu[-1])
        for parent, bits in sorted(parents.items()):
            if bits == {"0", "1"}:
                child0 = (parent[0] + "0", parent[1] + "0")
                child1 = (parent[0] + "1", parent[1] + "1")
                if child0 in terms and child1 in terms:
                    terms.remove(child0)
                    terms.remove(child1)
                    if parent in terms:
                        terms.remove(parent)
                    else:
                        terms.add(parent)
                    changed = True
                    break
    return tuple(sorted(terms))


started = time.monotonic()
cases = []
for depth in range(10):
    cases.append(tuple((w, w) for w in binary_words(depth)))
rng = random.Random(20260908)
words = [w for depth in range(6) for w in binary_words(depth)]
for _ in range(128):
    cases.append(tuple(sorted(canonical(
        (rng.choice(words), rng.choice(words)) for _ in range(rng.randrange(1, 49))
    ))))
generators = [value for _, value in search.atlas_generators()]
for left in generators:
    for right in generators:
        cases.append(tuple(sorted(multiply(left, right))))
_, ball, _ = search.cayley_ball(2)
cases.extend(tuple(sorted(canonical(value))) for value in ball)

slow_seconds = fast_seconds = 0.0
for value in cases:
    before = time.monotonic()
    expected = reference(value)
    slow_seconds += time.monotonic() - before
    search._reduced_key.cache_clear()
    before = time.monotonic()
    actual = search._reduced_key(value)
    fast_seconds += time.monotonic() - before
    assert actual == expected
    assert equal(actual, value)

print(json.dumps({
    "status": "all_exact_comparisons_passed",
    "cases": len(cases),
    "reference_seconds": slow_seconds,
    "worklist_seconds": fast_seconds,
    "reduction_speedup": slow_seconds / fast_seconds,
    "elapsed_seconds": time.monotonic() - started,
    "source_sha256": hashlib.sha256(Path(search.__file__).read_bytes()).hexdigest(),
    "scope": "Exact old/new key comparisons on expanded identities, deterministic mixed-prefix sums, all 144 atlas-generator products, and all 109 radius-two elements; no conjecture resolution",
}, indent=2))
