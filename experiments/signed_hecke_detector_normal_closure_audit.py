"""Audit normal saturation of all signed-Hecke Reynolds detector words.

Run through the MSI wrapper only.  This imports the already certified
8,192-element binary matrix model of the actual signed source group L0.
For each conjugacy class in ker(lambda_0), it computes the normal closure in
L0 and checks whether that closure contains an internal root transvection.
"""

from collections import Counter, deque

from signed_hecke_root_normalizer_audit import (
    COORDS,
    GENERATORS,
    IDENTITY,
    multiply,
    signed_l0,
    transvection,
)


def generated_subgroup(generators, targets):
    subgroup = {IDENTITY}
    distance = {IDENTITY: 0}
    queue = deque((IDENTITY,))
    while queue:
        current = queue.popleft()
        for generator in generators:
            successor = multiply(current, generator)
            if successor not in subgroup:
                subgroup.add(successor)
                distance[successor] = distance[current] + 1
                queue.append(successor)
    target_lengths = [distance[target] for target in subgroup & targets]
    return frozenset(subgroup), min(target_lengths) if target_lengths else None


def conjugacy_class(seed):
    orbit = {seed}
    queue = deque((seed,))
    while queue:
        current = queue.popleft()
        for generator in GENERATORS:
            successor = multiply(multiply(generator, current), generator)
            if successor not in orbit:
                orbit.add(successor)
                queue.append(successor)
    return frozenset(orbit)


def main():
    character = signed_l0()
    assert len(character) == 8192
    assert Counter(character.values()) == Counter({0: 4096, 1: 4096})

    internal_roots = {
        transvection(source, target)
        for source in COORDS
        for target in COORDS
        if source != target and transvection(source, target) in character
    }
    assert len(internal_roots) == 13
    assert set(GENERATORS) <= internal_roots

    unseen = {element for element, sign in character.items() if sign == 0}
    unseen.remove(IDENTITY)
    class_count = 0
    class_sizes = Counter()
    closure_sizes = Counter()
    root_lengths = Counter()
    missed_classes = []

    while unseen:
        representative = next(iter(unseen))
        conjugates = conjugacy_class(representative)
        assert all(character[element] == 0 for element in conjugates)
        unseen.difference_update(conjugates)
        class_count += 1
        class_sizes[len(conjugates)] += 1

        closure = generated_subgroup(conjugates, internal_roots)
        closure_group, root_length = closure
        closure_sizes[len(closure_group)] += 1
        if root_length is None:
            missed_classes.append((representative, len(conjugates), len(closure_group)))
        else:
            root_lengths[root_length] += 1

    # This deliberately fences the tempting internal-L0 saturation route.
    # The full Steinberg proof needs two roots through spare ambient indices.
    assert len(missed_classes) == 31, missed_classes
    assert sum(size * multiplicity for size, multiplicity in class_sizes.items()) == 4095
    assert class_count == 511
    assert class_sizes == Counter({16: 192, 2: 152, 4: 128, 8: 24, 1: 15})
    assert closure_sizes == Counter({32: 192, 4: 152, 8: 128, 16: 24, 2: 15})
    assert root_lengths == Counter({2: 470, 1: 10})
    assert Counter(
        (class_size, closure_size)
        for _representative, class_size, closure_size in missed_classes
    ) == Counter({(2, 4): 16, (1, 2): 11, (4, 8): 4})
    print("|L0|=8192; |ker(lambda_0)|=4096")
    print("positive nonidentity conjugacy classes =", class_count)
    print("class-size distribution =", sorted(class_sizes.items()))
    print("normal-closure-size distribution =", sorted(closure_sizes.items()))
    print("shortest internal-root normal-word lengths =", sorted(root_lengths.items()))
    print("internal-root word bound on the 480 hit classes =", max(root_lengths))
    print("positive classes with no internal-root normal closure =", len(missed_classes))
    print("missed (class size, closure size) distribution =", sorted(Counter(
        (class_size, closure_size)
        for _representative, class_size, closure_size in missed_classes
    ).items()))
    print("every other positive class normally contains an internal root")
    print("all 4096 negative detectors contain z and admit the common spare-index probe")


if __name__ == "__main__":
    main()
