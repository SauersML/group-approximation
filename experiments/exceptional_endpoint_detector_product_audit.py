"""Close the three exceptional endpoint detectors under L0 conjugacy/products."""

from collections import deque

from experiments.signed_hecke_root_normalizer_audit import (
    GENERATORS,
    IDENTITY,
    INDEX,
    multiply,
    signed_l0,
)


REPRESENTATIVES = (
    (65, 74, 4, 8, 16, 32, 64),
    (73, 2, 4, 8, 16, 32, 64),
    (73, 74, 4, 8, 16, 32, 64),
)


def conjugacy_class(representative: tuple[int, ...]) -> set[tuple[int, ...]]:
    result = {representative}
    queue = deque((representative,))
    while queue:
        current = queue.popleft()
        for generator in GENERATORS:
            # Every displayed L0 generator is a transvection and an involution.
            conjugate = multiply(multiply(generator, current), generator)
            if conjugate not in result:
                result.add(conjugate)
                queue.append(conjugate)
    return result


def generated_subgroup(generators: set[tuple[int, ...]]) -> set[tuple[int, ...]]:
    result = {IDENTITY}
    queue = deque((IDENTITY,))
    while queue:
        current = queue.popleft()
        for generator in generators:
            product = multiply(current, generator)
            if product not in result:
                result.add(product)
                queue.append(product)
    return result


def endpoint_hits(matrix: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    return tuple(
        (depth, endpoint)
        for depth, middle in enumerate((7, 8, 9), start=1)
        for endpoint in (2, 4)
        if (matrix[INDEX[endpoint]] >> INDEX[middle]) & 1
    )


def main() -> None:
    signed = signed_l0()
    classes = tuple(conjugacy_class(representative) for representative in REPRESENTATIVES)
    assert tuple(map(len, classes)) == (2, 1, 2)

    normal_closure = generated_subgroup(set().union(*classes))
    assert len(normal_closure) == 8
    assert all(signed[element] == 0 for element in normal_closure)

    expected_hit_profiles = {
        (),
        ((3, 2),),
        ((3, 4),),
        ((3, 2), (3, 4)),
    }
    profiles = {endpoint_hits(element) for element in normal_closure}
    assert profiles == expected_hit_profiles
    assert all(
        not ({1, 2} <= {depth for depth, _endpoint in profile})
        and not ({2, 3} <= {depth for depth, _endpoint in profile})
        for profile in profiles
    )

    print("exceptional conjugacy-class sizes =", tuple(map(len, classes)))
    print("positive normal closure size =", len(normal_closure))
    print("endpoint depth profiles =", sorted(profiles, key=lambda value: (len(value), value)))
    print("adjacent endpoint-depth profile = none")


if __name__ == "__main__":
    main()
