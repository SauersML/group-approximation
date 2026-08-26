"""Audit the 31 root-free signed-Hecke classes against the middle Pauli menu.

Run on MSI only.  This is the exact F_2 index skeleton of the literal
middle-index packet.  The signed source L0 acts on (2,4,5,6,7,8,9), the
three dual Pauli translations are 3->7, 3->8, 3->9, and the two literal
Whiteheads induce the adjacent swaps of 7,8,9.  Their affine closure has
order 8*6=48.

For every positive L0 conjugacy class whose L0-normal closure contains no
internal root, the audit distinguishes:

* a menu word that preserves the signed source;
* a menu word that moves it to one of the explicitly named conjugate source
  types;
* a nonzero first commutator with a dual Pauli translation; and
* an actual elementary-root extraction after a second literal primal Pauli
  leg k->1.

The last test is intentionally stronger than mere noncommutation.  It is the
finite index condition needed by the two-spare-index saturation argument.
"""

from collections import Counter, deque

from signed_hecke_detector_normal_closure_audit import (
    conjugacy_class,
    generated_subgroup,
)
from signed_hecke_root_normalizer_audit import (
    COORDS as ACTOR_COORDS,
    GENERATORS as ACTOR_GENERATORS,
    IDENTITY as ACTOR_IDENTITY,
    multiply as actor_multiply,
    signed_l0,
    transvection as actor_transvection,
)


COORDS = (1, 2, 3, 4, 5, 6, 7, 8, 9)
INDEX = {coordinate: index for index, coordinate in enumerate(COORDS)}
IDENTITY = tuple(1 << index for index in range(len(COORDS)))
MIDDLE = (7, 8, 9)


def multiply(left, right):
    product = []
    for left_row in left:
        row = 0
        for index in range(len(COORDS)):
            if (left_row >> index) & 1:
                row ^= right[index]
        product.append(row)
    return tuple(product)


def inverse(matrix):
    left = list(matrix)
    right = list(IDENTITY)
    for column in range(len(COORDS)):
        pivot = next(row for row in range(column, len(COORDS))
                     if (left[row] >> column) & 1)
        left[column], left[pivot] = left[pivot], left[column]
        right[column], right[pivot] = right[pivot], right[column]
        for row in range(len(COORDS)):
            if row != column and ((left[row] >> column) & 1):
                left[row] ^= left[column]
                right[row] ^= right[column]
    assert tuple(left) == IDENTITY
    return tuple(right)


def transvection(source, target):
    matrix = list(IDENTITY)
    matrix[INDEX[target]] ^= 1 << INDEX[source]
    return tuple(matrix)


def embed_actor(matrix):
    embedded = list(IDENTITY)
    for actor_row, target in zip(matrix, ACTOR_COORDS):
        row = 0
        for actor_index, source in enumerate(ACTOR_COORDS):
            if (actor_row >> actor_index) & 1:
                row ^= 1 << INDEX[source]
        embedded[INDEX[target]] = row
    return tuple(embedded)


def restrict_actor(matrix):
    restricted = []
    actor_mask = sum(1 << INDEX[coordinate] for coordinate in ACTOR_COORDS)
    fixed_mask = sum(1 << INDEX[coordinate] for coordinate in (1, 3))
    for coordinate in (1, 3):
        assert matrix[INDEX[coordinate]] == 1 << INDEX[coordinate]
    for target in ACTOR_COORDS:
        assert matrix[INDEX[target]] & fixed_mask == 0
        row = 0
        for actor_index, source in enumerate(ACTOR_COORDS):
            if matrix[INDEX[target]] & (1 << INDEX[source]):
                row ^= 1 << actor_index
        restricted.append(row)
        assert matrix[INDEX[target]] & ~(actor_mask | fixed_mask) == 0
    return tuple(restricted)


def commutator(left, right):
    return multiply(multiply(multiply(left, right), inverse(left)), inverse(right))


def generated_group(generators):
    group = {IDENTITY}
    queue = deque((IDENTITY,))
    while queue:
        current = queue.popleft()
        for generator in generators:
            successor = multiply(current, generator)
            if successor not in group:
                group.add(successor)
                queue.append(successor)
    return frozenset(group)


def swap(first, second):
    # In characteristic two this is the literal three-transvection Weyl word.
    return multiply(
        multiply(transvection(first, second), transvection(second, first)),
        transvection(first, second),
    )


def is_transvection(matrix):
    difference = tuple(row ^ identity_row
                       for row, identity_row in zip(matrix, IDENTITY))
    nonzero_rows = [row for row in difference if row]
    return len(nonzero_rows) == 1 and nonzero_rows[0].bit_count() == 1


def source_signature(conjugator, character):
    conjugator_inverse = inverse(conjugator)
    return frozenset(
        (multiply(multiply(conjugator, embed_actor(element)), conjugator_inverse), sign)
        for element, sign in character.items()
    )


def preserves_signed_source(conjugator, character):
    conjugator_inverse = inverse(conjugator)
    for index, generator in enumerate(ACTOR_GENERATORS):
        conjugate = multiply(
            multiply(conjugator, embed_actor(generator)), conjugator_inverse
        )
        try:
            restricted = restrict_actor(conjugate)
        except AssertionError:
            return False
        if restricted not in character or character[restricted] != (index < 3):
            return False
    return True


def missed_classes(character):
    internal_roots = {
        actor_transvection(source, target)
        for source in ACTOR_COORDS
        for target in ACTOR_COORDS
        if source != target and actor_transvection(source, target) in character
    }
    unseen = {element for element, sign in character.items() if sign == 0}
    unseen.remove(ACTOR_IDENTITY)
    missed = []
    while unseen:
        representative = next(iter(unseen))
        conjugates = conjugacy_class(representative)
        unseen.difference_update(conjugates)
        closure, root_length = generated_subgroup(conjugates, internal_roots)
        if root_length is None:
            missed.append((representative, conjugates, closure))
    assert len(missed) == 31
    return missed


def main():
    character = signed_l0()
    classes = missed_classes(character)

    y = {middle: transvection(3, middle) for middle in MIDDLE}
    x = {middle: transvection(middle, 1) for middle in MIDDLE}
    w1 = swap(7, 8)
    w2 = swap(8, 9)
    s3 = generated_group((w1, w2))
    translations = generated_group((y[7], y[8], y[9]))
    menu_labels = {}
    for permutation in s3:
        for translation in translations:
            word = multiply(permutation, translation)
            translation_mask = tuple(
                middle for middle in MIDDLE
                if translation != multiply(translation, y[middle])
                and any(
                    translation[INDEX[target]]
                    & (1 << INDEX[3])
                    for target in (middle,)
                )
            )
            menu_labels[word] = (permutation, translation_mask)
    menu = frozenset(menu_labels)
    assert len(menu) == 48

    preserving = frozenset(word for word in menu
                           if preserves_signed_source(word, character))
    source_types = {source_signature(word, character) for word in menu}

    # Coverage is classwise: conjugating a detector by L0 costs only a typed
    # source-preserving occurrence, so every representative in the L0 class
    # is available before applying one external menu probe.
    class_rows = []
    uncovered_translation = []
    uncovered_double = []
    uncovered_menu = []
    uncovered_menu_double = []
    uncovered_two_menu = []
    uncovered_preserving = []
    uncovered_preserving_two_menu = []
    for representative, conjugates, closure in classes:
        embedded_conjugates = tuple(embed_actor(element) for element in conjugates)

        translation_hits = []
        double_hits = []
        for element in embedded_conjugates:
            for middle_y, probe_y in y.items():
                first = commutator(element, probe_y)
                if first != IDENTITY:
                    translation_hits.append((middle_y, is_transvection(first)))
                for middle_x, probe_x in x.items():
                    extracted = commutator(probe_x, first)
                    if is_transvection(extracted):
                        double_hits.append((middle_y, middle_x))

        menu_hits = []
        menu_double_hits = []
        two_menu_hits = []
        preserving_hits = []
        preserving_two_menu_hits = []
        for element in embedded_conjugates:
            for word in menu:
                first = commutator(element, word)
                if first != IDENTITY:
                    menu_hits.append(word)
                    if word in preserving:
                        preserving_hits.append(word)
                for middle_x, probe_x in x.items():
                    extracted = commutator(probe_x, first)
                    if is_transvection(extracted):
                        menu_double_hits.append((word, middle_x))
                for second_word in menu:
                    extracted = commutator(first, second_word)
                    if is_transvection(extracted):
                        two_menu_hits.append((word, second_word))
                        if word in preserving and second_word in preserving:
                            preserving_two_menu_hits.append((word, second_word))

        if not translation_hits:
            uncovered_translation.append(representative)
        if not double_hits:
            uncovered_double.append(representative)
        if not menu_hits:
            uncovered_menu.append(representative)
        if not menu_double_hits:
            uncovered_menu_double.append(representative)
        if not two_menu_hits:
            uncovered_two_menu.append(representative)
        if not preserving_hits:
            uncovered_preserving.append(representative)
        if not preserving_two_menu_hits:
            uncovered_preserving_two_menu.append(representative)

        class_rows.append({
            "class_size": len(conjugates),
            "closure_size": len(closure),
            "translation": bool(translation_hits),
            "translation_single_root": any(single for _, single in translation_hits),
            "literal_double_root": bool(double_hits),
            "menu": bool(menu_hits),
            "menu_double_root": bool(menu_double_hits),
            "two_menu_root": bool(two_menu_hits),
            "preserving": bool(preserving_hits),
            "preserving_two_menu_root": bool(preserving_two_menu_hits),
        })

    profile = Counter(
        (
            row["class_size"],
            row["closure_size"],
            row["translation"],
            row["translation_single_root"],
            row["literal_double_root"],
            row["menu"],
            row["menu_double_root"],
            row["two_menu_root"],
            row["preserving"],
            row["preserving_two_menu_root"],
        )
        for row in class_rows
    )

    print("|middle affine Pauli menu| =", len(menu))
    print("menu words preserving (L0,lambda0) =", len(preserving))
    print("preserving menu matrices =", sorted(preserving))
    print("distinct explicitly transported signed-source types =", len(source_types))
    print("missed positive detector classes =", len(classes))
    print("coverage profile:")
    for key, count in sorted(profile.items()):
        print(" ", key, ":", count)
    print("classes missed by the 8 translations at first commutator =",
          len(uncovered_translation))
    print("classes missed by literal Y-then-X root extraction =",
          len(uncovered_double))
    print("classes commuting with the full 48-word menu =", len(uncovered_menu))
    print("classes missed by menu-then-X root extraction =",
          len(uncovered_menu_double))
    print("classes missed by two-probe 48-menu root extraction =",
          len(uncovered_two_menu))
    print("classes commuting with every source-preserving menu probe =",
          len(uncovered_preserving))
    print("classes missed by two source-preserving menu probes =",
          len(uncovered_preserving_two_menu))

    # Exact matrices of an uncovered representative are useful as a compact
    # obstruction certificate without depending on set iteration order.
    for label, uncovered in (
        ("translation fence", uncovered_translation),
        ("literal double fence", uncovered_double),
        ("full-menu fence", uncovered_menu),
        ("menu-double fence", uncovered_menu_double),
        ("two-menu fence", uncovered_two_menu),
        ("preserving fence", uncovered_preserving),
        ("preserving-two-menu fence", uncovered_preserving_two_menu),
    ):
        encoded = sorted(tuple(matrix) for matrix in uncovered)
        print(label, "representatives =", encoded)


if __name__ == "__main__":
    main()
