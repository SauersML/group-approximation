"""Generate proof-carrying P13 word reductions for the exact Hodge certificate.

The 3-by-3 matrix model is used *only* to discover which finite words should
be compared.  Every exported equality is independently certified as a product
of conjugates of the thirteen abstract P13 relators.  The corresponding Lean
verifier checks that product in the free group, so neither this program nor
matrix equality is in the trusted proof base.

The completion is deliberately bounded.  It maintains shortlex-decreasing
rewrite rules and records a proof DAG for every critical-pair rule.  Once all
finite target equalities reduce to a common word, the DAGs are expanded to
literal conjugated-relator atoms and checked again by free reduction before
JSON export.
"""

import argparse
import collections
import itertools
import json
import time

import numpy as np


ROOTS = tuple((i, j) for i in range(3) for j in range(3) if i != j)
IDENTITY = (1, 0, 0, 0, 1, 0, 0, 0, 1)


def free_reduce(word):
    stack = []
    for letter in word:
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def inverse_word(word):
    return tuple(-letter for letter in reversed(word))


def multiply(left, right):
    return free_reduce(left + right)


def commutator(left, right):
    return multiply(multiply(multiply(left, right), inverse_word(left)),
                    inverse_word(right))


def matrix_multiply(left, right):
    return tuple(sum(left[3 * i + k] * right[3 * k + j]
                     for k in range(3))
                 for i in range(3) for j in range(3))


def matrix_inverse(matrix):
    a, b, c, d, e, f, g, h, i = matrix
    return (
        e * i - f * h, c * h - b * i, b * f - c * e,
        f * g - d * i, a * i - c * g, c * d - a * f,
        d * h - e * g, b * g - a * h, a * e - b * d,
    )


def generator_matrices():
    answer = []
    for row, column in ROOTS:
        matrix = list(IDENTITY)
        matrix[3 * row + column] = 1
        answer.append(tuple(matrix))
    return tuple(answer)


def word_matrix(word, generators):
    answer = IDENTITY
    for letter in word:
        generator = generators[abs(letter) - 1]
        answer = matrix_multiply(
            answer, generator if letter > 0 else matrix_inverse(generator))
    return answer


def presentation_relators():
    root_index = {root: index + 1 for index, root in enumerate(ROOTS)}
    relators = []
    for i, j, k in itertools.permutations(range(3)):
        relators.append(multiply(
            commutator((root_index[(i, j)],), (root_index[(j, k)],)),
            (-root_index[(i, k)],)))
    for first, second in itertools.combinations(ROOTS, 2):
        i, j = first
        k, ell = second
        if i != ell and j != k:
            relators.append(commutator(
                (root_index[first],), (root_index[second],)))
    block = (root_index[(0, 1)], -root_index[(1, 0)],
             root_index[(0, 1)])
    relators.append(free_reduce(block * 4))
    return tuple(relators)


def support_and_targets(certificate_path):
    """Recover the finite target list; matrices are discovery labels only."""
    archive = np.load(certificate_path)
    stored_support = [tuple(map(int, row))
                      for row in archive["group_support"]]
    generators = generator_matrices()
    relators = presentation_relators()
    if any(word_matrix(relator, generators) != IDENTITY
           for relator in relators):
        raise AssertionError("a literal P13 relator has the wrong matrix")

    candidates = {IDENTITY: [()]}
    for index, generator in enumerate(generators):
        candidates.setdefault(matrix_inverse(generator), []).append(
            (-(index + 1),))
    prefix_words = set([()])
    for relator in relators:
        prefix = ()
        for letter in relator:
            if letter > 0:
                edge_prefix = prefix
                prefix = multiply(prefix, (letter,))
            else:
                prefix = multiply(prefix, (letter,))
                edge_prefix = prefix
            prefix_words.add(edge_prefix)
            candidates.setdefault(
                word_matrix(edge_prefix, generators), []).append(edge_prefix)
        # `prefix` is a free word, so it is generally nonempty even though the
        # relator evaluates to the identity in the intended matrix model.
        if word_matrix(prefix, generators) != IDENTITY:
            raise AssertionError("a literal P13 relator did not close")

    if set(candidates) != set(stored_support):
        raise AssertionError("stored support differs from literal prefixes")
    support_words = tuple(
        min(set(candidates[matrix]), key=lambda word: (len(word), word))
        for matrix in stored_support)

    target_kinds = {}

    # Canonicalize all actual Fox prefixes and inverse-generator monomials to
    # the 22 certificate support words.
    for matrix, aliases in candidates.items():
        canonical = support_words[stored_support.index(matrix)]
        for alias in set(aliases):
            if alias != canonical:
                target_kinds[(alias, canonical)] = "prefix"

    # Canonicalize the 22-by-22 products used by V*Q^T QV.
    product_words = {}
    for left, left_word in enumerate(support_words):
        for right, right_word in enumerate(support_words):
            product = multiply(inverse_word(left_word), right_word)
            product_words[(left, right)] = product
    classes = {}
    for product in set(product_words.values()):
        classes.setdefault(word_matrix(product, generators), []).append(product)
    representatives = {
        matrix: min(words, key=lambda word: (len(word), word))
        for matrix, words in classes.items()
    }
    for product in set(product_words.values()):
        canonical = representatives[word_matrix(product, generators)]
        if product != canonical:
            target_kinds[(product, canonical)] = "product"

    class_matrices = sorted(representatives)
    class_index = {matrix: index for index, matrix in enumerate(class_matrices)}
    product_class_table = [
        [class_index[word_matrix(product_words[(left, right)], generators)]
         for right in range(len(support_words))]
        for left in range(len(support_words))
    ]
    class_words = [representatives[matrix] for matrix in class_matrices]
    targets = tuple(sorted(
        ((left, right, kind) for (left, right), kind in target_kinds.items()),
        key=lambda item: (len(item[0]), item[0], len(item[1]), item[1])))
    return support_words, class_words, product_class_table, targets


def canonical_boundary(certificate_path):
    """Exact 13 x 6 x 22 Fox coefficients after proved prefix merges.

    The output is only source data: Lean separately proves every prefix
    identification by replay and checks the resulting group-ring expansion.
    """
    support, _classes, _product_table, targets = support_and_targets(
        certificate_path)
    support_index = {word: index for index, word in enumerate(support)}
    prefix_to_support = dict(support_index)
    for left, right, kind in targets:
        if kind == "prefix":
            prefix_to_support[left] = support_index[right]
    answer = [[[0 for _ in range(len(support))] for _ in range(6)]
              for _ in range(13)]
    for relator_index, relator in enumerate(presentation_relators()):
        prefix = ()
        for letter in relator:
            generator = abs(letter) - 1
            if letter > 0:
                edge = prefix
                prefix = multiply(prefix, (letter,))
                coefficient = 1
            else:
                prefix = multiply(prefix, (letter,))
                edge = prefix
                coefficient = -1
            answer[relator_index][generator][prefix_to_support[edge]] += coefficient
    return answer


def shortlex(word):
    return len(word), word


def atom_word(atom, relators):
    conjugator, relator_index, inverted = atom
    relator = relators[relator_index]
    if inverted:
        relator = inverse_word(relator)
    return multiply(multiply(conjugator, relator), inverse_word(conjugator))


def atoms_word(atoms, relators):
    answer = ()
    for atom in atoms:
        answer = multiply(answer, atom_word(atom, relators))
    return answer


def invert_atoms(atoms):
    return tuple((conjugator, relator_index, not inverted)
                 for conjugator, relator_index, inverted in reversed(atoms))


class Rule(object):
    def __init__(self, left, right, atoms=None, applications=None):
        self.left = left
        self.right = right
        self.atoms = atoms
        self.applications = applications


def initial_rules(relators):
    """All oriented cyclic relator splits, each with one exact proof atom."""
    rules = []
    active = {}
    for relator_index, relator in enumerate(relators):
        for inverted, signed in ((False, relator),
                                 (True, inverse_word(relator))):
            length = len(signed)
            for shift in range(length):
                prefix = signed[:shift]
                cyclic = signed[shift:] + prefix
                base_conjugator = inverse_word(prefix)
                for cut in range(1, length + 1):
                    left = free_reduce(cyclic[:cut])
                    right = inverse_word(free_reduce(cyclic[cut:]))
                    if left == right:
                        continue
                    atom = (base_conjugator, relator_index, inverted)
                    if shortlex(left) < shortlex(right):
                        left, right = right, left
                        atom = (base_conjugator, relator_index, not inverted)
                    if atom_word(atom, relators) != multiply(
                            left, inverse_word(right)):
                        raise AssertionError("bad initial relator split")
                    old = active.get(left)
                    if old is None or shortlex(right) < shortlex(
                            rules[old].right):
                        rule = Rule(left, right, atoms=(atom,))
                        rules.append(rule)
                        active[left] = len(rules) - 1
    return rules, active


def active_rules(rules, active):
    return sorted(
        ((left, rules[index].right, index) for left, index in active.items()),
        key=lambda item: (-len(item[0]), item[0]))


def normalize_with_trace(word, rules, active, maximum_steps=10000):
    current = free_reduce(word)
    trace = []
    ordered = active_rules(rules, active)
    for _ in range(maximum_steps):
        found = False
        for position in range(len(current) + 1):
            for left, right, rule_index in ordered:
                if current[position:position + len(left)] != left:
                    continue
                following = free_reduce(
                    current[:position] + right +
                    current[position + len(left):])
                if shortlex(following) >= shortlex(current):
                    continue
                trace.append((rule_index, current[:position], False))
                current = following
                found = True
                break
            if found:
                break
        if not found:
            return current, tuple(trace)
    raise RuntimeError("normalization exceeded its step bound")


def reverse_applications(applications):
    return tuple((rule_index, prefix, not reverse)
                 for rule_index, prefix, reverse in reversed(applications))


def expand_rule_atoms(rule_index, rules, cache):
    cached = cache.get(rule_index)
    if cached is not None:
        return cached
    rule = rules[rule_index]
    if rule.atoms is not None:
        answer = rule.atoms
    else:
        expanded = []
        for parent_index, prefix, reverse in rule.applications:
            parent_atoms = expand_rule_atoms(parent_index, rules, cache)
            if reverse:
                parent_atoms = invert_atoms(parent_atoms)
            expanded.extend((multiply(prefix, conjugator), index, inverted)
                            for conjugator, index, inverted in parent_atoms)
        answer = tuple(expanded)
    cache[rule_index] = answer
    return answer


def expand_applications(applications, rules, cache=None):
    if cache is None:
        cache = {}
    answer = []
    for rule_index, prefix, reverse in applications:
        atoms = expand_rule_atoms(rule_index, rules, cache)
        if reverse:
            atoms = invert_atoms(atoms)
        answer.extend((multiply(prefix, conjugator), index, inverted)
                      for conjugator, index, inverted in atoms)
    return tuple(answer)


def add_overlap(queue, seen, rules, left_index, right_index,
                maximum_overlap_word, priority):
    left = rules[left_index].left
    right = rules[right_index].left
    # All proper overlaps, including containment critical pairs.
    for offset in range(-len(right) + 1, len(left)):
        start = min(0, offset)
        finish = max(len(left), offset + len(right))
        width = finish - start
        if width > maximum_overlap_word:
            continue
        overlap_start = max(0, offset)
        overlap_finish = min(len(left), offset + len(right))
        if overlap_start >= overlap_finish:
            continue
        if left[overlap_start:overlap_finish] != right[
                overlap_start - offset:overlap_finish - offset]:
            continue
        left_position = -start
        right_position = offset - start
        if left_index == right_index and left_position == right_position:
            continue
        key = (left_index, right_index, offset)
        if key in seen:
            continue
        seen.add(key)
        if priority == "short":
            score = width
        elif priority == "long":
            score = -width
        elif priority == "spread":
            score = ((left_index * 73856093 + right_index * 19349663 +
                      (offset + 1000) * 83492791) % 1000003)
        else:
            raise ValueError("unknown overlap priority: %s" % priority)
        queue.append((score, key))


def unresolved_targets(targets, solved):
    """Targets for which no immutable checked proof has yet been captured."""
    return [target for index, target in enumerate(targets)
            if index not in solved]


def capture_solved_targets(relators, targets, rules, active, solved,
                           atom_cache):
    """Permanently retain each target joined by the current rewrite system.

    Completion need not be confluent at an intermediate stage: a later rule
    can change one current normal form without changing the other.  Therefore
    we expand and free-check a proof immediately when a target joins, and keep
    that immutable proof regardless of subsequent normal forms.  This is the
    monotone finite-target progress invariant.
    """
    added = 0
    for index, (left, right, _kind) in enumerate(targets):
        if index in solved:
            continue
        left_normal, left_trace = normalize_with_trace(left, rules, active)
        right_normal, right_trace = normalize_with_trace(right, rules, active)
        if left_normal != right_normal:
            continue
        applications = left_trace + reverse_applications(right_trace)
        atoms = expand_applications(applications, rules, atom_cache)
        expected = multiply(left, inverse_word(right))
        if atoms_word(atoms, relators) != expected:
            raise AssertionError("captured proof atoms failed free replay")
        solved[index] = atoms
        added += 1
    return added


def currently_unresolved_targets(targets, rules, active):
    """Diagnostic only; unlike captured proofs, current normal forms can move."""
    answer = []
    for left, right, kind in targets:
        left_normal, _ = normalize_with_trace(left, rules, active)
        right_normal, _ = normalize_with_trace(right, rules, active)
        if left_normal != right_normal:
            answer.append((left, right, kind))
    return answer


def rewrite_neighbors(word, rules, active, maximum_word_length):
    """Enumerate bounded proof-producing rewrites in either direction."""
    for rule_index in active.values():
        rule = rules[rule_index]
        for pattern, replacement, reverse in (
                (rule.left, rule.right, False),
                (rule.right, rule.left, True)):
            # Reversing a rule with empty right side inserts its left side at
            # every position and creates an uninformative branching explosion.
            # Completion already includes cyclic/contextual relator rules, so
            # the bounded target search deliberately omits those empty inserts.
            if not pattern:
                continue
            for position in range(len(word) - len(pattern) + 1):
                if word[position:position + len(pattern)] != pattern:
                    continue
                following = free_reduce(
                    word[:position] + replacement +
                    word[position + len(pattern):])
                if len(following) > maximum_word_length or following == word:
                    continue
                yield following, (rule_index, word[:position], reverse)


def bidirectional_join(left, right, rules, active, seconds,
                       maximum_states, maximum_word_length):
    """Find a bounded rewrite path and return exact rule applications."""
    left = free_reduce(left)
    right = free_reduce(right)
    if left == right:
        return ()
    started = time.time()
    left_paths = {left: ()}
    right_paths = {right: ()}
    left_frontier = collections.deque([left])
    right_frontier = collections.deque([right])
    while left_frontier and right_frontier:
        if time.time() - started >= seconds:
            return None
        if len(left_paths) + len(right_paths) >= maximum_states:
            return None
        expand_left = len(left_frontier) <= len(right_frontier)
        frontier = left_frontier if expand_left else right_frontier
        own_paths = left_paths if expand_left else right_paths
        other_paths = right_paths if expand_left else left_paths
        level_size = len(frontier)
        for _ in range(level_size):
            current = frontier.popleft()
            current_path = own_paths[current]
            for following, application in rewrite_neighbors(
                    current, rules, active, maximum_word_length):
                if following in own_paths:
                    continue
                following_path = current_path + (application,)
                own_paths[following] = following_path
                frontier.append(following)
                if following not in other_paths:
                    continue
                if expand_left:
                    return following_path + reverse_applications(
                        other_paths[following])
                return other_paths[following] + reverse_applications(
                    following_path)
    return None


def target_directed_completion(relators, targets, rules, active, solved,
                               seconds, maximum_states,
                               maximum_word_length):
    """Use solved target equalities as new exact rules to cascade joins."""
    started = time.time()
    atom_cache = {}
    progress = True
    while progress and len(solved) < len(targets):
        progress = False
        for index, (left, right, _kind) in enumerate(targets):
            if index in solved:
                continue
            remaining = seconds - (time.time() - started)
            if remaining <= 0:
                return
            applications = bidirectional_join(
                left, right, rules, active,
                min(remaining, 3.0), maximum_states, maximum_word_length)
            if applications is None:
                continue
            atoms = expand_applications(applications, rules, atom_cache)
            expected = multiply(left, inverse_word(right))
            if atoms_word(atoms, relators) != expected:
                raise AssertionError("targeted proof atoms failed free replay")
            solved[index] = atoms
            new_left, new_right = left, right
            proof = applications
            if shortlex(new_left) < shortlex(new_right):
                new_left, new_right = new_right, new_left
                proof = reverse_applications(proof)
            if new_left not in active:
                rules.append(Rule(new_left, new_right, applications=proof))
                active[new_left] = len(rules) - 1
            capture_solved_targets(
                relators, targets, rules, active, solved, atom_cache)
            print(json.dumps({
                "targeted_solved": len(solved),
                "targeted_remaining": len(targets) - len(solved),
                "elapsed_s": round(time.time() - started, 3),
            }), flush=True)
            progress = True
            break


def complete(relators, targets, seconds, maximum_rules,
             maximum_overlap_word, solved=None, overlap_priority="short"):
    import heapq

    rules, active = initial_rules(relators)
    if solved is None:
        solved = {}

    # A replay loaded from a seed is already a fully checked consequence of
    # the defining relators.  Make those finite target equalities available as
    # rewrite rules immediately, instead of merely remembering their status.
    # This is particularly important for short structural identities (the
    # rank-two Weyl braid, for example) whose contextual consequences account
    # for many later coefficient merges.
    for target_index, atoms in sorted(solved.items()):
        left, right, _kind = targets[target_index]
        oriented_atoms = atoms
        if shortlex(left) < shortlex(right):
            left, right = right, left
            oriented_atoms = invert_atoms(oriented_atoms)
        old_index = active.get(left)
        if old_index is not None and shortlex(rules[old_index].right) <= \
                shortlex(right):
            continue
        rules.append(Rule(left, right, atoms=oriented_atoms))
        active[left] = len(rules) - 1

    queue = []
    seen = set()
    active_indices = list(active.values())
    for left_index in active_indices:
        for right_index in active_indices:
            add_overlap(queue, seen, rules, left_index, right_index,
                        maximum_overlap_word, overlap_priority)
    heapq.heapify(queue)
    started = time.time()
    added = 0
    atom_cache = {}
    capture_solved_targets(
        relators, targets, rules, active, solved, atom_cache)
    while queue and len(rules) < maximum_rules and time.time() - started < seconds:
        _, (left_index, right_index, offset) = heapq.heappop(queue)
        left_rule = rules[left_index]
        right_rule = rules[right_index]
        if active.get(left_rule.left) != left_index or \
                active.get(right_rule.left) != right_index:
            continue
        start = min(0, offset)
        left_position = -start
        right_position = offset - start
        finish = max(len(left_rule.left), offset + len(right_rule.left))
        overlap = [None] * (finish - start)
        for position, letter in enumerate(left_rule.left):
            overlap[left_position + position] = letter
        for position, letter in enumerate(right_rule.left):
            location = right_position + position
            if overlap[location] is not None and overlap[location] != letter:
                raise AssertionError("invalid queued overlap")
            overlap[location] = letter
        overlap = tuple(overlap)

        left_once = free_reduce(
            overlap[:left_position] + left_rule.right +
            overlap[left_position + len(left_rule.left):])
        right_once = free_reduce(
            overlap[:right_position] + right_rule.right +
            overlap[right_position + len(right_rule.left):])
        left_normal, left_trace = normalize_with_trace(
            left_once, rules, active)
        right_normal, right_trace = normalize_with_trace(
            right_once, rules, active)
        if left_normal == right_normal:
            continue

        overlap_to_left = ((left_index, overlap[:left_position], False),) + \
            left_trace
        overlap_to_right = ((right_index, overlap[:right_position], False),) + \
            right_trace
        proof = reverse_applications(overlap_to_left) + overlap_to_right
        new_left, new_right = left_normal, right_normal
        if shortlex(new_left) < shortlex(new_right):
            new_left, new_right = new_right, new_left
            proof = reverse_applications(proof)
        if len(new_left) > maximum_overlap_word:
            continue
        old_index = active.get(new_left)
        if old_index is not None and shortlex(rules[old_index].right) <= \
                shortlex(new_right):
            continue
        rules.append(Rule(new_left, new_right, applications=proof))
        new_index = len(rules) - 1
        # Old rules stay immutable in `rules` because proof DAGs may refer to
        # them.  Only the preferred active rule for this left side is replaced.
        # Captured target proofs are likewise immutable, so this optimization
        # cannot undo finite-target progress.
        active[new_left] = new_index
        added += 1
        for other_index in list(active.values()):
            # `queue` is already a heap here.  Re-heapifying the entire
            # critical-pair queue after every new rule made bounded runs spend
            # most of their time rebuilding an unchanged heap.  Collect only
            # the new overlaps and push them individually.
            fresh = []
            add_overlap(fresh, seen, rules, new_index, other_index,
                        maximum_overlap_word, overlap_priority)
            add_overlap(fresh, seen, rules, other_index, new_index,
                        maximum_overlap_word, overlap_priority)
            for item in fresh:
                heapq.heappush(queue, item)
        capture_solved_targets(
            relators, targets, rules, active, solved, atom_cache)
        if added % 100 == 0:
            print(json.dumps({
                "added_rules": added,
                "active_rules": len(active),
                "queued_pairs": len(queue),
                "unresolved_targets": len(targets) - len(solved),
                "currently_unresolved_targets": len(
                    currently_unresolved_targets(targets, rules, active)),
                "elapsed_s": round(time.time() - started, 3),
            }), flush=True)
            if len(solved) == len(targets):
                break
    return rules, active, solved


def export_reductions(relators, targets, solved):
    reductions = []
    total_atoms = 0
    maximum_atoms = 0
    for index, (left, right, kind) in enumerate(targets):
        if index not in solved:
            continue
        atoms = solved[index]
        expected = multiply(left, inverse_word(right))
        if atoms_word(atoms, relators) != expected:
            raise AssertionError("expanded proof atoms failed free replay")
        total_atoms += len(atoms)
        maximum_atoms = max(maximum_atoms, len(atoms))
        reductions.append({
            "target_index": index,
            "kind": kind,
            "left": list(left),
            "right": list(right),
            "atoms": [{
                "conjugator": list(conjugator),
                "relator_index": relator_index,
                "inverted": inverted,
            } for conjugator, relator_index, inverted in atoms],
        })
    return reductions, total_atoms, maximum_atoms


def load_seed(path, relators, targets):
    """Load only replay proofs that independently match the current targets."""
    if path is None:
        return {}
    with open(path) as source:
        data = json.load(source)
    if data.get("format") != "P13 conjugated-relator replay v1":
        raise ValueError("unrecognized seed replay format")
    solved = {}
    for reduction in data["reductions"]:
        index = int(reduction["target_index"])
        left, right, kind = targets[index]
        if reduction["kind"] != kind or \
                tuple(reduction["left"]) != left or \
                tuple(reduction["right"]) != right:
            raise ValueError("seed target does not match current target table")
        atoms = tuple((tuple(atom["conjugator"]),
                       int(atom["relator_index"]), bool(atom["inverted"]))
                      for atom in reduction["atoms"])
        if atoms_word(atoms, relators) != multiply(left, inverse_word(right)):
            raise ValueError("seed proof failed independent free replay")
        solved[index] = atoms
    return solved


class WordClasses(object):
    """Finite union-find for equalities already backed by replay proofs."""
    def __init__(self):
        self.parent = {}

    def find(self, word):
        word = free_reduce(word)
        self.parent.setdefault(word, word)
        if self.parent[word] != word:
            self.parent[word] = self.find(self.parent[word])
        return self.parent[word]

    def union(self, left, right):
        left_root = self.find(left)
        right_root = self.find(right)
        if left_root == right_root:
            return
        if shortlex(left_root) <= shortlex(right_root):
            self.parent[right_root] = left_root
        else:
            self.parent[left_root] = right_root


def partial_residual_bounds(certificate_path, relators, support, targets,
                            solved):
    """Diagnostic bound using only target merges with checked replay proofs.

    This is not the Lean certificate.  It tells us whether unresolved word
    merges are numerically necessary, while refusing to use a matrix label as
    an equality: the union-find contains exactly the solved replay targets.
    """
    prefix_replacements = {}
    product_replacements = {}
    for index in solved:
        left, right, kind = targets[index]
        replacements = (prefix_replacements if kind == "prefix"
                        else product_replacements)
        replacements[free_reduce(left)] = free_reduce(right)

    def canonical_product(word):
        word = free_reduce(word)
        return product_replacements.get(word, word)

    def add_term(element, word, coefficient):
        word = canonical_product(word)
        element[word] = element.get(word, 0) + int(coefficient)
        if element[word] == 0:
            del element[word]

    def adjoint(element):
        answer = {}
        for word, coefficient in element.items():
            inverse = inverse_word(word)
            answer[inverse] = answer.get(inverse, 0) + coefficient
            if answer[inverse] == 0:
                del answer[inverse]
        return answer

    def product(left, right):
        answer = {}
        for first, first_coefficient in left.items():
            for second, second_coefficient in right.items():
                add_term(answer, multiply(first, second),
                         first_coefficient * second_coefficient)
        return answer

    # Fox rows, with each prefix replaced only through a checked prefix replay.
    fox = []
    for relator in relators:
        row = [{} for _ in range(6)]
        prefix = ()
        for letter in relator:
            generator = abs(letter) - 1
            if letter > 0:
                edge_prefix = prefix
                prefix = multiply(prefix, (letter,))
                coefficient = 1
            else:
                prefix = multiply(prefix, (letter,))
                edge_prefix = prefix
                coefficient = -1
            edge_prefix = prefix_replacements.get(edge_prefix, edge_prefix)
            row[generator][edge_prefix] = (
                row[generator].get(edge_prefix, 0) + coefficient)
            if row[generator][edge_prefix] == 0:
                del row[generator][edge_prefix]
        fox.append(row)

    coboundary = []
    for generator in range(1, 7):
        entry = {}
        add_term(entry, (generator,), 1)
        add_term(entry, (), -1)
        coboundary.append(entry)

    delta = [[{} for _ in range(6)] for _ in range(6)]
    for left in range(6):
        for right in range(6):
            entry = delta[left][right]
            for row in fox:
                for word, coefficient in product(
                        adjoint(row[left]), row[right]).items():
                    add_term(entry, word, coefficient)
            for word, coefficient in product(
                    coboundary[left], adjoint(coboundary[right])).items():
                add_term(entry, word, coefficient)

    archive = np.load(certificate_path)
    factor = archive["factor_numerators"].astype(object)
    denominator = int(archive["factor_denominator"][0])
    gap_numerator = int(archive["gap_numerator"][0])
    gap_denominator = int(archive["gap_denominator"][0])
    gram = factor.T @ factor
    common_denominator = denominator * denominator
    if common_denominator % gap_denominator:
        raise AssertionError("unexpected nonintegral common gap scale")
    gap_scaled = gap_numerator * (common_denominator // gap_denominator)

    row_bounds = []
    residual_terms = 0
    maximum_coefficient = 0
    for left in range(6):
        row_bound = 0
        for right in range(6):
            residual = {
                word: coefficient * common_denominator
                for word, coefficient in delta[left][right].items()
            }
            if left == right:
                add_term(residual, (), -gap_scaled)
            for source, left_word in enumerate(support):
                for target, right_word in enumerate(support):
                    coefficient = int(gram[
                        left * len(support) + source,
                        right * len(support) + target])
                    if coefficient:
                        add_term(residual,
                                 multiply(inverse_word(left_word), right_word),
                                 -coefficient)
            row_bound += sum(abs(value) for value in residual.values())
            residual_terms += len(residual)
            if residual:
                maximum_coefficient = max(
                    maximum_coefficient,
                    max(abs(value) for value in residual.values()))
        row_bounds.append(row_bound)
    return {
        "proved_merges": len(solved),
        "residual_terms": residual_terms,
        "maximum_coefficient_numerator": maximum_coefficient,
        "row_bound_numerators": row_bounds,
        "maximum_row_bound_numerator": max(row_bounds),
        "common_denominator": common_denominator,
        "gap_numerator_at_common_scale": gap_scaled,
        "positive_gap": max(row_bounds) < gap_scaled,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--seed")
    parser.add_argument("--seconds", type=float, default=50.0)
    parser.add_argument("--maximum-rules", type=int, default=5000)
    parser.add_argument("--maximum-overlap-word", type=int, default=18)
    parser.add_argument("--overlap-priority", choices=("short", "long", "spread"),
                        default="short")
    parser.add_argument("--targeted-seconds", type=float, default=0.0)
    parser.add_argument("--targeted-maximum-states", type=int, default=100000)
    parser.add_argument("--targeted-maximum-word", type=int, default=20)
    parser.add_argument("--target-index", type=int)
    parser.add_argument("--report-partial-bound", action="store_true")
    args = parser.parse_args()

    relators = presentation_relators()
    support, classes, product_table, targets = support_and_targets(
        args.certificate)
    print(json.dumps({
        "support_words": len(support),
        "product_classes": len(classes),
        "targets": len(targets),
        "prefix_targets": sum(kind == "prefix" for _, _, kind in targets),
        "product_targets": sum(kind == "product" for _, _, kind in targets),
    }), flush=True)
    solved = load_seed(args.seed, relators, targets)
    if solved:
        print(json.dumps({"seed_solved": len(solved)}), flush=True)
    rules, active, solved = complete(
        relators, targets, args.seconds, args.maximum_rules,
        args.maximum_overlap_word, solved, args.overlap_priority)
    if args.target_index is not None and args.target_index not in solved:
        left, right, _kind = targets[args.target_index]
        applications = bidirectional_join(
            left, right, rules, active, args.targeted_seconds,
            args.targeted_maximum_states, args.targeted_maximum_word)
        if applications is not None:
            atoms = expand_applications(applications, rules)
            if atoms_word(atoms, relators) != multiply(
                    left, inverse_word(right)):
                raise AssertionError("focused proof atoms failed free replay")
            solved[args.target_index] = atoms
            print(json.dumps({
                "focused_target": args.target_index,
                "focused_applications": len(applications),
                "focused_atoms": len(atoms),
            }), flush=True)
    if len(solved) != len(targets) and args.targeted_seconds > 0:
        target_directed_completion(
            relators, targets, rules, active, solved,
            args.targeted_seconds, args.targeted_maximum_states,
            args.targeted_maximum_word)
    reductions, total_atoms, maximum_atoms = export_reductions(
        relators, targets, solved)
    if args.report_partial_bound:
        print(json.dumps({"partial_bound": partial_residual_bounds(
            args.certificate, relators, support, targets, solved)}),
            flush=True)
    result = {
        "format": "P13 conjugated-relator replay v1",
        "generator_order": ["e12", "e13", "e21", "e23", "e31", "e32"],
        "support_words": [list(word) for word in support],
        "product_class_words": [list(word) for word in classes],
        "product_class_table": product_table,
        "reductions": reductions,
        "proof_atoms": total_atoms,
        "maximum_atoms_per_reduction": maximum_atoms,
    }
    with open(args.output, "w") as output:
        json.dump(result, output, indent=2, sort_keys=True)
        output.write("\n")
    unresolved = unresolved_targets(targets, solved)
    if unresolved:
        print(json.dumps({
            "status": "incomplete",
            "active_rules": len(active),
            "total_rules": len(rules),
            "solved": len(solved),
            "unresolved": len(unresolved),
            "unresolved_words": [
                {"left": list(left), "right": list(right), "kind": kind}
                for left, right, kind in unresolved
            ],
            "output": args.output,
        }))
        raise SystemExit(2)
    print(json.dumps({
        "status": "complete",
        "active_rules": len(active),
        "total_rules": len(rules),
        "proof_atoms": total_atoms,
        "maximum_atoms_per_reduction": maximum_atoms,
        "output": args.output,
    }))


if __name__ == "__main__":
    main()
