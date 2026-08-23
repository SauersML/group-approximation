#!/usr/bin/env python3
"""Bounded shortlex Knuth--Bendix probe for the concrete triangular table."""

import argparse
import json
import time
from collections import deque


def order_key(word):
    return len(word), word


def orient(left, right):
    if left == right:
        return None
    return (left, right) if order_key(left) > order_key(right) else (right, left)


def reduce_word(word, rules, rule_index):
    word = tuple(word)
    while True:
        changed = False
        for position in range(len(word)):
            for rule_number in rule_index.get(word[position], ()):
                left, right = rules[rule_number]
                if left and word[position : position + len(left)] == left:
                    word = word[:position] + right + word[position + len(left):]
                    changed = True
                    break
            if changed:
                break
        if not changed:
            return word


def critical_equations(first, second):
    left1, right1 = first
    left2, right2 = second
    equations = []
    for overlap in range(1, min(len(left1), len(left2)) + 1):
        if left1[-overlap:] == left2[:overlap]:
            equations.append((
                right1 + left2[overlap:],
                left1[:-overlap] + right2,
            ))
    for position in range(len(left1) - len(left2) + 1):
        if left1[position : position + len(left2)] == left2:
            equations.append((
                right1,
                left1[:position] + right2 + left1[position + len(left2):],
            ))
    return equations


def irreducible_automaton_has_cycle(rules, alphabet):
    forbidden = {left for left, _ in rules}
    prefixes = {()}
    for left in forbidden:
        prefixes.update(left[:length] for length in range(1, len(left)))

    def transition(state, letter):
        word = state + (letter,)
        if any(len(left) <= len(word) and word[-len(left):] == left
               for left in forbidden):
            return None
        return max(
            (prefix for prefix in prefixes
             if len(prefix) <= len(word) and word[-len(prefix):] == prefix),
            key=len,
        )

    graph = {}
    pending = deque([()])
    graph[()] = []
    while pending:
        state = pending.popleft()
        for letter in range(alphabet):
            target = transition(state, letter)
            if target is None:
                continue
            graph[state].append((letter, target))
            if target not in graph:
                graph[target] = []
                pending.append(target)

    colors = {}
    def visit(state):
        colors[state] = 1
        for _, target in graph[state]:
            if colors.get(target) == 1:
                return True
            if colors.get(target, 0) == 0 and visit(target):
                return True
        colors[state] = 2
        return False

    return visit(()), len(graph)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate")
    parser.add_argument("--seconds", type=float, default=20.0)
    parser.add_argument("--max-rules", type=int, default=5000)
    parser.add_argument("--output")
    args = parser.parse_args()
    with open(args.certificate) as source:
        certificate = json.load(source)
    alphabet = 2 * certificate["generators"]

    equations = [((letter, letter ^ 1), ()) for letter in range(alphabet)]
    for relator in certificate["table"]:
        word = tuple(relator)
        equations.append((word, ()))
        equations.append((tuple(letter ^ 1 for letter in reversed(word)), ()))

    rules = []
    rule_set = set()
    for left, right in equations:
        rule = orient(left, right)
        if rule is not None and rule not in rule_set:
            rule_set.add(rule)
            rules.append(rule)
    rule_index = {}
    for rule_number, (left, _) in enumerate(rules):
        rule_index.setdefault(left[0], []).append(rule_number)
    queue = deque(
        (i, j) for i in range(len(rules)) for j in range(len(rules))
        if critical_equations(rules[i], rules[j])
    )
    started = time.monotonic()
    processed = 0
    status = "complete"
    while queue:
        if time.monotonic() - started > args.seconds:
            status = "timeout"
            break
        i, j = queue.popleft()
        processed += 1
        for left, right in critical_equations(rules[i], rules[j]):
            left_nf = reduce_word(left, rules, rule_index)
            right_nf = reduce_word(right, rules, rule_index)
            rule = orient(left_nf, right_nf)
            if rule is None or rule in rule_set:
                continue
            if len(rules) >= args.max_rules:
                status = "rule_limit"
                queue.clear()
                break
            new_index = len(rules)
            rule_set.add(rule)
            rules.append(rule)
            rule_index.setdefault(rule[0][0], []).append(new_index)
            for old_index in range(new_index + 1):
                if critical_equations(rules[new_index], rules[old_index]):
                    queue.append((new_index, old_index))
                if critical_equations(rules[old_index], rules[new_index]):
                    queue.append((old_index, new_index))

    result = {
        "status": status,
        "rules": len(rules),
        "pending_pairs": len(queue),
        "processed_pairs": processed,
        "maximum_left_length": max(map(lambda rule: len(rule[0]), rules)),
        "maximum_right_length": max(map(lambda rule: len(rule[1]), rules)),
        "elapsed_seconds": time.monotonic() - started,
        "singleton_left_sides": len({left for left, _ in rules if len(left) == 1}),
        "nonempty_reduced_letters": sum(
            bool(reduce_word((letter,), rules, rule_index)) for letter in range(alphabet)
        ),
    }
    if status == "complete":
        has_cycle, automaton_states = irreducible_automaton_has_cycle(
            rules, alphabet
        )
        result["infinite_normal_forms"] = has_cycle
        result["normal_form_states"] = automaton_states
    if args.output:
        with open(args.output, "w") as output:
            json.dump({
                "summary": result,
                "rules": [[list(left), list(right)] for left, right in rules],
            }, output, separators=(",", ":"))
        result["output"] = args.output
    print(json.dumps(result))


if __name__ == "__main__":
    main()
