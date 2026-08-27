#!/usr/bin/env python3
"""Checks the Titz--Witzel involution-sandwich normal form.

No external packages are required.  The free-word checks verify the literal
substitutions.  Random permutation checks exercise every quantitative
inequality; the written proof supplies the general argument.
"""

from random import Random


def reduce_word(word, involutions=()):
    involutions = set(involutions)
    out = []
    for letter in word:
        if abs(letter) in involutions:
            letter = abs(letter)
        if out and out[-1] == -letter:
            out.pop()
        elif out and letter in involutions and out[-1] == letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def product(*words, involutions=()):
    return reduce_word(
        (letter for word in words for letter in word), involutions
    )


def inverse(word):
    return tuple(-letter for letter in reversed(word))


def power(word, exponent, involutions=()):
    if exponent < 0:
        return power(inverse(word), -exponent, involutions)
    return product(*(word for _ in range(exponent)), involutions=involutions)


def words():
    e, u = (1,), (2,)
    invs = (1,)
    p = lambda *ws: product(*ws, involutions=invs)
    q = lambda w, k: power(w, k, involutions=invs)
    h = p(u, e, inverse(u))
    a = p(e, h, e)
    x = p(a, q(u, 2))
    c = p(q(u, 2), a, q(u, 2))
    f = p(inverse(x), h, x)
    d = p(e, inverse(a), f)
    s = p(f, a, f)
    rho = p(inverse(x), inverse(s), inverse(c))
    b = p(rho, inverse(u), rho)
    beta = p(rho, e, inverse(rho))
    sandwich = p(beta, a)
    r0 = p(q(rho, 2), e, inverse(u))
    p0 = p(b, x, inverse(u), inverse(d))
    q0 = p(a, c, d, b)
    new_p = p(beta, a, u, inverse(d))
    w = p(q(d, 2), inverse(u), c)
    j = p(sandwich, u, sandwich, c)
    return locals()


def compose(left, right):
    return tuple(left[right[i]] for i in range(len(left)))


def perm_inverse(p):
    out = [0] * len(p)
    for i, image in enumerate(p):
        out[image] = i
    return tuple(out)


def evaluate(word, images):
    result = tuple(range(len(next(iter(images.values())))))
    inverses = {key: perm_inverse(value) for key, value in images.items()}
    for letter in word:
        image = images[abs(letter)] if letter > 0 else inverses[abs(letter)]
        result = compose(result, image)
    return result


def defect(p):
    return sum(i != image for i, image in enumerate(p))


def random_involution(rng, n):
    points = list(range(n))
    rng.shuffle(points)
    result = list(range(n))
    while len(points) >= 2:
        if rng.randrange(3) == 0:
            points.pop()
            continue
        i, j = points.pop(), points.pop()
        result[i], result[j] = j, i
    return tuple(result)


def random_permutation(rng, n):
    result = list(range(n))
    rng.shuffle(result)
    return tuple(result)


def main():
    w = words()
    p = w["p"]
    invs = w["invs"]

    # x u^-1 = a u, the only free reduction in the old fourth relator.
    assert p(w["x"], inverse(w["u"])) == p(w["a"], w["u"])

    # If d is replaced by p*u, the square-root word becomes the sandwich.
    symbolic_d = p(w["sandwich"], w["u"])
    assert p(power(symbolic_d, 2, invs), inverse(w["u"]), w["c"]) == w["j"]

    # If b is replaced by d*u^-1*a, Q is conjugate/cyclic-conjugate to W.
    symbolic_b = p(w["d"], inverse(w["u"]), w["a"])
    q_sub = p(w["a"], w["c"], w["d"], symbolic_b)
    q_stripped = p(w["a"], q_sub, w["a"])
    cyclic_w = p(w["c"], w["d"], w["d"], inverse(w["u"]))
    assert q_stripped == cyclic_w

    rng = Random(20260826)
    for n in range(3, 15):
        for _ in range(80):
            images = {1: random_involution(rng, n), 2: random_permutation(rng, n)}
            defects = {
                name: defect(evaluate(w[name], images))
                for name in ("r0", "p0", "q0", "new_p", "w", "j")
            }
            assert abs(defects["new_p"] - defects["p0"]) <= defects["r0"]
            assert defects["w"] <= defects["q0"] + defects["p0"]
            assert defects["q0"] <= defects["w"] + defects["p0"]
            assert abs(defects["j"] - defects["w"]) <= 2 * defects["new_p"]

            c2 = power(w["c"], 2, w["invs"])
            p2 = power(w["sandwich"], 2, w["invs"])
            u2 = power(w["u"], 2, w["invs"])
            u8 = power(w["u"], 8, w["invs"])
            delta_c = defect(evaluate(c2, images))
            theta = defect(evaluate(p2, images))
            marked2 = defect(evaluate(u2, images))
            marked8 = defect(evaluate(u8, images))
            commutator_ue = product(
                w["h"], inverse(w["e"]), involutions=w["invs"]
            )
            kappa = defect(evaluate(commutator_ue, images))
            u2e = product(u2, w["e"], involutions=w["invs"])
            eu2 = product(w["e"], u2, involutions=w["invs"])
            eta = sum(
                left != right
                for left, right in zip(
                    evaluate(u2e, images), evaluate(eu2, images)
                )
            )
            support_e = defect(evaluate(w["e"], images))
            assert marked8 <= delta_c + 6 * kappa
            assert marked8 <= delta_c + 6 * eta
            assert marked8 <= delta_c + 2 * support_e
            assert marked2 <= delta_c + 2 * defects["j"] + 2 * theta
            assert marked8 <= 4 * delta_c + 8 * defects["j"] + 8 * theta

    print("all Titz--Witzel involution-sandwich checks passed")


if __name__ == "__main__":
    main()
