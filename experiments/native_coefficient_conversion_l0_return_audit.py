"""Exact signed-L0 return audit for the two nested native coefficient chains.

Run on MSI only.  This tests every actor spare endpoint for the minimal
Steinberg multiplication by t_00 after x_1 or before x_2.
"""

from order_seven_head_return_conjugacy_audit import (
    COORDS, ARROWS, closure_with_words, shortest_conjugator,
)


def main():
    words = closure_with_words()
    print('signed L0 size', len(words))

    first = []
    # x_89(x1) * x_(9,ell)(t00) produces x_(8,ell)(y2).
    # In source-to-target notation test ell->8 against native 9->8.
    for ell in COORDS:
        if ell in (8, 9):
            continue
        shortest, count = shortest_conjugator(words, ell, 8, 9, 8)
        first.append((ell, shortest, count))
        print('x1*t00 endpoint', ell, 'to native y2:',
              'NO' if shortest is None else 'YES', 'hits', count)

    second = []
    # x_(ell,7)(t00) * x_78(x2) produces x_(ell,8)(y1).
    # In source-to-target notation test 8->ell against native 8->7.
    for ell in COORDS:
        if ell in (7, 8):
            continue
        shortest, count = shortest_conjugator(words, 8, ell, 8, 7)
        second.append((ell, shortest, count))
        print('t00*x2 endpoint', ell, 'to native y1:',
              'NO' if shortest is None else 'YES', 'hits', count)

    assert all(shortest is None and count == 0
               for _, shortest, count in first)
    assert all(shortest is None and count == 0
               for _, shortest, count in second)
    assert len(first) == len(second) == 5


if __name__ == '__main__':
    main()
