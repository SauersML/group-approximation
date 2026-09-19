"""Deterministically export the complete 4,648-word rank-five Atlas packet.

The historical ``atlas-rank5-T_St.json`` stopped after the full Steinberg
family and the involutivity merge (4,636 words).  The mathematical packet also
contains the twelve reverse-dictionary relators.  This exporter assembles all
three source families in one process, reproduces the historical full-family /
involutivity union, appends all twelve named reverse-dictionary relations,
audits reduced-word multiplicities, and records a SHA-256 digest of the ordered
presentation list.

Generation is sparse: a word is a list of chart-factor / 4-by-4 binary-matrix
syllables.  No regular ``A8`` matrix, dense 20,160-dimensional operator, or
sector expansion is allocated.  Pass ``--verify-source-kernels`` only when a
fresh repetition of the already-recorded exact Leavitt audits is desired.
"""

import argparse
import hashlib
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import atlas_relator_rank5_full_family as full_family  # noqa: E402
import atlas_relator_rank5_involutivity as involutivity  # noqa: E402
import atlas_relator_rank5_reverse as reverse_dictionary  # noqa: E402


PROVENANCE = {
    "full_family": {
        "script": "experiments/atlas_relator_rank5_full_family.py",
        "introduced": "0c8e3b3cf",
    },
    "involutivity": {
        "script": "experiments/atlas_relator_rank5_involutivity.py",
        "introduced": "0701ceb90",
    },
    "reverse_dictionary": {
        "script": "experiments/atlas_relator_rank5_reverse.py",
        "introduced": "0c30ee812",
    },
}


def word_key(word):
    return tuple((int(factor), matrix.tobytes()) for factor, matrix in word)


def serialize_word(word):
    return [[int(factor), "".join(str(int(v)) for v in matrix.reshape(-1))]
            for factor, matrix in word]


def serialized_entry(source, name, word, lengths):
    return {
        "source": source,
        "name": name,
        "syllables": len(word),
        "x_length": sum(lengths[matrix.tobytes()]
                        for _factor, matrix in word),
        "word": serialize_word(word),
    }


def assemble(verify_source_kernels=False):
    full, lengths, _subcounts = full_family.generate_relators(
        verify=verify_source_kernels
    )
    squares, trivial_squares, square_lengths = involutivity.generate_relators(
        verify=verify_source_kernels
    )
    reverse_rows, reverse_lengths = reverse_dictionary.generate_relators(
        verify=verify_source_kernels
    )
    assert lengths.keys() == square_lengths.keys() == reverse_lengths.keys()

    entries = []
    seen_nonempty = set()
    duplicates = {"involutivity": []}

    def add(source, name, word):
        key = word_key(word)
        if key in seen_nonempty:
            duplicates[source].append(name)
            return False
        seen_nonempty.add(key)
        entries.append(serialized_entry(source, name, word, lengths))
        return True

    for name, word in full:
        assert add("full_family", name, word)

    for name, word in squares:
        add("involutivity", name, word)

    for row in reverse_rows:
        name, _chart, _u, _v, _factors, _dictionary_word, relator, _ok = row
        # These are twelve named presentation relations, eight of which reduce
        # freely to the empty word.  Preserve all twelve occurrences: 4,648 is
        # the proved assembly count, while 4,640 is its nonempty reduced count.
        entries.append(serialized_entry(
            "reverse_dictionary", "reverse_%s" % name, relator, lengths
        ))

    reverse_nonempty = [row[6] for row in reverse_rows if row[6]]
    reverse_trivial = len(reverse_rows) - len(reverse_nonempty)
    reverse_overlap = sum(word_key(word) in seen_nonempty
                          for word in reverse_nonempty)
    distinct_nonempty = len(seen_nonempty | {word_key(word)
                                             for word in reverse_nonempty})

    counts = {
        "full_family_distinct": len(full),
        "involutivity_considered": len(squares) + len(trivial_squares),
        "involutivity_freely_trivial": len(trivial_squares),
        "involutivity_nontrivial": len(squares),
        "involutivity_duplicate_of_full_family":
            len(duplicates["involutivity"]),
        "involutivity_added":
            len(squares) - len(duplicates["involutivity"]),
        "family_plus_involutivity":
            len(full) + len(squares) - len(duplicates["involutivity"]),
        "reverse_dictionary_considered": len(reverse_rows),
        "reverse_dictionary_freely_trivial": reverse_trivial,
        "reverse_dictionary_nontrivial": len(reverse_nonempty),
        "reverse_dictionary_nontrivial_overlap": reverse_overlap,
        "presentation_packet_entries": len(entries),
        "nonempty_packet_entries": sum(bool(entry["word"])
                                       for entry in entries),
        "distinct_nonempty_words": distinct_nonempty,
    }

    expected = {
        "full_family_distinct": 4612,
        "involutivity_considered": 100,
        "involutivity_freely_trivial": 12,
        "involutivity_nontrivial": 88,
        "involutivity_duplicate_of_full_family": 64,
        "involutivity_added": 24,
        "family_plus_involutivity": 4636,
        "reverse_dictionary_considered": 12,
        "reverse_dictionary_freely_trivial": 8,
        "reverse_dictionary_nontrivial": 4,
        "reverse_dictionary_nontrivial_overlap": 0,
        "presentation_packet_entries": 4648,
        "nonempty_packet_entries": 4640,
        "distinct_nonempty_words": 4640,
    }
    assert counts == expected, (counts, expected)

    canonical_words = json.dumps(
        [entry["word"] for entry in entries],
        ensure_ascii=True,
        separators=(",", ":"),
    ).encode("ascii")
    digest = hashlib.sha256(canonical_words).hexdigest()
    metadata = {
        "schema": "atlas-rank5-complete-packet-v1",
        "provenance": PROVENANCE,
        "counts": counts,
        "duplicate_names": duplicates,
        "word_list_sha256": digest,
    }
    return metadata, entries


def emit_json(path, metadata, entries):
    with open(path, "w") as handle:
        handle.write('{"metadata":')
        json.dump(metadata, handle, ensure_ascii=True, sort_keys=True,
                  separators=(",", ":"))
        handle.write(',"relators":[')
        for index, entry in enumerate(entries):
            if index:
                handle.write(",")
            json.dump(entry, handle, ensure_ascii=True, sort_keys=True,
                      separators=(",", ":"))
        handle.write("]}\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit", default="",
                        help="write the complete packet to this JSON path")
    parser.add_argument("--verify-source-kernels", action="store_true",
                        help="repeat the exact source-family Leavitt audits")
    args = parser.parse_args()

    metadata, entries = assemble(args.verify_source_kernels)
    print(json.dumps(metadata["counts"], sort_keys=True))
    print("word_list_sha256:", metadata["word_list_sha256"])
    if args.emit:
        emit_json(args.emit, metadata, entries)
        print("wrote", args.emit)
    return 0


if __name__ == "__main__":
    sys.exit(main())
