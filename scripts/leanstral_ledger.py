#!/usr/bin/env python3
"""Permanent reservation ledger for the Leanstral lane.

A reservation is made *before* inference and must survive failed runs, no-change
runs, and PRs that are never merged. That state therefore cannot live in the
working tree, and this repository deliberately carries exactly two branches, so
it cannot live on a branch either.

It lives instead at the git ref ``refs/leanstral/ledger``: real git objects in
the repository's own object store, permanent, but outside ``refs/heads`` and
``refs/tags``, so it is not a branch, not a tag, not fetched by a default clone,
and invisible in every branch and tag listing.

Concurrency, honestly. GitHub does **not** enforce fast-forward on refs outside
``refs/heads``: a ``PATCH`` with ``force: false`` onto a sibling commit returns
200 and moves the ref (measured, not assumed). So this is not compare-and-swap,
and the workflow's ``concurrency`` group -- one agent run at a time -- is what
actually prevents concurrent appends.

What this module adds is that a lost write cannot go *unnoticed* or stay lost:

* before moving the ref it re-reads the tip and refuses if it moved under us;
* after moving it re-reads and requires the result to be exactly the rows it
  read plus its own, so a clobber fails the run instead of passing quietly;
* every append is a commit parented on the previous one, so ``verify`` can walk
  the chain and recover any row a bad write dropped. That is the real advantage
  over a mutable file: the history is in the object graph, not overwritten.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import sys
import time
import urllib.error
import urllib.request

API = os.environ.get('GITHUB_API_URL', 'https://api.github.com')
REF = 'refs/leanstral/ledger'
LEDGER_PATH = 'attempts.tsv'
HEADER = '# run_id\treserved_at_utc\tlean_path\tdeclaration_anchor'
MAX_ATTEMPTS = 6


class LedgerError(RuntimeError):
    pass


def _token() -> str:
    for name in ('GITHUB_TOKEN', 'GH_TOKEN'):
        value = os.environ.get(name)
        if value:
            return value
    raise LedgerError('no GITHUB_TOKEN/GH_TOKEN in the environment')


def _repo() -> str:
    repo = os.environ.get('GITHUB_REPOSITORY')
    if not repo:
        raise LedgerError('GITHUB_REPOSITORY is not set')
    return repo


def _api(path: str, method: str = 'GET', payload: dict | None = None):
    """One GitHub REST call. Returns None for 404/409/422 so callers can branch."""
    url = path if path.startswith('http') else f'{API}/{path}'
    data = json.dumps(payload).encode() if payload is not None else None
    request = urllib.request.Request(url, data=data, method=method)
    request.add_header('Authorization', f'Bearer {_token()}')
    request.add_header('Accept', 'application/vnd.github+json')
    request.add_header('X-GitHub-Api-Version', '2022-11-28')
    if data is not None:
        request.add_header('Content-Type', 'application/json')
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            body = response.read()
            return json.loads(body) if body else {}
    except urllib.error.HTTPError as error:
        if error.code in (404, 409, 422):
            return None
        detail = error.read().decode('utf-8', 'replace')[:400]
        raise LedgerError(f'{method} {url} -> HTTP {error.code}: {detail}') from error


def parse(text: str) -> list[list[str]]:
    """Well-formed reservation rows only; comments and stray lines are dropped."""
    rows = []
    for line in text.splitlines():
        if not line or line.startswith('#'):
            continue
        fields = line.split('\t')
        if len(fields) == 4 and fields[0].isdigit() and all(f.strip() for f in fields):
            rows.append(fields)
    return rows


def serialize(rows: list[list[str]]) -> str:
    return '\n'.join([HEADER] + ['\t'.join(r) for r in rows]) + '\n'


def tip() -> str | None:
    got = _api(f'repos/{_repo()}/git/ref/{REF[len("refs/"):]}')
    return got['object']['sha'] if got else None


def read_at(commit_sha: str | None) -> list[list[str]]:
    if not commit_sha:
        return []
    commit = _api(f'repos/{_repo()}/git/commits/{commit_sha}')
    if not commit:
        raise LedgerError(f'ledger commit {commit_sha} is unreadable')
    tree = _api(f'repos/{_repo()}/git/trees/{commit["tree"]["sha"]}')
    blob_sha = next(
        (e['sha'] for e in (tree or {}).get('tree', []) if e['path'] == LEDGER_PATH), None
    )
    if not blob_sha:
        return []
    blob = _api(f'repos/{_repo()}/git/blobs/{blob_sha}')
    raw = base64.b64decode((blob or {}).get('content', ''))
    return parse(raw.decode('utf-8'))


def _commit_rows(rows: list[list[str]], parent: str | None, message: str) -> str:
    repo = _repo()
    content = base64.b64encode(serialize(rows).encode()).decode()
    blob = _api(f'repos/{repo}/git/blobs', 'POST',
                {'content': content, 'encoding': 'base64'})
    tree = _api(f'repos/{repo}/git/trees', 'POST',
                {'tree': [{'path': LEDGER_PATH, 'mode': '100644',
                           'type': 'blob', 'sha': blob['sha']}]})
    commit = _api(f'repos/{repo}/git/commits', 'POST',
                  {'message': message, 'tree': tree['sha'],
                   'parents': [parent] if parent else []})
    return commit['sha']


def append(run_id: str, target: str, anchor: str) -> list[list[str]]:
    """Append one reservation. Raises if (target, anchor) is already reserved."""
    repo = _repo()
    row = [run_id, time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), target, anchor]
    for attempt in range(MAX_ATTEMPTS):
        parent = tip()
        rows = read_at(parent)
        if any(r[2] == target and r[3] == anchor for r in rows):
            raise LedgerError(f'already reserved: {target} :: {anchor}')
        new_sha = _commit_rows(rows + [row], parent,
                               f'reserve Leanstral target {run_id}')
        if tip() != parent:
            time.sleep(0.7 * (attempt + 1))  # someone appended while we built
            continue
        if parent is None:
            moved = _api(f'repos/{repo}/git/refs', 'POST', {'ref': REF, 'sha': new_sha})
        else:
            moved = _api(f'repos/{repo}/git/refs/{REF[len("refs/"):]}', 'PATCH',
                         {'sha': new_sha, 'force': False})
        if moved is None:
            time.sleep(0.7 * (attempt + 1))
            continue
        # The ref moved; prove it holds exactly what it should. GitHub will not
        # do this for us on a custom ref, so an unnoticed clobber is the failure
        # mode worth spending a read on.
        written = read_at(tip())
        want = [tuple(r) for r in rows] + [tuple(row)]
        if [tuple(r) for r in written] != want:
            raise LedgerError(
                f'ledger is not what was written: expected {len(want)} rows ending in '
                f'{run_id}, found {len(written)}. Run "verify" to recover from the chain.'
            )
        return written
    raise LedgerError(f'gave up after {MAX_ATTEMPTS} attempts appending {run_id}')


def verify() -> tuple[list[list[str]], list[list[str]]]:
    """Walk the commit chain; report rows that were once recorded but are gone.

    A dropped row is recoverable precisely because each append is a commit, so
    this is the repair path for a write that lost a race.
    """
    current = {tuple(r) for r in read_at(tip())}
    seen, sha, order = {}, tip(), []
    while sha:
        for r in read_at(sha):
            if tuple(r) not in seen:
                seen[tuple(r)] = sha
                order.append(r)
        commit = _api(f'repos/{_repo()}/git/commits/{sha}')
        parents = (commit or {}).get('parents', [])
        sha = parents[0]['sha'] if parents else None
    missing = [list(r) for r in seen if r not in current]
    missing.sort(key=lambda r: int(r[0]))
    return [list(r) for r in order], missing


def _self_test() -> None:
    rows = [['1', 'T', 'a.lean', 'x'], ['2', 'T', 'b.lean', 'y']]
    assert parse(serialize(rows)) == rows
    # comments, blank lines, short rows and non-numeric ids are not reservations
    noise = serialize(rows) + '\n# note\nnot\ta\trow\nabc\tT\tc.lean\tz\n1\t2\t3\n'
    assert parse(noise) == rows
    # a tab inside a field would corrupt the row, so reject at the boundary
    assert parse('9\tT\ta.lean\tx\ty') == []
    assert parse('9\tT\t\tx') == []
    # round-trip through base64 the way the blob API carries it
    encoded = base64.b64encode(serialize(rows).encode()).decode()
    assert parse(base64.b64decode(encoded).decode()) == rows
    assert serialize([]).strip() == HEADER
    # the post-write invariant is order-sensitive: appending must preserve prefix
    before = [['1', 'T', 'a.lean', 'x']]
    after = before + [['2', 'T', 'b.lean', 'y']]
    assert [tuple(r) for r in after] == [tuple(r) for r in before] + [('2', 'T', 'b.lean', 'y')]
    assert parse(serialize(after))[:1] == before
    print('leanstral ledger self-test: ok')


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('command', choices=['read', 'append', 'verify', 'self-test'])
    ap.add_argument('--run-id')
    ap.add_argument('--target')
    ap.add_argument('--anchor')
    args = ap.parse_args()

    if args.command == 'self-test':
        _self_test()
        return 0
    try:
        if args.command == 'read':
            sys.stdout.write(''.join('\t'.join(r) + '\n' for r in read_at(tip())))
            return 0
        if args.command == 'verify':
            _, missing = verify()
            for row in missing:
                print('MISSING\t' + '\t'.join(row))
            print(f'ledger verify: {len(missing)} row(s) dropped from the tip',
                  file=sys.stderr)
            return 1 if missing else 0
        if not (args.run_id and args.target and args.anchor):
            ap.error('append requires --run-id, --target and --anchor')
        rows = append(args.run_id, args.target, args.anchor)
        print(f'reserved {args.target} :: {args.anchor} ({len(rows)} total) at {REF}')
        return 0
    except LedgerError as error:
        print(f'::error::{error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
