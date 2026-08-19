#!/usr/bin/env python3
"""Tests for the PR-only PreToolUse guard.

The guard is only as good as its wiring, and both halves have failed before:
the handler once pointed at a path that does not exist from the session's
working directory, and a missing hook script exits 2, which PreToolUse reads as
*deny* -- so a broken path does not fail open, it blocks every tool call. These
tests therefore check the resolved command and the decisions together.

Run directly (``python3 .grok/hooks/test_pr_only_guard.py``) or via CI.
"""

from __future__ import annotations

import json
import os
import pathlib
import subprocess
import sys
import tempfile

HOOKS_DIR = pathlib.Path(__file__).resolve().parent
GUARD = HOOKS_DIR / 'pr-only-guard.py'
HOOK_JSON = HOOKS_DIR / 'pr-only.json'
PROJECT = HOOKS_DIR.parent.parent

DENY = 2


def _git(cwd: pathlib.Path, *args: str) -> None:
    subprocess.run(['git', '-C', str(cwd), *args], check=True,
                   capture_output=True, text=True)


def _repo(tmp: pathlib.Path, name: str, branch: str) -> pathlib.Path:
    path = tmp / name
    path.mkdir()
    _git(path, 'init', '-q', '-b', 'main')
    _git(path, '-c', 'user.email=t@t', '-c', 'user.name=t',
         'commit', '-q', '--allow-empty', '-m', 'init')
    if branch != 'main':
        _git(path, 'checkout', '-q', '-b', branch)
    return path


def _decide(event: dict) -> int:
    done = subprocess.run([sys.executable, str(GUARD)], input=json.dumps(event),
                          capture_output=True, text=True, timeout=20)
    return done.returncode


def main() -> int:
    failures = []

    def check(name: str, got: int, want: int) -> None:
        verdict = 'DENY' if got == DENY else 'allow'
        expected = 'DENY' if want == DENY else 'allow'
        if got != want:
            failures.append(f'{name}: got {verdict}, expected {expected}')
        print(f'  {"ok  " if got == want else "FAIL"}  {name:<44} {verdict}')

    # The wiring: whatever command the hook declares must resolve to the guard.
    hook = json.loads(HOOK_JSON.read_text())
    entries = hook['hooks']['PreToolUse'][0]['hooks']
    command = entries[0]['command']
    print(f'hook command: {command}')
    resolved = command.split('"')[1] if '"' in command else command.split()[-1]
    resolved = os.path.expandvars(resolved.replace('$GROK_WORKSPACE_ROOT', str(PROJECT)))
    if not pathlib.Path(resolved).is_file():
        failures.append(f'hook command does not resolve to a file: {resolved}')
    if '$GROK_WORKSPACE_ROOT' not in command and '$CLAUDE_PROJECT_DIR' not in command:
        failures.append('hook command is not anchored to the workspace root; '
                        'a relative path resolves against the session cwd and a '
                        'missing script exits 2, which PreToolUse reads as deny')
    # No matcher is deliberate: the guard decides from the tool name, so a rename
    # in the CLI cannot silently disable it. A matcher that never matches is
    # indistinguishable from a working guard in every listing Grok offers.
    if 'matcher' in hook['hooks']['PreToolUse'][0]:
        failures.append('PreToolUse declares a matcher; tool-name drift would '
                        'silently disable the guard')

    loader = json.loads((HOOKS_DIR / 'global-loader.json').read_text())
    loader_cmd = loader['hooks']['PreToolUse'][0]['hooks'][0]['command']
    if 'pr-only-guard.py' not in loader_cmd or '-f ' not in loader_cmd:
        failures.append('global loader must test for the guard before running it, '
                        'or it denies every tool call in repositories with no guard')

    with tempfile.TemporaryDirectory() as raw:
        tmp = pathlib.Path(raw)
        on_main = str(_repo(tmp, 'onmain', 'main'))
        on_branch = str(_repo(tmp, 'onbranch', 'grok/task'))

        def bash(cwd: str, cmd: str) -> dict:
            # Grok's real shell tool, not the Claude Code spelling.
            return {'toolName': 'run_terminal_command', 'cwd': cwd,
                    'toolInput': {'command': cmd}}

        print('\non main -- the protected branch:')
        # workspaceRoot arrives with a trailing slash; the guard must cope.
        check('trailing-slash workspaceRoot',
              _decide({'toolName': 'search_replace', 'workspaceRoot': on_main + '/',
                       'toolInput': {'file_path': 'x'}}), DENY)
        for tool in ('search_replace', 'edit_file', 'write_file', 'delete_file',
                     'Edit', 'Write', 'MultiEdit'):
            check(f'{tool} is refused', _decide({'toolName': tool, 'cwd': on_main,
                                                 'toolInput': {}}), DENY)
        check('git commit is refused', _decide(bash(on_main, 'git commit -m x')), DENY)
        check('git push is refused', _decide(bash(on_main, 'git push origin main')), DENY)
        check('git rebase is refused', _decide(bash(on_main, 'git rebase -i HEAD~2')), DENY)
        check('read-only git is allowed', _decide(bash(on_main, 'git status')), 0)
        check('snake_case event keys honoured',
              _decide({'tool_name': 'Write', 'cwd': on_main, 'tool_input': {}}), DENY)

        print('\nread-only tools are never blocked:')
        for tool in ('read_file', 'list_dir', 'grep'):
            check(f'{tool} is allowed on main',
                  _decide({'toolName': tool, 'cwd': on_main, 'toolInput': {}}), 0)

        print('\non a grok/ branch -- the working branch:')
        for tool in ('search_replace', 'edit_file', 'write_file', 'Edit'):
            check(f'{tool} is allowed', _decide({'toolName': tool, 'cwd': on_branch,
                                                 'toolInput': {}}), 0)
        check('pushing the topic branch is allowed',
              _decide(bash(on_branch, 'git push origin HEAD:refs/heads/grok/task')), 0)
        check('pushing to main is refused',
              _decide(bash(on_branch, 'git push origin HEAD:main')), DENY)
        check('push --all is refused',
              _decide(bash(on_branch, 'git push --all origin')), DENY)
        check('gh pr merge is refused', _decide(bash(on_branch, 'gh pr merge 5')), DENY)
        check('API merge is refused',
              _decide(bash(on_branch, 'gh api --method PUT repos/o/r/pulls/5/merge')), DENY)

    print()
    if failures:
        print('FAILURES:')
        for f in failures:
            print(' -', f)
        return 1
    print('pr-only guard: all checks passed')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
