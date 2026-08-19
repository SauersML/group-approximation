#!/usr/bin/env python3
"""PreToolUse guard enforcing Grok Build's PR-only repository workflow."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys

PROTECTED = {"main", "master"}
EDIT_TOOLS = {"search_replace", "Edit", "MultiEdit", "Write", "edit", "write_file"}


def deny(reason: str) -> None:
    print(
        json.dumps(
            {
                "decision": "deny",
                "reason": reason,
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "deny",
                    "permissionDecisionReason": reason,
                },
            }
        )
    )
    print(reason, file=sys.stderr)
    raise SystemExit(2)


def current_branch(cwd: str) -> str:
    try:
        proc = subprocess.run(
            ["git", "-C", cwd, "branch", "--show-current"],
            check=False,
            capture_output=True,
            text=True,
            timeout=2,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    return proc.stdout.strip() if proc.returncode == 0 else ""


def value(obj: object, *names: str) -> object | None:
    if not isinstance(obj, dict):
        return None
    for name in names:
        if name in obj:
            return obj[name]
    return None


def has_git_subcommand(command: str, subcommand: str) -> bool:
    pattern = rf"\bgit(?:\s+-C\s+\S+)?\s+{re.escape(subcommand)}\b"
    return re.search(pattern, command) is not None


def pushes_protected(command: str) -> bool:
    if not has_git_subcommand(command, "push"):
        return False
    push = re.search(r"\bgit(?:\s+-C\s+\S+)?\s+push\b([^\n;&|]*)", command)
    if not push:
        return False
    args = push.group(1)
    if re.search(r"(?:^|\s)--(?:all|mirror)(?:\s|$)", args):
        return True
    return re.search(
        r"(?:^|[\s:])(?:refs/heads/)?(?:main|master)(?=$|[\s:])",
        args,
    ) is not None


def main() -> None:
    try:
        event = json.load(sys.stdin)
    except (OSError, ValueError):
        return

    tool = value(event, "toolName", "tool_name")
    tool = tool if isinstance(tool, str) else ""
    tool_input = value(event, "toolInput", "tool_input")
    tool_input = tool_input if isinstance(tool_input, dict) else {}
    cwd = value(event, "cwd", "workspaceRoot", "workspace_root")
    cwd = cwd if isinstance(cwd, str) and cwd else os.getcwd()
    branch = current_branch(cwd)

    if tool in EDIT_TOOLS and branch in PROTECTED:
        deny(
            f"PR-only policy: edits are blocked on {branch}. "
            "Create a `grok/<task>` branch first."
        )

    command = tool_input.get("command")
    if not isinstance(command, str) or not command:
        return

    if re.search(r"\bgh\s+pr\s+merge\b", command):
        deny("PR-only policy: Grok may open or update PRs, but a human must merge them.")

    if re.search(r"\bgh\s+api\b[^\n;&|]*/pulls/[^\s]+/merge\b", command):
        deny("PR-only policy: GitHub API PR merges are blocked.")

    if pushes_protected(command):
        deny("PR-only policy: direct pushes to main/master are blocked.")

    if branch in PROTECTED:
        if has_git_subcommand(command, "push"):
            deny(
                f"PR-only policy: pushing while checked out on {branch} is blocked. "
                "Create a `grok/<task>` branch first."
            )
        if any(
            has_git_subcommand(command, sub)
            for sub in ("commit", "merge", "rebase", "cherry-pick", "revert")
        ):
            deny(
                f"PR-only policy: mutating git history on {branch} is blocked. "
                "Work on a `grok/<task>` branch."
            )


if __name__ == "__main__":
    main()
