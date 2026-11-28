"""Minimal Python client for `rigor machine` JSONL sessions.

The client is standard-library only. It is a producer-side convenience: the
Rigor kernel and runtime still decide whether any emitted proof is valid.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Optional


class RigorMachineError(RuntimeError):
    pass


class RigorMachine:
    """Synchronous client for one `rigor machine` subprocess.

    Every method returns the decoded JSON response. Failed commands normally
    have `ok=False`; they are returned rather than raised so an agent can use
    the error message as search feedback.
    """

    def __init__(self, rigor: str | Path = "rigor") -> None:
        self.proc = subprocess.Popen(
            [str(rigor), "machine"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        if self.proc.stdin is None or self.proc.stdout is None:
            raise RigorMachineError("failed to open rigor machine pipes")

    def command(self, **obj: Any) -> dict[str, Any]:
        if self.proc.poll() is not None:
            err = self.proc.stderr.read() if self.proc.stderr else ""
            raise RigorMachineError(f"rigor machine exited with {self.proc.returncode}: {err}")
        assert self.proc.stdin is not None
        assert self.proc.stdout is not None
        self.proc.stdin.write(json.dumps(obj, separators=(",", ":")) + "\n")
        self.proc.stdin.flush()
        line = self.proc.stdout.readline()
        if not line:
            err = self.proc.stderr.read() if self.proc.stderr else ""
            raise RigorMachineError(f"rigor machine closed stdout: {err}")
        return json.loads(line)

    def open(self, source: str) -> dict[str, Any]:
        return self.command(op="open", source=source)

    def inspect(self) -> dict[str, Any]:
        return self.command(op="inspect")

    def suggest(self) -> dict[str, Any]:
        return self.command(op="suggest")

    def apply(self, tactic: str) -> dict[str, Any]:
        return self.command(op="apply", tactic=tactic)

    def cert(self, plugin: str, args: Optional[list[str | int]] = None) -> dict[str, Any]:
        return self.command(op="cert", plugin=plugin, args=args or [])

    def fork(self, goal: str) -> dict[str, Any]:
        return self.command(op="fork", goal=goal)

    def restore(self, state: str) -> dict[str, Any]:
        return self.command(op="restore", state=state)

    def seal(
        self,
        *,
        verify: bool = True,
        path: str | Path | None = None,
        include_bundle: bool = False,
    ) -> dict[str, Any]:
        obj: dict[str, Any] = {"op": "seal", "verify": verify, "include_bundle": include_bundle}
        if path is not None:
            obj["path"] = str(path)
        return self.command(**obj)

    def close(self) -> None:
        if self.proc.poll() is None:
            try:
                assert self.proc.stdin is not None
                self.proc.stdin.write('{"op":"quit"}\n')
                self.proc.stdin.flush()
                self.proc.stdin.close()
            except (BrokenPipeError, AssertionError):
                pass
            try:
                self.proc.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.proc.kill()
                self.proc.wait()

    def __enter__(self) -> "RigorMachine":
        return self

    def __exit__(self, *_: object) -> None:
        self.close()


def open_file(machine: RigorMachine, path: str | Path) -> dict[str, Any]:
    """Open the first theorem in a `.rigor` file in an interactive session."""
    return machine.open(Path(path).read_text())
