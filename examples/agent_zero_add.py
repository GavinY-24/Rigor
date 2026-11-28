#!/usr/bin/env python3
"""End-to-end agent-loop example for `rigor machine`.

Run from the repository root after `cargo build --release`:

    python3 examples/agent_zero_add.py ./target/release/rigor /tmp/zero_add.rigorb
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "agent"))

from rigor_machine import RigorMachine


SOURCE = """\
theorem zero_add_machine (given n : Nat) : 0 + n = n := by
  trivial
"""


def main() -> int:
    rigor = sys.argv[1] if len(sys.argv) > 1 else "rigor"
    out = sys.argv[2] if len(sys.argv) > 2 else "zero_add.rigorb"
    with RigorMachine(rigor) as machine:
        response = machine.open(SOURCE)
        if not response["ok"]:
            print(response["message"], file=sys.stderr)
            return 1

        # The response already contains ranked hints. A real agent can choose
        # using its own model; this example simply tries them in ranked order.
        state = response["state_id"]
        proved = None
        for hint in response["suggestions"]:
            attempt = machine.apply(hint["tactic"])
            if attempt["ok"]:
                proved = attempt
                break
            # Failed attempts do not mutate the immutable state. Restore is
            # explicit here both as error recovery and as protocol documentation.
            machine.restore(state)

        if proved is None or not all(goal["closed"] for goal in machine.inspect()["goals"]):
            print("no suggested tactic closed the goal", file=sys.stderr)
            return 1

        sealed = machine.seal(path=out, verify=True, include_bundle=False)
        if not sealed["ok"]:
            print(sealed.get("error") or sealed["message"], file=sys.stderr)
            return 1
        verification = sealed["sealed"]["verification"]
        print(f"verified {verification['verdict']} in {verification['wall_ms']} ms -> {out}")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
