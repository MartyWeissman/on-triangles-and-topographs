# Contributing

Please explain the mathematical or pedagogical issue and the intended change.
For mathematical changes, identify the affected definitions and theorem
statements, not just the tactics that changed. State any substantive AI
assistance used in a contribution.

Run `./scripts/verify.sh` before proposing a source change. Do not introduce
proof placeholders, extra mathematical axioms, or `native_decide`. Extend
`Check.lean` when adding important public theorems. Keep dependency upgrades
separate and explain why they are needed.

Documentation corrections are welcome, particularly where informal prose
could suggest a stronger statement than the formal theorem. The definitions
and kernel-checked theorems determine the formal result. New mathematical
claims and attribution or novelty claims require human review and sources.

Update the changelog and regenerate source statistics when appropriate.

Contributions are submitted under the applicable license described in
[LICENSES.md](LICENSES.md): Apache 2.0 for software and CC BY 4.0 for standalone
documentation. Preserve any applicable third-party notices.
