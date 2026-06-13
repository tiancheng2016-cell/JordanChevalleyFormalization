# Jordan-Chevalley Formalization

## Main Theorem

`AI4MATH.jordan_chevalley_decomposition`

## Description

This repository contains my AI for Mathematics Assignment 2 Lean formalization of the Jordan-Chevalley decomposition for finite-dimensional linear operators over an algebraically closed field.

## Files

- `Formalization.lean`: final Lean proof.
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`: Lean/Lake project metadata.
- `report.pdf`: final report.
- `agent_config_and_prompts.zip`: optional agent prompt/config/log bundle.
- `verification/FINAL_VERIFICATION.md`: final verification log.
- `verification/AXIOMS_OUTPUT.txt`: final `#print axioms` output.

## Lean / Mathlib Version

- Lean toolchain: `leanprover/lean4:v4.30.0`
- Mathlib version requested in `lakefile.toml`: `leanprover-community/mathlib` at `v4.30.0`
- Mathlib manifest revision in `lake-manifest.json`: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

## Verification Command

Run:

```text
lake env lean Formalization.lean
```

Final result:

```text
Lean accepted the file with no output.
```

## Axiom Check

Exact final output:

```text
'AI4MATH.jordan_chevalley_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` appears.

The proof is not choice-free, because `Classical.choice` appears in the axiom output.

## Agent Workflow Summary

Codex was used as the agentic coding assistant. Numina-Lean-Agent was used as the Lean proving-agent harness. A local wrapper translated Numina's Claude-shaped calls to Codex CLI calls.

Archon was attempted but blocked by Claude Code authentication. Round 1 was rejected because it used a Newton shortcut too close to Mathlib's own Jordan-Chevalley proof. Round 2 was the strict repair iteration and produced the final accepted proof.

Final trust came from Lean kernel verification, forbidden-name searches, and `#print axioms`.

## GitHub Pages / Live Lean Page

This repository includes `index.html`, which can be served with GitHub Pages. After publishing, open:

```text
https://<your-username>.github.io/JordanChevalleyFormalization/
```

The page includes an "Open in live Lean" button that loads `Formalization.lean` into live Lean using the `#url=` mechanism.

The live Lean editor may use a newer Mathlib version; the pinned verified build is the local Lake project using `lean-toolchain` and `lake-manifest.json`.

## Notes

- `.lake/` is intentionally not included.
- To reproduce, run `lake exe cache get` first if Mathlib cache is needed, then run `lake env lean Formalization.lean`.
- No API keys, tokens, or authentication files are included.
