# Reference proofs for two PR #2318 gaps

These files are reference copies of Lean proofs for the two catalogue entries proposed in
[CGandGameEngineLearner/goldbach-proofs#2318](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2318).
They are not under `lean/` and are **not** a submission. Once the entries appear in
`research/gaps.json` on the default branch, each file is intended to be copied to its gap
`file` path and submitted as a one-file PR.

| Gap id | Intended repository file | Theorem name |
|---|---|---|
| `L-goldbach-dyadic-sum-avoiding-mask` | `lean/PEqualNP/Outside/L_goldbach_dyadic_sum_avoiding_mask.lean` | `PEqualNP.Outside.L_goldbach_dyadic_sum_avoiding_mask` |
| `L-goldbach-dyadic-progression-countermodel` | `lean/PEqualNP/Outside/L_goldbach_dyadic_progression_countermodel.lean` | `PEqualNP.Outside.L_goldbach_dyadic_progression_countermodel` |

Each file imports only `Mathlib` and declares one theorem named after its module. The
countermodel file re-proves the mask construction internally, because the proposed gap's
`imports` list is empty.

## Local verification

- Lean `4.34.0-rc2` (x86_64-w64-windows-gnu), Mathlib
  `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- Both files pass the repository's `outside-guard.mjs imports` check (only `import Mathlib`,
  no forbidden token).
- For both files, `example : <the recorded statement> := <theorem>` closes, so the theorem
  type is definitionally equal to the statement in PR #2318's change-set.
- Both theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; there is no
  `sorry` or extra axiom.
- SHA256:
  - mask: `a433fa000d5cad9bd3afe0f32feefff64d0349095846ccf6c40704d9054374dd`
  - countermodel: `02f5b9768fd2fd73d398614a3bc0a72b94cc5be86dbcb7bb01274e5ae96a81ce`

The research desk's authoritative checker pins Lean `4.36.0` / Mathlib `fc4f59e5`.
These files have not yet been re-elaborated under that exact pinned toolchain on the
author's machine. They use only standard Mathlib lemmas and are expected to port; the
authoritative CI run after submission is the final check.
