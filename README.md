# JSP-000527 — Convex polytopes from fewer points (Pohoata–Zakharov)

Formalization (Lean 4 + Mathlib) of the higher-dimensional Erdős–Szekeres
theorem:

> `ES_d(n) = 2^{o(n)}` for all `d ≥ 3` — in dimension ≥ 3, far fewer than
> exponentially many points in general position suffice to force `n` points in
> convex position.

Reference: Cosmin Pohoata, Dmitrii Zakharov, *Convex polytopes from fewer
points*, arXiv:2208.04878 (2022).

Catalog entry:
[JSP-000527](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000527).

## Status

`in_progress` — the statement layer, the projection monotonicity, and the
proof decomposition into named paper lemmas are in place. Remaining `sorry`s
correspond to named items of the paper (see `lean/JSPProblem/` module map and
`HARNESS_LOG.md`). Run `bash scripts/status.sh` for a structured summary and
`bash scripts/harness.sh` to re-verify.

## Build instructions

- Toolchain: `leanprover/lean4:v4.34.0`, pinned in `lean/lean-toolchain`
  (use `elan`; it installs the pinned toolchain automatically).
- Dependency: mathlib `v4.34.0` (`lean/lakefile.lean`).

```sh
cd lean
lake exe cache get   # download prebuilt mathlib oleans (first run only)
lake build
```

## Harness

```sh
bash scripts/harness.sh   # lake build + sorry count + #print axioms → HARNESS_LOG.md
bash scripts/status.sh    # structured JSON status
```

## Repository layout

- `PROBLEM.md` — precise statement of the result being formalized
- `ACCEPTANCE.md` — prize-ready checklist
- `SCOPE.md` — in/out of scope and interface decisions
- `formalization.yaml`, `acceptance.json`, `ATTRIBUTION.md` — metadata
- `lean/` — the Lean development
- `scripts/` — harness and status

## Module map (`lean/JSPProblem/`)

- `Defs.lean` — `InGeneralPosition`, `InConvexPosition`, `ForcesConvex`,
  2-separation, `C`-free / `C`-cap predicates.
- `Checkpoint.lean` — sanity lemmas validating the definitions (proved).
- `Projection.lean` — Valtr's lifting argument and
  `ForcesConvex (d-1) N n → ForcesConvex d N n`.
- `CupsCaps.lean` — Theorem 2.1 (Erdős–Szekeres cups-vs-caps).
- `PorValtr.lean` — Theorem 2.2 (positive-fraction Erdős–Szekeres in ℝ²).
- `Kirchberger.lean` — Theorem 2.3 (Kirchberger via Carathéodory).
- `HamSandwich.lean` — Lemma 2.6 (discrete ham sandwich corollary).
- `Separation.lean` — Props 2.2–2.7 (above/below, 2-separability).
- `Caps3D.lean` — Proposition 2.1 (`P`-caps via Dilworth + cups-caps).
- `MainTheorem.lean` — Proposition 3.1 and the §3 assembly;
  `es_three_subexponential` and `convexSubset_forcing_points_exp`.
