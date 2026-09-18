# ACCEPTANCE — JSP-000527 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000527
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md
- Catalog field `Eligible to claim` currently reads **No** for this entry;
  the checklist below is the technical gate regardless of eligibility status.

## Exact original question (English)

> In higher-dimensional general position, is the number of points forcing a
> convex subset exponential in the target size?

Catalog description matches the above. The accepted resolution is
`ES_d(n) = 2^{o(n)}` for all `d ≥ 3` (Pohoata–Zakharov, arXiv:2208.04878):
the forcing number grows **sub**-exponentially, disproving exponentiality.

## Required Lean theorem name(s) (FULL statement)

| Lean name | Intended statement |
|---|---|
| `convexSubset_forcing_points_exp` | For every `d ≥ 3` and every `ε > 0` there is `n₀` such that for all `n ≥ n₀`, every finite `X ⊆ ℝ^d` in general position with `|X| ≥ 2^{ε·n}` contains an `n`-element subset in convex position. (=`ES_d(n) = 2^{o(n)}` for all `d ≥ 3`.) |
| `es_three_subexponential` | The `d = 3` case above — Theorem 1.1 of the paper verbatim. |

Supporting (not sufficient alone): `forcingConvex_mono_dim` (the Valtr
projection inequality `ES_d ≤ ES_{d-1}`), and the named paper lemmas
`cupsCaps`, `porValtr_positiveFraction`, `kirchberger`, `hamSandwich_halves`,
`prop_2_1` … `prop_3_1`.

**Not sufficient for prize_ready:** any of the intermediate lemmas alone;
dimension `d = 3` alone without the `d ≥ 3` headline; a statement weakened to
fixed `ε` ranges or to sufficiently dense subsets only.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms` on headline theorem(s) shows only standard axioms
      (`propext`, `Classical.choice`, `Quot.sound`)
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators
- [ ] Named headline theorem(s) above exist and are proved

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named
headline theorem(s) exist and are proved.

`partial_ok` may be true for harness-green partial results (e.g. the
projection monotonicity alone); never treat as SUCCESS for the prize.
