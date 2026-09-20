# ACCEPTANCE — JSP-000527 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000527
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Exact original question (English)

> In higher-dimensional general position, is the number of points forcing a convex subset exponential in the target size?

The accepted resolution is PoZa22 (arXiv:2208.04878): \(ES_d(n)=2^{o(n)}\) for all \(d\ge 3\) — i.e. the forcing number is **sub**-exponential, not exponential.

## Required Lean theorem name(s) (FULL statement)

| Lean name | Intended statement |
|---|---|
| `es_three_subexponential` | \(ES_3(n)=2^{o(n)}\) (PoZa22 Theorem 1.1). |
| `convexSubset_forcing_points_exp` | For every \(d\ge 3\) and \(\varepsilon>0\), sufficiently large \(n\), every general-position set of size \(\ge 2^{\varepsilon n}\) in \(\mathbb{R}^d\) contains an \(n\)-point convex subset (\(=ES_d(n)=2^{o(n)}\)). |

**Not sufficient for prize_ready:** projection monotonicity alone, cups/caps lemmas alone, or \(d=3\) without the \(d\ge 3\) headline.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms` on headline theorem(s) shows only standard axioms
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators
- [ ] Named headline theorem(s) above exist and are proved

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named headline theorem(s) exist and are proved.
