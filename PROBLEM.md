# JSP-000527 — In higher-dimensional general position, is the number of points forcing a convex subset exponential in the target size?

- **id:** JSP-000527
- **title:** In higher-dimensional general position, is the number of points forcing a convex subset exponential in the target size?
- **area:** Geometry / Convexity
- **status:** Solved
- **Lean:** No (formalization target)
- **Eligible / Claim:** No / Unavailable
- **role:** Formalize path (Solved + Lean=No)

## Statement

In higher-dimensional general position, is the number of points forcing a convex subset exponential in the target size?

Writing \(ES_d(n)\) for the Erdős–Szekeres function in \(\mathbb{R}^d\): is \(ES_d(n)\) exponential in \(n\) for \(d\ge 3\)?

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000527
- Awards home: https://github.com/TheJustinSunPrize/awards

## Primary papers

- [PoZa22] Convex polytopes from fewer points — arXiv:2208.04878 (2022). **Main formalization source.**

## Accepted mathematical answer

No — \(ES_d(n)=2^{o(n)}\) for all \(d\ge 3\) (Pohoata–Zakharov). In particular \(ES_3(n)=2^{o(n)}\), and higher dimensions follow by projection monotonicity.

## Success criteria

- `lake build` succeeds
- Zero `sorry` / `admit`
- Named headline theorem(s) in ACCEPTANCE.md proved
