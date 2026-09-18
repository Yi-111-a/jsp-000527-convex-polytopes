# JSP-000527 — In higher-dimensional general position, is the number of points forcing a convex subset exponential in the target size?

- **id:** JSP-000527
- **title:** In higher-dimensional general position, is the number of points forcing a convex subset exponential in the target size?
- **area:** Geometry / Convexity (discrete and computational geometry)
- **status:** Solved
- **Lean:** No (this repository is the formalization effort)
- **Eligible / Claim:** catalog lists `Eligible to claim: No` — see note below
- **role:** Formalization of the published solution

## Statement

Let `ES_d(n)` be the smallest integer such that **every** set of `ES_d(n)`
points in `ℝ^d` in general position contains `n` points in convex position.
Question (catalog): does `ES_d(n)` grow exponentially in `n` for `d ≥ 3`?

**Answer (Pohoata–Zakharov 2022): NO — `ES_d(n) = 2^{o(n)}` for every `d ≥ 3`.**

## Exact theorem being formalized

The headline target is the paper's main theorem together with the standard
dimension-monotonicity that lifts it to all `d ≥ 3`.

### Theorem 1.1 (Pohoata–Zakharov)

> For any `ε > 0` there exists `n₀(ε)` such that for every `n ≥ n₀(ε)`:
> if `X ⊂ ℝ³` is a set of points in general position with `|X| ≥ 2^{εn}`,
> then `X` contains `n` points in convex position. In other words,
> `ES₃(n) = 2^{o(n)}`.

### Dimension chain (Valtr's projection argument, eq. (1) of the paper)

> `ES_d(n) ≤ ES_{d-1}(n)` for every `d ≥ 3`: project a general-position set in
> `ℝ^d` onto a generic hyperplane, find a convex subset in the projection, and
> lift it back — the lift of a convex-position set along a generic projection is
> again in convex position.

Together: `ES_d(n) = 2^{o(n)}` for all `d ≥ 3`. This disproves the
Morris–Soltan prediction `ES_d(n) = Ω(2^{2n/d})` (and their conjectured
recurrence `ES_d(n) = 4·ES_d(n−d) − 3`).

## Definitions used in the formalization

- **General position** (paper): `X ⊂ ℝ^d`, `|X| ≥ d+1`, no `d+1` points of `X`
  lie on a common `(d−1)`-dimensional hyperplane.
  **Lean choice:** every `(d+1)`-element subset of `X` is affinely independent
  (`AffineIndependent`). This is the standard equivalence — `d+1` points lie on
  a hyperplane iff they are affinely dependent — and it avoids existential
  quantification over hyperplanes. A checkpoint lemma records the equivalence.
- **Convex position** (paper): the points of `P` are the vertices of a convex
  polytope.
  **Lean choice:** for a finite `S`, every `x ∈ S` satisfies
  `x ∉ convexHull ℝ (S ∖ {x})`. A checkpoint lemma connects this to
  `Set.extremePoints`/`convexHull` membership so the two readings coincide.

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000527
- Awards home: https://github.com/TheJustinSunPrize/awards
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Primary paper

- [PoZa22] Cosmin Pohoata, Dmitrii Zakharov, *Convex polytopes from fewer
  points*, arXiv:2208.04878 (2022). https://arxiv.org/abs/2208.04878

## Proof dependencies inside the paper (Section 2–3)

| Paper item | Content | Status in Mathlib (v4.34.0) |
|---|---|---|
| Thm 2.1 | cups-vs-caps: `f(a,b) = C(a+b-4, a-2) + 1` | not present |
| Thm 2.2 | Pór–Valtr positive-fraction Erdős–Szekeres in ℝ² | not present (deep) |
| Thm 2.3 | Kirchberger's theorem (`conv A ∩ conv B ≠ ∅` via `d+2` points) | derivable from `Convex.caratheodory` (present) |
| Lemma 2.6 | discrete ham-sandwich corollary | not present (needs Borsuk–Ulam) |
| Prop 2.1 | `P`-caps in ℝ³ via Dilworth + cups-caps | Dilworth not present |
| Prop 2.2–2.4 | above/below lemma via `R₄(k,k)` + Kirchberger | hypergraph Ramsey not present |
| Prop 2.5 | 2-separability via iterated Lemma 2.6 | depends on ham sandwich |
| Prop 2.7 | separable collections in convex position | needs Kirchberger + continuity |
| Prop 3.1 | 3-edge unbounded polytope construction | geometric, paper-specific |
| §3 | assembly: `k₀ = n^{1/4}`, Ramsey on 3-tuples, binomial bookkeeping | needs all of the above |

The full proof additionally invokes the four-colour theorem **only** for
Theorem 1.2 (the positive-fraction refinement), which is **out of scope** for
the catalog question — the headline here is Theorem 1.1 + the projection chain.

## Success criteria

- `lake build` succeeds
- `sorry` and `admit` counts are zero
- `#print axioms` on the headline theorem shows only the standard axioms
- final commit SHA (40 chars) and build evidence recorded

## Notes

This is a research-level formalization: two prerequisites (the discrete
ham-sandwich theorem and the Pór–Valtr positive-fraction theorem) are
themselves missing from Mathlib and constitute substantial independent
formalization projects. The repository is organised so that every remaining
`sorry` is a named lemma matching a numbered item of the paper.
