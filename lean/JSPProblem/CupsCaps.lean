import JSPProblem.Checkpoint

/-!
# JSP-000527 — Theorem 2.1 (Erdős–Szekeres cups-vs-caps)

A `k`-cup (resp. `k`-cap) is a `k`-point set in convex position whose convex
hull is bounded from below (resp. above) by a single edge; equivalently every
point admits a non-vertical line through it with all other points strictly
above (resp. below).  The classical statement assumes pairwise distinct
first coordinates (recorded as `DistinctX`).

`f(a,b)`, the least `N` forcing an `a`-cup or a `b`-cap, equals
`(a+b-4 choose a-2) + 1`.  We only need the upper-bound direction.
-/

noncomputable section

/-- All points of `P` have pairwise distinct first coordinates — the usual
hypothesis of the cups–caps theorem. -/
def DistinctX (P : Finset (Euc 2)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p 0 = q 0 → p = q

/-- A cup: through every `p ∈ P` there is a non-vertical line
`y = a·x + b` having all other points of `P` strictly above it. -/
def IsCup (P : Finset (Euc 2)) : Prop :=
  ∀ p ∈ P, ∃ a b : ℝ, p 1 = a * p 0 + b ∧ ∀ q ∈ P, q ≠ p → q 1 > a * q 0 + b

/-- A cap: the mirror notion with all other points strictly below. -/
def IsCap (P : Finset (Euc 2)) : Prop :=
  ∀ p ∈ P, ∃ a b : ℝ, p 1 = a * p 0 + b ∧ ∀ q ∈ P, q ≠ p → q 1 < a * q 0 + b

/-- **Theorem 2.1 (cups vs caps).**  Any set of `(a+b-4 choose a-2)+1` points in
`ℝ²` in general position with distinct `x`-coordinates contains an `a`-cup or a
`b`-cap.  Paper item: Theorem 2.1 (Erdős–Szekeres 1935). -/
theorem cupsCaps {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    {X : Finset (Euc 2)} (hX : InGeneralPosition (X : Set _)) (hdx : DistinctX X)
    (hcard : (a + b - 4).choose (a - 2) + 1 ≤ X.card) :
    ∃ S ⊆ X, (S.card = a ∧ IsCup S) ∨ (S.card = b ∧ IsCap S) := by
  sorry

end
