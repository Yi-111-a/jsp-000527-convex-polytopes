import JSPProblem.Checkpoint

/-!
# JSP-000527 — Theorem 2.3 (Kirchberger)

`conv A ∩ conv B ≠ ∅` implies `conv A' ∩ conv B' ≠ ∅` for some `A' ⊆ A`,
`B' ⊆ B` with `|A'| + |B'| ≤ d+2`.

Proof via Carathéodory in `ℝ^{d+1}`: from `p ∈ conv A ∩ conv B` build
`0 ∈ conv Z` for `Z = {(a,1)} ∪ {(-b,-1)}`, take a `(d+2)`-element subset
`Z' ⊆ Z` still containing `0` in its hull, and read off the two coefficient
blocks; the last-coordinate balance forces equal total mass `t = 1/2` on each
side, so `(1/t) Σ α a = (1/t) Σ β b` is the common point.
-/

noncomputable section

variable {d : ℕ}

/-- Lift `x : ℝ^d` to `(x, 1) : ℝ^{d+1}`. -/
def liftUp (x : Euc d) : Euc (d + 1) := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) 1)

/-- Lift `x : ℝ^d` to `(−x, −1) : ℝ^{d+1}`. -/
def liftDown (x : Euc d) : Euc (d + 1) := -liftUp x

/-- **Theorem 2.3 (Kirchberger).** -/
theorem kirchberger {A B : Set (Euc d)}
    (h : (convexHull ℝ A ∩ convexHull ℝ B).Nonempty) :
    ∃ A' B' : Finset (Euc d),
      (A' : Set (Euc d)) ⊆ A ∧ (B' : Set (Euc d)) ⊆ B ∧
      A'.card + B'.card ≤ d + 2 ∧
      (convexHull ℝ (A' : Set (Euc d)) ∩ convexHull ℝ (B' : Set (Euc d))).Nonempty := by
  sorry

end
