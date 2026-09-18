import JSPProblem.Checkpoint

/-!
# JSP-000527 — Lemma 2.6 (discrete ham sandwich corollary)

**Lemma 2.6.**  For `1 ≤ r ≤ d` and arbitrary finite sets
`X₁,…,X_{d+1} ⊆ ℝ^d` there is a hyperplane `H` such that the closed half-space
`H⁺` contains at least half the points of each of `X₁,…,X_r` and `H⁻` at least
half of each of `X_{r+1},…,X_{d+1}`.

The proof applies the discrete ham-sandwich theorem to `X₁,…,X_d` and then
orients `H` so that `X_{d+1}` has at least half its points in `H⁺`.  The
underlying ham-sandwich theorem (Steinhaus–Banach–Stone–Tukey, via
Borsuk–Ulam) is the deepest missing prerequisite of this development.

A hyperplane is given as `{x | f x = c}` for a nonzero linear functional `f`;
`H⁺ = {x | c ≤ f x}`, `H⁻ = {x | f x ≤ c}`.
-/

noncomputable section

variable {d : ℕ}

/-- **Lemma 2.6 of the paper** (corollary of the discrete ham sandwich
theorem). -/
theorem hamSandwich_halves {r : ℕ}
    (X : Fin (d + 1) → Finset (Euc d)) :
    ∃ f : Euc d →ₗ[ℝ] ℝ, ∃ c : ℝ, f ≠ 0 ∧
      (∀ i : Fin (d + 1), i.val < r →
        2 * ((X i).filter (fun x ↦ c ≤ f x)).card ≥ (X i).card) ∧
      (∀ i : Fin (d + 1), r ≤ i.val →
        2 * ((X i).filter (fun x ↦ f x ≤ c)).card ≥ (X i).card) := by
  sorry

end
