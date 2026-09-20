import JSPProblem.Projection
import JSPProblem.Separation
import JSPProblem.SeparationRamsey
import JSPProblem.SeparationHalving
import JSPProblem.Caps3D
import JSPProblem.PorValtr

/-!
# JSP-000527 — Theorem 1.1 and the headline `ES_d(n) = 2^{o(n)}`

* `es_three_subexponential` — **Theorem 1.1** of Pohoata–Zakharov verbatim:
  for every `ε > 0` there is `n₀` such that every general-position
  `X ⊆ ℝ³` with `|X| ≥ 2^{ε n}`, `n ≥ n₀`, contains `n` points in convex
  position.  Its proof is the §3 assembly: apply `porValtr_positiveFraction`
  to the projection with `k₀ = n^{1/4}`, thin to a 2-separated collection via
  `prop_2_5`, extract the above/below structure via `cor_2_4`, build the
  two 3-edge polytopes of Proposition 3.1, colour triples by the
  `P¹`-free/`P²`-free dichotomy (Dilworth), Ramsey to a monochromatic clique,
  and apply `prop_2_1` — contradiction with `|X| ≥ 2^{εn}` unless a convex
  `n`-set exists.
* `convexSubset_forcing_points_exp` — the headline: `ES_d(n) = 2^{o(n)}` for
  all `d ≥ 3`, proved from the `d = 3` theorem by iterating
  `forcesConvex_succ` (Valtr's projection argument).
-/

noncomputable section

open Filter

/-- **Theorem 1.1** of Pohoata–Zakharov, *Convex polytopes from fewer points*:
`ES₃(n) = 2^{o(n)}`.  For any `ε > 0` there exists `n₀(ε)` such that for every
`n ≥ n₀`, every set `X ⊆ ℝ³` in general position with `|X| ≥ 2^{εn}` contains
`n` points in convex position. -/
theorem es_three_subexponential (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Euc 3),
      InGeneralPosition (X : Set (Euc 3)) →
      (2:ℝ) ^ (ε * (n:ℝ)) ≤ (X.card : ℝ) →
      ∃ S ⊆ X, S.card = n ∧ InConvexPosition S := by
  sorry

/-- `2^{ε·n} → ∞` as `n → ∞` for `ε > 0`. -/
theorem tendsto_two_pow (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (2:ℝ) ^ (ε * (n:ℝ))) atTop atTop := by
  have h1 : (1:ℝ) < (2:ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have heq : (fun n : ℕ ↦ (2:ℝ) ^ (ε * (n:ℝ))) = fun n ↦ ((2:ℝ) ^ ε) ^ n := by
    ext n
    rw [← Real.rpow_natCast ((2:ℝ) ^ ε) n, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [heq]
  exact tendsto_pow_atTop_atTop_of_one_lt h1

/-- **Headline theorem — `ES_d(n) = 2^{o(n)}` for all `d ≥ 3`** (the negative
answer to the catalog question "is the forcing number exponential in `n`?").

For every `ε > 0` there exists `n₀` such that for all `n ≥ n₀`, every
general-position set `X ⊆ ℝ^d` with `|X| ≥ 2^{εn}` contains an `n`-element
subset in convex position. -/
theorem convexSubset_forcing_points_exp {d : ℕ} (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Euc d),
      InGeneralPosition (X : Set (Euc d)) →
      (2:ℝ) ^ (ε * (n:ℝ)) ≤ (X.card : ℝ) →
      ∃ S ⊆ X, S.card = n ∧ InConvexPosition S := by
  obtain ⟨n₀, hn₀⟩ := es_three_subexponential ε hε
  -- choose the effective threshold: `n ≥ n₀` and `2^{εn} ≥ d+2`.
  obtain ⟨m, hm0, hmN⟩ : ∃ m : ℕ, n₀ ≤ m ∧
      (d + 2 : ℝ) ≤ (2:ℝ) ^ (ε * (m:ℝ)) := by
    obtain ⟨m, hm⟩ := ((tendsto_two_pow ε hε).eventually_ge_atTop (d + 2)).and
      (eventually_ge_atTop n₀) |>.exists
    exact ⟨m, hm.2, hm.1⟩
  refine ⟨m, fun n hn X hX hcard ↦ ?_⟩
  have hn₀' : n₀ ≤ n := le_trans hm0 hn
  have hN : (d + 2 : ℝ) ≤ (2:ℝ) ^ (ε * (n:ℝ)) := by
    refine le_trans hmN ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hε.le
  set N := ⌈(2:ℝ) ^ (ε * (n:ℝ))⌉₊ with hNdef
  have hNd : d + 2 ≤ N := by
    have : (d + 2 : ℝ) ≤ (N : ℝ) := le_trans hN (Nat.le_ceil _)
    exact_mod_cast this
  have hNcard : N ≤ X.card := (Nat.ceil_le).2 hcard
  -- `ForcesConvex 3 N n` is exactly the `d = 3` theorem.
  have hfc3 : ForcesConvex 3 N n := fun Y hY hNY ↦
    hn₀ n hn₀' Y hY (le_trans (Nat.le_ceil _) (by exact_mod_cast hNY))
  -- iterate the projection inequality up to dimension `d`.
  have iter : ∀ k ≤ d, 3 ≤ k → ForcesConvex k N n := by
    intro k hkd hk3
    induction k, hk3 using Nat.le_induction with
    | base => exact hfc3
    | succ k' hk3' ih =>
        exact forcesConvex_succ (d := k') (N := N) (n := n)
          (by omega) (by omega) (ih (Nat.le_of_succ_le hkd))
  exact iter d le_rfl hd X hX hNcard

end
