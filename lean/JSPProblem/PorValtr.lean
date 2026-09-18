import JSPProblem.CupsCaps

/-!
# JSP-000527 — Theorem 2.2 (Pór–Valtr positive-fraction Erdős–Szekeres)

Given a `(k+1)`-cap or `(k+1)`-cup `P = {x₀,…,x_k}` sorted left-to-right,
its *support* is the collection of regions `T₁,…,T_k`, where `T_i` is the
region outside `conv P` bounded by the segment `x_i x_{i+1}` and by the lines
`x_{i-1}x_i` and `x_{i+1}x_{i+2}` (indices taken modulo `k+1` at the
endpoints).  We formalize a support region as an intersection of open
half-planes via the oriented-edge predicate `LeftOf`.

**Theorem 2.2 (Pór–Valtr).**  `X ⊆ ℝ²` in general position with distinct
`x`-coordinates, `|X| ≥ 2^{40k}` `⇒` there is a `(k+1)`-cap or `(k+1)`-cup
`P ⊆ X` with support regions `T₁,…,T_k` satisfying `|T_i ∩ X| ≥ |X| / 2^{40k}`,
and every `k`-tuple picking one point from each `T_i ∩ X` is in convex
position.
-/

noncomputable section

/-- The open half-plane strictly to the left of the directed edge `u → v`
(cross product of `v−u` with `p−u` positive). -/
def LeftOf (u v : Euc 2) : Set (Euc 2) :=
  {p | 0 < (v 0 - u 0) * (p 1 - u 1) - (v 1 - u 1) * (p 0 - u 0)}

/-- The open half-plane strictly to the right of the directed edge `u → v`. -/
def RightOf (u v : Euc 2) : Set (Euc 2) := LeftOf v u

/-- The support region of the edge `xᵢ xᵢ₊₁` in a left-to-right cap (`σ = true`)
or cup (`σ = false`), relative to the neighbouring vertices `l` (before `xᵢ`)
and `r` (after `xᵢ₊₁`): the intersection of the open half-plane across the
edge with the two open half-planes across the extended neighbouring edges. -/
def SupportRegion (l xᵢ xᵢ₁ r : Euc 2) (σ : Bool) : Set (Euc 2) :=
  (if σ then LeftOf xᵢ xᵢ₁ else RightOf xᵢ xᵢ₁) ∩
  (if σ then RightOf l xᵢ else LeftOf l xᵢ) ∩
  (if σ then LeftOf xᵢ₁ r else RightOf xᵢ₁ r)

/-- **Theorem 2.2 (Pór–Valtr).**  Paper item: Theorem 2.2 (the consequence of
`[PV02, Theorem 4]` recorded in Suk's paper).  The enumeration `x` is sorted by
first coordinate; `σ = true` gives a cap, `σ = false` a cup; the regions `T i`
are the support regions of the consecutive edges, with indices wrapped modulo
`k+1` at the two ends. -/
theorem porValtr_positiveFraction {k : ℕ} (hk : 3 ≤ k)
    {X : Finset (Euc 2)} (hX : InGeneralPosition (X : Set (Euc 2))) (hdx : DistinctX X)
    (hcard : 2 ^ (40 * k) ≤ X.card) :
    ∃ x : Fin (k + 1) → Euc 2, ∃ σ : Bool, ∃ T : Fin k → Set (Euc 2),
      (∀ i, x i ∈ X) ∧
      StrictMono (fun i ↦ (x i) 0) ∧
      (if σ then IsCap (Finset.image x Finset.univ)
             else IsCup (Finset.image x Finset.univ)) ∧
      (∀ i : Fin k,
        T i = SupportRegion
          (x ⟨(i.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩)
          (x ⟨i.val, by omega⟩)
          (x ⟨i.val + 1, by omega⟩)
          (x ⟨(i.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩) σ) ∧
      (∀ i : Fin k, 2 ^ (40 * k) * (T i ∩ (X : Set (Euc 2))).ncard ≥ X.card) ∧
      (∀ Y : Fin k → Euc 2, (∀ i, Y i ∈ T i ∩ (X : Set (Euc 2))) →
        InConvexPosition (Finset.image Y Finset.univ)) := by
  sorry

end
