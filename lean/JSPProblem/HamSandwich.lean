import JSPProblem.Checkpoint

/-!
# JSP-000527 — Lemma 2.6 (discrete ham sandwich corollary)

**Lemma 2.6.**  For `1 ≤ r ≤ d` and arbitrary finite sets
`X₁,…,X_{d+1} ⊆ ℝ^d` there is a hyperplane `H` such that the closed half-space
`H⁺` contains at least half the points of each of `X₁,…,X_r` and `H⁻` at least
half of each of `X_{r+1},…,X_{d+1}`.

A hyperplane is given as `{x | f x = c}` for a nonzero linear functional `f`;
`H⁺ = {x | c ≤ f x}`, `H⁻ = {x | f x ≤ c}`.

## Status of the proof in this development

* **`hamSandwich_halves` is false as stated for `d = 0`.**  `Euc 0` is a
  subsingleton, so every `f : Euc 0 →ₗ[ℝ] ℝ` is zero and `f ≠ 0` cannot hold
  (`not_exists_nonzero_linearMap_euc_zero`).  The statement needs `1 ≤ d`
  (the paper has `1 ≤ r ≤ d`, which forces `d ≥ 1`).

* For `1 ≤ d` the theorem is proved here modulo the **discrete ham sandwich
  theorem** `discrete_ham_sandwich` (bisect `d` finite sets in `ℝ^d` by one
  hyperplane): bisect `X₀,…,X_{d-1}` and orient `H` so that `X_d` has at least
  half its points in `H⁻`.  See `hamSandwich_halves'` for the reduction.

* `discrete_ham_sandwich` is the Stone–Tukey theorem for counting measures.
  Its standard proof applies Borsuk–Ulam to the median-hyperplane map
  `S^{d-1} → ℝ^{d-1}`; equivalently it is a parity/Tucker-lemma argument.
  Mathlib v4.34.0 has no Borsuk–Ulam, Tucker or Sperner lemma, so `d ≥ 4` is
  the precise topological blocker.  `d = 1` (a median cut) and `d = 2`
  (the "pancake" argument: two sets are bisected because their median
  intervals cannot be strictly separated in every direction — connectedness
  of `S¹`) are elementary; `d = 3` is proved below via the universal cover
  of `S¹` (`borsuk_ulam_odd_dim3`): an odd map `S¹ → S¹` has odd degree, so
  it cannot extend over the hemisphere.
-/

noncomputable section

variable {d : ℕ}

/-- For `d ≥ 1`, `Euc d` admits a nonzero linear functional (a coordinate
projection). -/
theorem exists_ne_zero_linearMap (hd : 1 ≤ d) :
    ∃ f : Euc d →ₗ[ℝ] ℝ, f ≠ 0 := by
  refine ⟨EuclideanSpace.projₗ ⟨0, hd⟩, ?_⟩
  intro h
  have := congrFun (congrArg DFunLike.coe h) (WithLp.toLp 2 fun _ : Fin d ↦ (1 : ℝ))
  simp at this

/-- `hamSandwich_halves` is literally false for `d = 0`: there is no nonzero
linear functional on the zero-dimensional space `Euc 0`. -/
theorem not_exists_nonzero_linearMap_euc_zero :
    ¬ ∃ f : Euc 0 →ₗ[ℝ] ℝ, ∃ _ : ℝ, f ≠ 0 := by
  rintro ⟨f, -, hf⟩
  apply hf
  ext x
  rw [Subsingleton.elim x 0]
  simp

/-- A uniform cutoff `c` disposes of the degenerate ranges `r = 0` (every set
needs a lower half) and `d + 1 ≤ r` (every set needs an upper half). -/
theorem hamSandwich_halves_trivial (hd : 1 ≤ d) {r : ℕ}
    (hr : r = 0 ∨ d + 1 ≤ r) (X : Fin (d + 1) → Finset (Euc d)) :
    ∃ f : Euc d →ₗ[ℝ] ℝ, ∃ c : ℝ, f ≠ 0 ∧
      (∀ i : Fin (d + 1), i.val < r →
        2 * ((X i).filter (fun x ↦ c ≤ f x)).card ≥ (X i).card) ∧
      (∀ i : Fin (d + 1), r ≤ i.val →
        2 * ((X i).filter (fun x ↦ f x ≤ c)).card ≥ (X i).card) := by
  classical
  obtain ⟨f₀, hf₀⟩ := exists_ne_zero_linearMap hd
  set U := Finset.univ.biUnion X with hU
  set B : ℝ := 1 + ∑ x ∈ U, |f₀ x| with hB
  have hBbound : ∀ x ∈ U, |f₀ x| < B := fun x hx ↦ by
    have hle : |f₀ x| ≤ ∑ y ∈ U, |f₀ y| :=
      Finset.single_le_sum (f := fun y ↦ |f₀ y|) (fun y _ ↦ abs_nonneg _) hx
    linarith
  rcases hr with rfl | hrr
  · -- r = 0: all sets take the lower half-space; `c = B` dominates everything.
    refine ⟨f₀, B, hf₀, fun i hi ↦ by omega, fun i _ ↦ ?_⟩
    have hflt : (X i).filter (fun x ↦ f₀ x ≤ B) = X i := by
      apply Finset.filter_true_of_mem
      intro x hx
      have hxU := hBbound x (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩)
      exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hxU)
    rw [hflt]
    omega
  · -- `d + 1 ≤ r`: all sets take the upper half-space; `c = -B` is below all.
    refine ⟨f₀, -B, hf₀, fun i _ ↦ ?_, fun i hi ↦ ?_⟩
    · have hflt : (X i).filter (fun x ↦ -B ≤ f₀ x) = X i := by
        apply Finset.filter_true_of_mem
        intro x hx
        have hxU := hBbound x (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩)
        have := neg_le_abs (f₀ x)
        linarith
      rw [hflt]
      omega
    · have hi' : i.val < d + 1 := i.isLt
      omega

/-! ### The discrete ham sandwich theorem, via Borsuk–Ulam

`discrete_ham_sandwich` is proved by reduction to `borsuk_ulam_odd`, the
"odd map" form of the Borsuk–Ulam theorem, which is the *only* place where
the topology enters.  `borsuk_ulam_odd` is proved for `d ≤ 3` (trivially for
`d = 1`, by the intermediate value theorem for `d = 2`, and via the
universal cover `Circle.exp : ℝ → Circle` for `d = 3`; see
`borsuk_ulam_odd_dim3`); the `d ≥ 4` case would need machinery absent from
mathlib v4.34.0.

The analytic workhorse is the *median interval* `[loMed s g, hiMed s g]` of
the values of `g : α → ℝ` on a finset `s`: the set of `c` such that both
closed halfspaces `{g ≤ c}` and `{c ≤ g}` contain at least half of `s`.
Both endpoints are order statistics, written in min–max form so that
continuity in `g` and the antipodal symmetry `loMed s (-g) = -hiMed s g`
are cheap. -/

section DiscreteHamSandwich

variable {α : Type*} [DecidableEq α]

/-- The lower endpoint of the *median interval* of the values of `g` on `s`:
the `⌈#s/2⌉`-th smallest value of `g x`, `x ∈ s`, expressed as the minimum
over all `⌈#s/2⌉`-element subsets `S ⊆ s` of `max_{x ∈ S} g x`.  The `if`
branches are junk values; the outer `powersetCard` is always nonempty here
since `⌈#s/2⌉ ≤ #s`. -/
noncomputable def loMed (s : Finset α) (g : α → ℝ) : ℝ :=
  if h : (s.powersetCard ((s.card + 1) / 2)).Nonempty then
    (s.powersetCard ((s.card + 1) / 2)).inf' h fun S ↦
      if hS : S.Nonempty then S.sup' hS g else 0
  else 0

/-- The upper endpoint of the median interval: the `⌈#s/2⌉`-th *largest*
value of `g` on `s`.  Defined as `- loMed s (-g)` so that the antipodal
symmetry is by definition. -/
noncomputable def hiMed (s : Finset α) (g : α → ℝ) : ℝ := -loMed s (-g)

omit [DecidableEq α] in
theorem powersetCard_mid_nonempty (s : Finset α) :
    (s.powersetCard ((s.card + 1) / 2)).Nonempty :=
  Finset.powersetCard_nonempty.mpr (by omega)

omit [DecidableEq α] in
theorem loMed_eq (s : Finset α) (g : α → ℝ) :
    loMed s g = (s.powersetCard ((s.card + 1) / 2)).inf'
      (powersetCard_mid_nonempty s) fun S ↦
        if hS : S.Nonempty then S.sup' hS g else 0 := by
  unfold loMed
  rw [dite_eq_left (powersetCard_mid_nonempty s)]

omit [DecidableEq α] in
/-- `c` is at least the lower median iff `s` contains `⌈#s/2⌉` points with
`g`-value `≤ c`. -/
theorem loMed_le_iff (hs : s.Nonempty) {g : α → ℝ} {c : ℝ} :
    loMed s g ≤ c ↔
      ∃ S ⊆ s, S.card = (s.card + 1) / 2 ∧ ∀ x ∈ S, g x ≤ c := by
  have hs0 : 0 < s.card := hs.card_pos
  rw [loMed_eq, Finset.inf'_le_iff]
  constructor
  · rintro ⟨S, hS, hSc⟩
    have hcard := (Finset.mem_powersetCard.mp hS).2
    have hSn : S.Nonempty := by rw [← Finset.card_pos, hcard]; omega
    rw [dite_eq_left hSn] at hSc
    exact ⟨S, (Finset.mem_powersetCard.mp hS).1, hcard, (Finset.sup'_le_iff hSn g).mp hSc⟩
  · rintro ⟨S, hsub, hcard, hle⟩
    have hSn : S.Nonempty := by rw [← Finset.card_pos, hcard]; omega
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, ?_⟩
    simp only [dite_eq_left hSn]
    exact Finset.sup'_le _ _ hle

omit [DecidableEq α] in
/-- `c` is at most the upper median iff `s` contains `⌈#s/2⌉` points with
`g`-value `≥ c`. -/
theorem le_hiMed_iff (hs : s.Nonempty) {g : α → ℝ} {c : ℝ} :
    c ≤ hiMed s g ↔
      ∃ S ⊆ s, S.card = (s.card + 1) / 2 ∧ ∀ x ∈ S, c ≤ g x := by
  rw [hiMed, le_neg, loMed_le_iff hs]
  refine exists_congr fun S ↦ and_congr_right fun _ ↦
    and_congr_right fun _ ↦ forall_congr' fun x ↦ forall_congr' fun _ ↦ ?_
  simp only [Pi.neg_apply, neg_le_neg_iff]

omit [DecidableEq α] in
/-- If `c` lies in the median interval of `g` on `s`, then each closed
halfspace `{g ≤ c}` and `{c ≤ g}` contains at least half of `s`. -/
theorem bisect_of_Icc (hs : s.Nonempty) {g : α → ℝ} {c : ℝ}
    (hlo : loMed s g ≤ c) (hhi : c ≤ hiMed s g) :
    s.card ≤ 2 * (s.filter fun x ↦ c ≤ g x).card ∧
      s.card ≤ 2 * (s.filter fun x ↦ g x ≤ c).card := by
  obtain ⟨S₁, hS₁sub, hS₁card, hS₁⟩ := (le_hiMed_iff hs).mp hhi
  obtain ⟨S₂, hS₂sub, hS₂card, hS₂⟩ := (loMed_le_iff hs).mp hlo
  have e1 : S₁ ⊆ s.filter (fun x ↦ c ≤ g x) :=
    fun x hx ↦ Finset.mem_filter.mpr ⟨hS₁sub hx, hS₁ x hx⟩
  have e2 : S₂ ⊆ s.filter (fun x ↦ g x ≤ c) :=
    fun x hx ↦ Finset.mem_filter.mpr ⟨hS₂sub hx, hS₂ x hx⟩
  have h1 := Finset.card_le_card e1
  have h2 := Finset.card_le_card e2
  omega

/-- The median interval is nonempty: `loMed s g ≤ hiMed s g`. -/
theorem loMed_le_hiMed (hs : s.Nonempty) (g : α → ℝ) :
    loMed s g ≤ hiMed s g := by
  have hs0 : 0 < s.card := hs.card_pos
  -- Fewer than `⌈#s/2⌉` points of `s` have `g`-value strictly below `loMed`.
  have hB : (s.filter fun x ↦ g x < loMed s g).card < (s.card + 1) / 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hlt
    have hTn : T.Nonempty := by rw [← Finset.card_pos, hTcard]; omega
    have hTlt : (if hT : T.Nonempty then T.sup' hT g else 0) < loMed s g := by
      rw [dite_eq_left hTn, Finset.sup'_lt_iff]
      intro x hx
      exact (Finset.mem_filter.mp (hTsub hx)).2
    rw [loMed_eq] at hTlt
    exact absurd hTlt (not_lt.mpr (Finset.inf'_le _ (Finset.mem_powersetCard.mpr
      ⟨fun x hx ↦ (Finset.mem_filter.mp (hTsub hx)).1, hTcard⟩)))
  -- Hence at least `⌈#s/2⌉` points satisfy `loMed ≤ g x`.
  have hC : (s.card + 1) / 2 ≤ (s.filter fun x ↦ loMed s g ≤ g x).card := by
    have hunion : s.filter (fun x ↦ g x < loMed s g) ∪
        s.filter (fun x ↦ loMed s g ≤ g x) = s := by
      rw [← Finset.filter_or]
      exact Finset.filter_true_of_mem fun x _ ↦ lt_or_ge _ _
    have hcard := hunion ▸ Finset.card_union_le
      (s.filter fun x ↦ g x < loMed s g) (s.filter fun x ↦ loMed s g ≤ g x)
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hC
  exact (le_hiMed_iff hs).mpr
    ⟨T, fun x hx ↦ (Finset.mem_filter.mp (hTsub hx)).1, hTcard,
      fun x hx ↦ (Finset.mem_filter.mp (hTsub hx)).2⟩

omit [DecidableEq α] in
/-- Antipodal symmetry of the median interval. -/
theorem loMed_neg (s : Finset α) (g : α → ℝ) :
    loMed s (-g) = -hiMed s g := by
  rw [hiMed, neg_neg]

omit [DecidableEq α] in
theorem hiMed_neg (s : Finset α) (g : α → ℝ) :
    hiMed s (-g) = -loMed s g := by
  rw [hiMed, neg_neg]

omit [DecidableEq α] in
/-- `loMed` is continuous in `g` (for `g` depending continuously on a
parameter): a finite min of finite maxes of continuous functions. -/
theorem continuous_loMed {ι : Type*} [TopologicalSpace ι] (s : Finset α)
    {g : ι → α → ℝ} (hg : ∀ x ∈ s, Continuous fun b ↦ g b x) :
    Continuous fun b ↦ loMed s (g b) := by
  simp only [loMed_eq]
  apply Continuous.finset_inf'_apply
  intro S hS
  by_cases hSn : S.Nonempty
  · simp only [dite_eq_left hSn]
    exact Continuous.finset_sup'_apply hSn fun x hx ↦
      hg x ((Finset.mem_powersetCard.mp hS).1 hx)
  · simp only [dite_eq_right hSn]
    exact continuous_const

omit [DecidableEq α] in
theorem continuous_hiMed {ι : Type*} [TopologicalSpace ι] (s : Finset α)
    {g : ι → α → ℝ} (hg : ∀ x ∈ s, Continuous fun b ↦ g b x) :
    Continuous fun b ↦ hiMed s (g b) := by
  simp only [hiMed]
  exact (continuous_loMed s fun x hx ↦ (hg x hx).neg).neg

end DiscreteHamSandwich

/-- The midpoint of the median interval of `s ⊆ Euc d` in direction `v`,
i.e. of the values `⟪v, x⟫` for `x ∈ s`. -/
noncomputable def medMid (s : Finset (Euc d)) (v : Euc d) : ℝ :=
  (loMed s ⇑(innerₗ (Euc d) v) + hiMed s ⇑(innerₗ (Euc d) v)) / 2

theorem medMid_continuous (s : Finset (Euc d)) : Continuous (medMid s) := by
  have hg : ∀ x ∈ s, Continuous fun v : Euc d ↦ innerₗ (Euc d) v x :=
    fun x _ ↦ continuous_inner.comp (continuous_id.prodMk continuous_const)
  show Continuous fun v ↦
    (loMed s ⇑(innerₗ (Euc d) v) + hiMed s ⇑(innerₗ (Euc d) v)) / 2
  exact ((continuous_loMed s hg).add (continuous_hiMed s hg)).div_const 2

/-- The median midpoint is an odd function of the direction. -/
theorem medMid_odd (s : Finset (Euc d)) (v : Euc d) :
    medMid s (-v) = -medMid s v := by
  have hgn : ⇑(innerₗ (Euc d) (-v)) = -⇑(innerₗ (Euc d) v) := by
    funext x
    rw [map_neg, LinearMap.neg_apply, Pi.neg_apply]
  unfold medMid
  rw [hgn, loMed_neg, hiMed_neg]
  ring

/-- Lift `j : Fin (d - 1)` to `Fin d` by the identity on values
(valid since `j.val < d - 1 ≤ d`). -/
private def finLift (d : ℕ) (j : Fin (d - 1)) : Fin d :=
  ⟨j.val, by have := j.isLt; omega⟩

/-! ### Borsuk–Ulam in dimension three

The `d = 3` case of `borsuk_ulam_odd` — a continuous odd map `S² → ℝ²` has a
zero — admits an elementary proof through the universal cover
`Circle.exp : ℝ → Circle`, which is carried out below.

Suppose `G : S² → ℝ²` is continuous, odd and nowhere zero, and write
`n v := G v / ‖G v‖ ∈ S¹`.  Pull back to the longitude–latitude plane by
`(θ, φ) ↦ (cos θ cos φ, sin θ cos φ, sin φ)` (a parametrisation of the
closed upper hemisphere for `φ ∈ [0, π/2]`): the resulting
`Ψ : ℝ × ℝ → Circle` satisfies `Ψ (θ + 2π, φ) = Ψ (θ, φ)`, the map
`θ ↦ Ψ (θ, π/2)` is constant (north pole), and oddness gives
`Ψ (θ + π, 0) = -Ψ (θ, 0)` on the equator.

Since `ℝ²` is simply connected, `Ψ` lifts along `Circle.exp` to a continuous
`Ψ̃ : ℝ × ℝ → ℝ` (`IsCoveringMap.existsUnique_continuousMap_lifts`).

* The continuous function `(θ, φ) ↦ Ψ̃ (θ + 2π, φ) - Ψ̃ (θ, φ)` takes values
  in the discrete fibre `exp ⁻¹ {1}`, hence is constant; at `φ = π/2` it is
  `0` because `θ ↦ Ψ̃ (θ, π/2)` lifts a constant map.  Thus
  `Ψ̃ (θ + 2π, 0) = Ψ̃ (θ, 0)`: the equatorial lift is periodic, i.e. the
  equatorial map has degree `0`.
* Oddness gives `Circle.exp (Ψ̃ (θ + π, 0) - Ψ̃ (θ, 0)) = Circle.exp π`, a
  constant value, so `Ψ̃ (θ + π, 0) - Ψ̃ (θ, 0)` is a constant `c`; iterating
  twice, `Ψ̃ (θ + 2π, 0) = Ψ̃ (θ, 0) + 2c`.  Combined with the periodicity
  this forces `c = 0`, hence `Circle.exp π = 1`, contradicting
  `Circle.exp_pi_ne_one`.  (In other words the equatorial map has *odd*
  degree.)

The constancy statements all use `IsCoveringMap.const_of_comp`: a lift of a
constant map out of a preconnected space is constant. -/

/-- The point of `S² ⊆ ℝ³` with longitude `θ` and latitude `φ`
(equator `φ = 0`, north pole `φ = π / 2`). -/
private noncomputable def spherePt (θ φ : ℝ) : Euc 3 :=
  WithLp.toLp 2 ![Real.cos θ * Real.cos φ, Real.sin θ * Real.cos φ, Real.sin φ]

private theorem norm_spherePt (θ φ : ℝ) : ‖spherePt θ φ‖ = 1 := by
  have key : (Real.cos θ * Real.cos φ) ^ 2 + (Real.sin θ * Real.cos φ) ^ 2 +
      Real.sin φ ^ 2 = 1 := by
    have h1 := Real.cos_sq_add_sin_sq θ
    have h2 := Real.cos_sq_add_sin_sq φ
    nlinarith
  show ‖WithLp.toLp 2 ![Real.cos θ * Real.cos φ, Real.sin θ * Real.cos φ,
      Real.sin φ]‖ = 1
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Real.norm_eq_abs,
    sq_abs]
  rw [key, Real.sqrt_one]

private theorem continuous_spherePt :
    Continuous fun p : ℝ × ℝ ↦ spherePt p.1 p.2 := by
  apply (PiLp.continuous_toLp 2 _).comp
  rw [continuous_pi_iff]
  intro i
  fin_cases i
  · show Continuous fun p : ℝ × ℝ ↦ Real.cos p.1 * Real.cos p.2
    fun_prop
  · show Continuous fun p : ℝ × ℝ ↦ Real.sin p.1 * Real.cos p.2
    fun_prop
  · show Continuous fun p : ℝ × ℝ ↦ Real.sin p.2
    fun_prop

/-- `spherePt` as a map into the unit sphere of `ℝ³`. -/
private noncomputable def sphereParam (θ φ : ℝ) : Metric.sphere (0 : Euc 3) 1 :=
  ⟨spherePt θ φ, mem_sphere_zero_iff_norm.mpr (norm_spherePt θ φ)⟩

private theorem continuous_sphereParam :
    Continuous fun p : ℝ × ℝ ↦ sphereParam p.1 p.2 :=
  Continuous.subtype_mk continuous_spherePt _

/-- The combined complex-valued map `v ↦ F₀ v + i·F₁ v`. -/
private noncomputable def N₃ (F : Fin 2 → Euc 3 → ℝ) (v : Euc 3) : ℂ :=
  (F 0 v : ℂ) + (F 1 v) * Complex.I

private theorem continuous_N₃ (F : Fin 2 → Euc 3 → ℝ)
    (hF : ∀ i, Continuous (F i)) : Continuous fun v ↦ N₃ F v :=
  (Complex.continuous_ofReal.comp (hF 0)).add
    ((Complex.continuous_ofReal.comp (hF 1)).mul continuous_const)

private theorem N₃_neg (F : Fin 2 → Euc 3 → ℝ)
    (hodd : ∀ i, ∀ v ∈ Metric.sphere (0 : Euc 3) 1, F i (-v) = -F i v)
    {v : Euc 3} (hv : v ∈ Metric.sphere (0 : Euc 3) 1) :
    N₃ F (-v) = -N₃ F v := by
  simp only [N₃, hodd 0 v hv, hodd 1 v hv]
  push_cast
  ring

/-- A nonzero complex number normalised to unit modulus lies in the unit
sphere — i.e. is an element of `Circle`. -/
private theorem norm_div_self_mem {z : ℂ} (hz : z ≠ 0) :
    z / (‖z‖ : ℂ) ∈ Submonoid.unitSphere ℂ := by
  show z / (‖z‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
  rw [mem_sphere_zero_iff_norm]
  have h0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self h0]

/-- The normalization `v ↦ N₃ F v / ‖N₃ F v‖` of an odd `F` that never
vanishes on `S²`, as a map `S² → Circle`. -/
private noncomputable def circMap (F : Fin 2 → Euc 3 → ℝ)
    (hNne : ∀ v ∈ Metric.sphere (0 : Euc 3) 1, N₃ F v ≠ 0) :
    Metric.sphere (0 : Euc 3) 1 → Circle :=
  fun v ↦ ⟨N₃ F v / (‖N₃ F v‖ : ℂ), norm_div_self_mem (hNne v v.2)⟩

private theorem circMap_continuous (F : Fin 2 → Euc 3 → ℝ)
    (hF : ∀ i, Continuous (F i))
    (hNne : ∀ v ∈ Metric.sphere (0 : Euc 3) 1, N₃ F v ≠ 0) :
    Continuous (circMap F hNne) :=
  Continuous.subtype_mk
    (((continuous_N₃ F hF).comp continuous_subtype_val).div
      (Complex.continuous_ofReal.comp
        (((continuous_N₃ F hF).comp continuous_subtype_val).norm))
      fun v ↦ by simp [hNne v v.2])
    fun v ↦ norm_div_self_mem (z := N₃ F (v : Euc 3)) (hNne v v.2)

/-- The pull-back of `circMap F` to the longitude–latitude plane
`ℝ × ℝ ∋ (θ, φ) ↦ (cos θ cos φ, sin θ cos φ, sin φ)`. -/
private noncomputable def hemiMap (F : Fin 2 → Euc 3 → ℝ)
    (hF : ∀ i, Continuous (F i))
    (hNne : ∀ v ∈ Metric.sphere (0 : Euc 3) 1, N₃ F v ≠ 0) :
    C(ℝ × ℝ, Circle) :=
  ⟨fun p ↦ circMap F hNne (sphereParam p.1 p.2),
    (circMap_continuous F hF hNne).comp continuous_sphereParam⟩

/-- **Borsuk–Ulam for odd maps `S² → ℝ²`.**  Proved via the universal cover
`Circle.exp : ℝ → Circle`: a nonvanishing odd map would give a lift
`Ψ̃ : ℝ² → ℝ` of the hemispheric pull-back that is simultaneously
`2π`-periodic in `θ` (the pole is a point) and satisfies
`Ψ̃ (θ + π, 0) = Ψ̃ (θ, 0) + c` with `Circle.exp c = Circle.exp π`; together
these force `Circle.exp π = 1`, contradiction.  This is the classical
argument that an odd map `S¹ → S¹` has odd degree, applied to the equator
of `S²`. -/
theorem borsuk_ulam_odd_dim3 (F : Fin 2 → Euc 3 → ℝ)
    (hF : ∀ i, Continuous (F i))
    (hodd : ∀ i, ∀ v ∈ Metric.sphere (0 : Euc 3) 1, F i (-v) = -F i v) :
    ∃ v ∈ Metric.sphere (0 : Euc 3) 1, ∀ i, F i v = 0 := by
  by_contra hcon
  -- `N₃ F` does not vanish on `S²` under the contrary assumption.
  have hNne : ∀ v ∈ Metric.sphere (0 : Euc 3) 1, N₃ F v ≠ 0 := by
    intro v hv hNv
    apply hcon
    have hre : F 0 v = 0 := by
      have h := congrArg Complex.re hNv
      simpa [N₃] using h
    have him : F 1 v = 0 := by
      have h := congrArg Complex.im hNv
      simpa [N₃] using h
    exact ⟨v, hv, Fin.forall_fin_two.mpr ⟨hre, him⟩⟩
  -- Unfolding equations for the subtype values.
  have hΨapp : ∀ θ φ : ℝ, hemiMap F hF hNne (θ, φ) =
      circMap F hNne (sphereParam θ φ) := fun _ _ ↦ rfl
  have hcirc : ∀ θ φ : ℝ, (circMap F hNne (sphereParam θ φ) : ℂ) =
      N₃ F (spherePt θ φ) / (‖N₃ F (spherePt θ φ)‖ : ℂ) := fun _ _ ↦ rfl
  -- The lift `Ψ̃ : ℝ² → ℝ` of `hemiMap` through `Circle.exp`.
  obtain ⟨Ψl, ⟨-, hcomp⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      (hemiMap F hF hNne) (0, 0)
      (Complex.arg (hemiMap F hF hNne (0, 0) : ℂ)) (Circle.exp_arg _)
  have hlift : ∀ p : ℝ × ℝ, Circle.exp (Ψl p) = hemiMap F hF hNne p :=
    fun p ↦ congrFun hcomp p
  -- Periodicity of `Ψ` in `θ`.
  have hΨper : ∀ θ φ : ℝ, hemiMap F hF hNne (θ + 2 * Real.pi, φ) =
      hemiMap F hF hNne (θ, φ) := by
    intro θ φ
    have hsp : spherePt (θ + 2 * Real.pi) φ = spherePt θ φ := by
      simp only [spherePt, Real.cos_add_two_pi, Real.sin_add_two_pi]
    rw [hΨapp, hΨapp,
      show sphereParam (θ + 2 * Real.pi) φ = sphereParam θ φ from
        Subtype.ext hsp]
  -- `Ψ` is constant in `θ` at the north pole.
  have hΨpole : ∀ θ : ℝ, hemiMap F hF hNne (θ, Real.pi / 2) =
      hemiMap F hF hNne (0, Real.pi / 2) := by
    intro θ
    have hsp : spherePt θ (Real.pi / 2) = spherePt 0 (Real.pi / 2) := by
      simp only [spherePt, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ext i
      fin_cases i <;> simp
    rw [hΨapp, hΨapp,
      show sphereParam θ (Real.pi / 2) = sphereParam 0 (Real.pi / 2) from
        Subtype.ext hsp]
  -- Oddness of `Ψ` on the equator.
  have hΨodd : ∀ θ : ℝ, hemiMap F hF hNne (θ + Real.pi, 0) =
      hemiMap F hF hNne (θ, 0) * Circle.exp Real.pi := by
    intro θ
    have hsp : spherePt (θ + Real.pi) 0 = -spherePt θ 0 := by
      simp only [spherePt, Real.cos_add_pi, Real.sin_add_pi]
      ext i
      fin_cases i <;> simp [PiLp.neg_apply]
    apply Circle.ext
    rw [Circle.coe_mul, Circle.coe_exp, Complex.exp_pi_mul_I, hΨapp, hΨapp,
      hcirc, hcirc, hsp,
      N₃_neg F hodd (mem_sphere_zero_iff_norm.mpr (norm_spherePt θ 0)),
      norm_neg, div_eq_mul_inv, div_eq_mul_inv]
    ring
  -- `θ ↦ Ψ̃ (θ, π/2)` lifts a constant map, hence is constant.
  have hT : ∀ θ θ' : ℝ, Ψl (θ, Real.pi / 2) = Ψl (θ', Real.pi / 2) := by
    intro θ θ'
    exact Circle.isCoveringMap_exp.const_of_comp
      (Ψl.continuous.comp
        (Continuous.prodMk continuous_id continuous_const))
      (fun a b ↦ by
        show Circle.exp (Ψl (a, Real.pi / 2)) = Circle.exp (Ψl (b, Real.pi / 2))
        rw [hlift, hlift, hΨpole a, hΨpole b])
      θ θ'
  -- The `2π`-displacement of `Ψ̃` is constant on `ℝ²` …
  have hD : ∀ θ φ : ℝ, Ψl (θ + 2 * Real.pi, φ) - Ψl (θ, φ) =
      Ψl (0 + 2 * Real.pi, Real.pi / 2) - Ψl (0, Real.pi / 2) := by
    intro θ φ
    refine Circle.isCoveringMap_exp.const_of_comp
      (g := fun p : ℝ × ℝ ↦ Ψl (p.1 + 2 * Real.pi, p.2) - Ψl p)
      ((Ψl.continuous.comp (Continuous.prodMk
        (continuous_fst.add continuous_const) continuous_snd)).sub
        Ψl.continuous)
      ?_ (θ, φ) (0, Real.pi / 2)
    intro a b
    have h1 : ∀ x : ℝ × ℝ,
        Circle.exp (Ψl (x.1 + 2 * Real.pi, x.2) - Ψl x) = 1 := fun x ↦ by
      rw [Circle.exp_sub, hlift, hlift, hΨper x.1 x.2]
      show hemiMap F hF hNne (x.1, x.2) / hemiMap F hF hNne x = 1
      rw [Prod.mk.eta]
      exact div_self' _
    rw [h1 a, h1 b]
  -- … and it vanishes at the pole, so `Ψ̃` is `2π`-periodic in `θ`.
  have hDzero : ∀ θ : ℝ, Ψl (θ + 2 * Real.pi, 0) = Ψl (θ, 0) := by
    intro θ
    have h := hD θ 0
    rw [sub_eq_zero.mpr (hT _ 0)] at h
    exact sub_eq_zero.mp h
  -- `θ ↦ Ψ̃ (θ + π, 0) - Ψ̃ (θ, 0)` is constant, with `exp`-image `exp π`.
  have hJexp : ∀ t : ℝ,
      Circle.exp (Ψl (t + Real.pi, 0) - Ψl (t, 0)) = Circle.exp Real.pi := by
    intro t
    rw [Circle.exp_sub, hlift, hlift, hΨodd, mul_div_cancel_left]
  have hJ : ∀ θ θ' : ℝ, Ψl (θ + Real.pi, 0) - Ψl (θ, 0) =
      Ψl (θ' + Real.pi, 0) - Ψl (θ', 0) := by
    intro θ θ'
    exact Circle.isCoveringMap_exp.const_of_comp
      ((Ψl.continuous.comp (Continuous.prodMk (continuous_id.add continuous_const)
        continuous_const)).sub
        (Ψl.continuous.comp (Continuous.prodMk continuous_id continuous_const)))
      (fun a b ↦ by
        show Circle.exp (Ψl (a + Real.pi, 0) - Ψl (a, 0)) =
          Circle.exp (Ψl (b + Real.pi, 0) - Ψl (b, 0))
        rw [hJexp a, hJexp b])
      θ θ'
  -- Combining: `Ψl (0,0) + 2c = Ψl (0,0)` gives `c = 0` and `exp π = 1`.
  have h2pi : (0 : ℝ) + 2 * Real.pi = Real.pi + Real.pi := by ring
  have hper : Ψl (Real.pi + Real.pi, 0) = Ψl (0, 0) := by
    have := hDzero 0
    rwa [h2pi] at this
  have hc : Ψl (Real.pi, 0) - Ψl (0, 0) = 0 := by
    have hJp0 : Ψl (Real.pi + Real.pi, 0) - Ψl (Real.pi, 0) =
        Ψl (0 + Real.pi, 0) - Ψl (0, 0) := hJ Real.pi 0
    rw [zero_add, hper] at hJp0
    linarith
  have hfin := hJexp 0
  rw [zero_add, hc, Circle.exp_zero] at hfin
  exact Circle.exp_pi_ne_one hfin.symm

/-- **Borsuk–Ulam theorem** in the odd-map form needed for the ham sandwich
theorem: `d - 1` continuous real functions on `Euc d`, each odd on the unit
sphere, have a common zero on the sphere.

This is equivalent to the usual statement that a continuous odd map
`S^{d-1} → ℝ^{d-1}` vanishes somewhere, and it is the *entire* topological
content of `discrete_ham_sandwich`.  Mathlib v4.34.0 contains neither
Borsuk–Ulam nor any of its standard substitutes (Tucker's lemma, the
topological Sperner lemma, the noncontractibility of spheres), so the
`4 ≤ d` case is out of reach here.

* `d = 1`: vacuous — there are no conditions and the sphere is nonempty.
* `d = 2`: a continuous odd `F : S¹ → ℝ` vanishes by the intermediate value
  theorem along the semicircle `θ ↦ (cos θ, sin θ)`, since
  `F(θ + Real.pi) = -F(θ)`.
* `d = 3`: proved in full (`borsuk_ulam_odd_dim3`) via the universal cover
  `Circle.exp : ℝ → Circle`, using the fact that the equatorial odd map
  `S¹ → S¹` lifts to a `Ψ̃ : ℝ → ℝ` with `Ψ̃ (θ + π) = Ψ̃ θ + c`,
  `Circle.exp c = Circle.exp π` — i.e. odd maps `S¹ → S¹` have odd degree.

The statement is restricted to `d ≤ 3`, which is all this development needs
(the paper's Lemma 2.6 is only applied in `ℝ³`); the `d ≥ 4` case is genuine
higher-dimensional Borsuk–Ulam and needs sphere homology / Tucker-type
combinatorics not present in mathlib v4.34.0. -/
theorem borsuk_ulam_odd {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (F : Fin (d - 1) → Euc d → ℝ)
    (hF : ∀ i, Continuous (F i))
    (hodd : ∀ i, ∀ v ∈ Metric.sphere (0 : Euc d) 1, F i (-v) = -F i v) :
    ∃ v ∈ Metric.sphere (0 : Euc d) 1, ∀ i, F i v = 0 := by
  rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl
  · -- `d = 1`: no conditions at all; take any unit vector.
    refine ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, ?_, fun i ↦ i.elim0⟩
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]
  · -- `d = 2`: intermediate value theorem on the semicircle `θ ∈ [0, Real.pi]`.
    have hmem : ∀ θ : ℝ,
        (WithLp.toLp 2 ![Real.cos θ, Real.sin θ] : Euc 2) ∈
          Metric.sphere (0 : Euc 2) 1 := by
      intro θ
      rw [mem_sphere_zero_iff_norm, PiLp.norm_eq_of_L2]
      simp [Fin.sum_univ_two, Real.cos_sq_add_sin_sq]
    have hneg : ∀ θ : ℝ,
        (WithLp.toLp 2 ![Real.cos (θ + Real.pi), Real.sin (θ + Real.pi)] : Euc 2) =
          -WithLp.toLp 2 ![Real.cos θ, Real.sin θ] := by
      intro θ
      ext i
      fin_cases i <;>
        simp [PiLp.neg_apply, Real.cos_add_pi, Real.sin_add_pi]
    have hcont : Continuous fun θ : ℝ ↦
        F ⟨0, by omega⟩ (WithLp.toLp 2 ![Real.cos θ, Real.sin θ]) := by
      apply (hF _).comp
      apply (PiLp.continuous_toLp 2 _).comp
      rw [continuous_pi_iff]
      intro i
      fin_cases i
      · simpa using Real.continuous_cos
      · simpa using Real.continuous_sin
    have hodd' : ∀ θ : ℝ,
        F ⟨0, by omega⟩ (WithLp.toLp 2 ![Real.cos (θ + Real.pi), Real.sin (θ + Real.pi)]) =
          -F ⟨0, by omega⟩ (WithLp.toLp 2 ![Real.cos θ, Real.sin θ]) := by
      intro θ
      rw [hneg θ]
      exact hodd _ _ (hmem θ)
    have hReal.pi : F ⟨0, by omega⟩ (WithLp.toLp 2 ![Real.cos Real.pi, Real.sin Real.pi]) =
        -F ⟨0, by omega⟩ (WithLp.toLp 2 ![Real.cos 0, Real.sin 0]) := by
      have := hodd' 0
      rwa [zero_add] at this
    obtain ⟨θ, -, hθ⟩ : ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi,
        F ⟨0, by omega⟩ (WithLp.toLp 2 ![Real.cos θ, Real.sin θ]) = 0 := by
      rcases le_or_gt (F ⟨0, by omega⟩
          (WithLp.toLp 2 ![Real.cos 0, Real.sin 0])) 0 with h0 | h0
      · exact intermediate_value_Icc Real.pi_nonneg hcont.continuousOn
          (Set.mem_Icc.mpr ⟨h0, by linarith⟩)
      · exact intermediate_value_Icc' Real.pi_nonneg hcont.continuousOn
          (Set.mem_Icc.mpr ⟨by linarith, h0.le⟩)
    refine ⟨_, hmem θ, fun j ↦ ?_⟩
    have : j = ⟨0, by omega⟩ := Fin.ext (by have := j.isLt; omega)
    rw [this]
    exact hθ
  · -- `d = 3`: proved above via the universal cover of the circle.
    exact borsuk_ulam_odd_dim3 F hF hodd

/-- **Discrete ham sandwich theorem** (Stone–Tukey for counting measures):
any `d` finite subsets of `ℝ^d` are simultaneously bisected by a hyperplane
`{x | f x = c}` — each closed halfspace contains at least half of each set.

**Proof.**  For each direction `v` on the unit sphere let `m_i(v)` be the
midpoint of the median interval of the values `⟪v, x⟫`, `x ∈ X_i`; then
`m_i(-v) = -m_i(v)` and `m_i` is continuous (`medMid_continuous`,
`medMid_odd`).  By `borsuk_ulam_odd` applied to the `d - 1` differences
`m_i - m_{i₀}` there is a `v` on the sphere with all `m_i(v)` equal to a
common value `c`, which then lies in every median interval and bisects every
nonempty `X_i` (`bisect_of_Icc`); empty sets are bisected trivially.

The theorem is stated for `d ≤ 3` since `borsuk_ulam_odd` is proved in that
range (the `d = 3` case via `borsuk_ulam_odd_dim3`); it is only applied at
`d = 3` below. -/
theorem discrete_ham_sandwich {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (X : Fin d → Finset (Euc d)) :
    ∃ f : Euc d →ₗ[ℝ] ℝ, ∃ c : ℝ, f ≠ 0 ∧ ∀ i : Fin d,
      2 * ((X i).filter (fun x ↦ c ≤ f x)).card ≥ (X i).card ∧
      2 * ((X i).filter (fun x ↦ f x ≤ c)).card ≥ (X i).card := by
  classical
  set i₀ : Fin d := ⟨d - 1, by omega⟩ with hi₀
  obtain ⟨v, hv, hFv⟩ := borsuk_ulam_odd hd hd3
    (fun j v ↦ medMid (X (finLift d j)) v - medMid (X i₀) v)
    (fun _ ↦ (medMid_continuous _).sub (medMid_continuous _))
    (fun j v _ ↦ by
      show medMid (X (finLift d j)) (-v) - medMid (X i₀) (-v) =
        -(medMid (X (finLift d j)) v - medMid (X i₀) v)
      rw [medMid_odd, medMid_odd]
      ring)
  -- `c` is the common value of all median midpoints at `v`.
  have hmc : ∀ i : Fin d, medMid (X i) v = medMid (X i₀) v := by
    intro i
    by_cases hii : i = i₀
    · rw [hii]
    · have hlt : i.val < d - 1 := by
        have hiv : i.val ≠ d - 1 := fun h ↦ hii (Fin.ext h)
        have := i.isLt
        omega
      have hzero := sub_eq_zero.mp (hFv ⟨i.val, hlt⟩)
      have hae : finLift d ⟨i.val, hlt⟩ = i := Fin.ext rfl
      rwa [hae] at hzero
  refine ⟨innerₗ (Euc d) v, medMid (X i₀) v, ?_, fun i ↦ ?_⟩
  · -- `⟪v, ·⟫ ≠ 0` since `⟪v, v⟫ = ‖v‖² = 1`.
    intro hzero
    have hvv : innerₗ (Euc d) v v = 1 := by
      simp only [innerₗ_apply_apply, real_inner_self_eq_norm_sq,
        mem_sphere_zero_iff_norm.mp hv, one_pow]
    rw [hzero] at hvv
    simp at hvv
  · by_cases hs : (X i).Nonempty
    · -- `c = m_i(v)` lies in the median interval of `X i`.
      rw [← hmc i]
      have hle := loMed_le_hiMed hs ⇑(innerₗ (Euc d) v)
      have hmem : loMed (X i) ⇑(innerₗ (Euc d) v) ≤ medMid (X i) v ∧
          medMid (X i) v ≤ hiMed (X i) ⇑(innerₗ (Euc d) v) := by
        simp only [medMid]
        constructor <;> linarith
      exact bisect_of_Icc hs hmem.1 hmem.2
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp

/-- **Lemma 2.6 of the paper** for `1 ≤ d ≤ 3`, reduced to the discrete ham
sandwich theorem: bisect `X₀,…,X_{d-1}` and orient `H` so that `X_d` has at
least half its points in `H⁻` (a bisected set has ≥ half on *both* sides, so
the `r`-split of the first `d` sets is unaffected by the flip). -/
theorem hamSandwich_halves' (hd : 1 ≤ d) (hd3 : d ≤ 3) {r : ℕ}
    (X : Fin (d + 1) → Finset (Euc d)) :
    ∃ f : Euc d →ₗ[ℝ] ℝ, ∃ c : ℝ, f ≠ 0 ∧
      (∀ i : Fin (d + 1), i.val < r →
        2 * ((X i).filter (fun x ↦ c ≤ f x)).card ≥ (X i).card) ∧
      (∀ i : Fin (d + 1), r ≤ i.val →
        2 * ((X i).filter (fun x ↦ f x ≤ c)).card ≥ (X i).card) := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · exact hamSandwich_halves_trivial hd (Or.inl rfl) X
  rcases lt_or_ge r (d + 1) with hrr | hrr
  swap
  · exact hamSandwich_halves_trivial hd (Or.inr hrr) X
  -- `1 ≤ r ≤ d`: bisect the first `d` sets, then orient for `X_d`.
  obtain ⟨f, c, hf, hbis⟩ :=
    discrete_ham_sandwich hd hd3 (fun j : Fin d ↦ X j.castSucc)
  set A := (X (Fin.last d)).filter (fun x ↦ c ≤ f x) with hA
  set Bs := (X (Fin.last d)).filter (fun x ↦ f x ≤ c) with hBs
  have hAB : X (Fin.last d) = A ∪ Bs := by
    rw [hA, hBs, ← Finset.filter_or]
    symm
    apply Finset.filter_true_of_mem
    intro x _
    exact le_total c (f x)
  have hcard : (X (Fin.last d)).card ≤ A.card + Bs.card := by
    rw [hAB]
    exact Finset.card_union_le A Bs
  rcases le_or_gt ((X (Fin.last d)).card) (2 * Bs.card) with hlast | hlast
  · -- `X_d` already has ≥ half in `{f ≤ c}`: keep `(f, c)`.
    refine ⟨f, c, hf, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact (hbis j).1
      · rw [Fin.val_last] at hi
        omega
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact (hbis j).2
      · exact hlast
  · -- `X_d` has > half in `{f ≥ c}`: flip orientation to `(−f, −c)`.
    have hlast' : (X (Fin.last d)).card ≤ 2 * A.card := by omega
    refine ⟨-f, -c, neg_ne_zero.2 hf, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have e : (X j.castSucc).filter (fun x ↦ -c ≤ (-f) x) =
            (X j.castSucc).filter (fun x ↦ f x ≤ c) := by
          apply Finset.filter_congr
          intro x _
          simp [LinearMap.neg_apply]
        rw [e]
        exact (hbis j).2
      · rw [Fin.val_last] at hi
        omega
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have e : (X j.castSucc).filter (fun x ↦ (-f) x ≤ -c) =
            (X j.castSucc).filter (fun x ↦ c ≤ f x) := by
          apply Finset.filter_congr
          intro x _
          simp [LinearMap.neg_apply]
        rw [e]
        exact (hbis j).1
      · have e : (X (Fin.last d)).filter (fun x ↦ (-f) x ≤ -c) = A := by
          rw [hA]
          apply Finset.filter_congr
          intro x _
          simp [LinearMap.neg_apply]
        rw [e]
        exact hlast'

/-- **Lemma 2.6 of the paper** (corollary of the discrete ham sandwich
theorem).

The statement is **false for `d = 0`** (no nonzero functional exists on
`Euc 0`, see `not_exists_nonzero_linearMap_euc_zero`); the paper's range
`1 ≤ r ≤ d` implicitly assumes `d ≥ 1`, which we add as a hypothesis.  For
`1 ≤ d ≤ 3` it follows from `discrete_ham_sandwich` via `hamSandwich_halves'`
(the restriction to `d ≤ 3` matches the proved range of Borsuk–Ulam; the
paper only applies this lemma in `ℝ³`). -/
theorem hamSandwich_halves (hd : 1 ≤ d) (hd3 : d ≤ 3) {r : ℕ}
    (X : Fin (d + 1) → Finset (Euc d)) :
    ∃ f : Euc d →ₗ[ℝ] ℝ, ∃ c : ℝ, f ≠ 0 ∧
      (∀ i : Fin (d + 1), i.val < r →
        2 * ((X i).filter (fun x ↦ c ≤ f x)).card ≥ (X i).card) ∧
      (∀ i : Fin (d + 1), r ≤ i.val →
        2 * ((X i).filter (fun x ↦ f x ≤ c)).card ≥ (X i).card) :=
  hamSandwich_halves' hd hd3 X

end
