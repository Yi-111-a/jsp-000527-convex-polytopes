import JSPProblem.Defs

/-!
# JSP-000527 — Definition checkpoints

Sanity lemmas validating the interface choices of `Defs.lean`.  Everything in
this file is fully proved; it fixes the semantics of `InGeneralPosition`,
`InConvexPosition` and `ForcesConvex` before the heavier developments.
-/

noncomputable section

variable {d : ℕ}

/-- Subsets of a general-position set are in general position. -/
theorem inGeneralPosition_mono {X Y : Set (Euc d)} (h : InGeneralPosition X)
    (hYX : Y ⊆ X) : InGeneralPosition Y :=
  fun s hs hcard ↦ h s (hs.trans hYX) hcard

/-- Convex position is hereditary: a subset of a convex-position set is again
in convex position. -/
theorem inConvexPosition_mono {S T : Finset (Euc d)} (hTS : T ⊆ S)
    (h : InConvexPosition S) : InConvexPosition T := by
  intro x hx
  have hsub : ((T.erase x : Finset (Euc d)) : Set (Euc d)) ⊆
      ((S.erase x : Finset (Euc d)) : Set (Euc d)) := by
    intro y hy
    simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
      Finset.mem_coe] at hy ⊢
    exact ⟨hTS hy.1, hy.2⟩
  exact fun hc ↦ h x (hTS hx) (convexHull_mono hsub hc)

/-- An affinely independent finset is in convex position: no vertex lies in the
convex hull (a fortiori the affine hull) of the others. -/
theorem inConvexPosition_of_affineIndependent {s : Finset (Euc d)}
    (h : AffineIndependent ℝ (fun x : s ↦ (x : Euc d))) : InConvexPosition s := by
  intro x hx
  have hnot : (x : Euc d) ∉
      affineSpan ℝ ((fun y : s ↦ (y : Euc d)) '' (Set.univ \ {⟨x, hx⟩})) :=
    h.notMem_affineSpan_sdiff ⟨x, hx⟩ Set.univ
  have himg : ((fun y : s ↦ (y : Euc d)) '' (Set.univ \ {⟨x, hx⟩})) =
      ((s.erase x : Finset _) : Set _) := by
    ext z
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
      true_and, Finset.coe_erase, Finset.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun hzx ↦ hy (Subtype.ext hzx)⟩
    · intro hz
      exact ⟨⟨z, hz.1⟩, fun h ↦ hz.2 (congrArg Subtype.val h), rfl⟩
  rw [himg] at hnot
  exact fun hc ↦ hnot (convexHull_subset_affineSpan _ hc)

/-- A general-position set `X` with `|X| ≥ d+1` has every `≤ d+1`-element
subset affinely independent (extend the subset to `d+1` points and restrict). -/
theorem affineIndependent_of_inGeneralPosition {X : Finset (Euc d)}
    (hX : InGeneralPosition (X : Set (Euc d))) (hXcard : d + 1 ≤ X.card)
    {s : Finset (Euc d)} (hs : s ⊆ X) (hsc : s.card ≤ d + 1) :
    AffineIndependent ℝ (fun x : s ↦ (x : Euc d)) := by
  classical
  have hXdiff : (X \ s).card = X.card - s.card := Finset.card_sdiff_of_subset hs
  obtain ⟨U, hUsub, hUcard⟩ :=
    Finset.exists_subset_card_eq (n := d + 1 - s.card) (by
      rw [hXdiff]; omega)
  have hsU : s ∪ U ⊆ X := Finset.union_subset hs (hUsub.trans Finset.sdiff_subset)
  have hcard : (s ∪ U).card = d + 1 := by
    rw [Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]; intro u hu hUs
      exact (Finset.mem_sdiff.1 (hUsub hUs)).2 hu)]
    omega
  have hT := hX (s ∪ U) (by exact_mod_cast hsU) hcard
  have hincl : (s : Set (Euc d)) ⊆ ((s ∪ U : Finset _) : Set _) := by
    intro y hy; exact Finset.mem_union_left U hy
  -- restrict the independent family on `s ∪ U` to `s`
  exact hT.mono hincl

/-- `ForcesConvex` is antitone in `N`: more points only help. -/
theorem forcesConvex_anti {N M n : ℕ} (h : ForcesConvex d N n) (hNM : N ≤ M) :
    ForcesConvex d M n :=
  fun X hX hM ↦ h X hX (hNM.trans hM)

/-- `ForcesConvex` is downward-closed in the target size: any `m`-subset of a
convex-position `n`-set is again in convex position. -/
theorem forcesConvex_of_le {N m n : ℕ} (h : ForcesConvex d N n) (hmn : m ≤ n) :
    ForcesConvex d N m := by
  intro X hX hN
  obtain ⟨S, hSX, hcard, hS⟩ := h X hX hN
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (show m ≤ S.card by omega)
  exact ⟨T, hTS.trans hSX, hT, inConvexPosition_mono hTS hS⟩

/-- A two-element set is in convex position. -/
theorem inConvexPosition_pair {a b : Euc d} (h : a ≠ b) : InConvexPosition {a, b} := by
  intro x hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · rw [Finset.erase_insert (by simp [h])]
    simp [convexHull_singleton, h]
  · rw [Finset.erase_insert_of_ne (by simp [h]),
        Finset.erase_singleton]
    simp [convexHull_singleton, Ne.symm h]

/-- A singleton is in convex position. -/
theorem inConvexPosition_singleton {a : Euc d} : InConvexPosition {a} := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  simp [Finset.erase_singleton, convexHull_empty]

end
