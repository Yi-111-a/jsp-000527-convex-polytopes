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

/-- Drop the last coordinate: `(x₁,…,x_d, x_{d+1}) ↦ (x₁,…,x_d)`. -/
def projDown : Euc (d + 1) →ₗ[ℝ] Euc d where
  toFun x := WithLp.toLp 2 fun i : Fin d ↦ (WithLp.ofLp x) i.castSucc
  map_add' x y := by
    ext i
    simp only [PiLp.add_apply]
  map_smul' t x := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]

@[simp]
theorem projDown_apply (x : Euc (d + 1)) (i : Fin d) :
    (WithLp.ofLp (projDown x)) i = (WithLp.ofLp x) i.castSucc := rfl

@[simp]
theorem liftUp_last (x : Euc d) :
    (WithLp.ofLp (liftUp x)) (Fin.last d) = 1 := by
  simp only [liftUp, WithLp.ofLp_toLp, Fin.snoc_last]

@[simp]
theorem liftUp_castSucc (x : Euc d) (i : Fin d) :
    (WithLp.ofLp (liftUp x)) i.castSucc = (WithLp.ofLp x) i := by
  simp only [liftUp, WithLp.ofLp_toLp, Fin.snoc_castSucc]

@[simp]
theorem liftDown_last (x : Euc d) :
    (WithLp.ofLp (liftDown x)) (Fin.last d) = -1 := by
  simp only [liftDown, PiLp.neg_apply, liftUp_last]

@[simp]
theorem liftDown_castSucc (x : Euc d) (i : Fin d) :
    (WithLp.ofLp (liftDown x)) i.castSucc = -(WithLp.ofLp x) i := by
  simp only [liftDown, PiLp.neg_apply, liftUp_castSucc]

@[simp]
theorem projDown_liftUp (x : Euc d) : projDown (liftUp x) = x := by
  ext i
  simp only [projDown_apply, liftUp_castSucc]

@[simp]
theorem projDown_liftDown (x : Euc d) : projDown (liftDown x) = -x := by
  ext i
  simp only [projDown_apply, liftDown_castSucc, PiLp.neg_apply]

theorem liftUp_surjective_projDown {A : Set (Euc d)} {z : Euc (d + 1)}
    (hz : z ∈ liftUp '' A) : liftUp (projDown z) = z := by
  obtain ⟨a, _, rfl⟩ := hz
  rw [projDown_liftUp]

theorem liftDown_surjective_projDown {B : Set (Euc d)} {z : Euc (d + 1)}
    (hz : z ∈ liftDown '' B) : liftDown (-projDown z) = z := by
  obtain ⟨b, _, rfl⟩ := hz
  rw [projDown_liftDown, neg_neg]

theorem liftUp_liftDown_disjoint {A B : Set (Euc d)} :
    Disjoint (liftUp '' A) (liftDown '' B) := by
  rw [Set.disjoint_iff]
  rintro z ⟨⟨a, _, rfl⟩, ⟨b, _, hzb⟩⟩
  have h1 := liftUp_last a
  rw [← hzb] at h1
  rw [liftDown_last] at h1
  norm_num at h1

/-- `∑ wᵢ • liftUp zᵢ = liftUp p` whenever `∑ wᵢ • zᵢ = p` and `∑ wᵢ = 1`. -/
private theorem weighted_sum_liftUp {ι : Type} (t : Finset ι) (w : ι → ℝ)
    (z : ι → Euc d) (q : Euc d) (hw1 : ∑ i ∈ t, w i = 1)
    (hs : ∑ i ∈ t, w i • z i = q) :
    ∑ i ∈ t, w i • liftUp (z i) = liftUp q := by
  ext k
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
  · simp only [liftUp_castSucc]
    have hh := congrFun (congrArg WithLp.ofLp hs) j
    rw [WithLp.ofLp_sum, Finset.sum_apply] at hh
    simp only [PiLp.smul_apply, smul_eq_mul] at hh
    exact hh
  · simp only [liftUp_last, mul_one]
    exact hw1

/-- **Theorem 2.3 (Kirchberger).** -/
theorem kirchberger {A B : Set (Euc d)}
    (h : (convexHull ℝ A ∩ convexHull ℝ B).Nonempty) :
    ∃ A' B' : Finset (Euc d),
      (A' : Set (Euc d)) ⊆ A ∧ (B' : Set (Euc d)) ⊆ B ∧
      A'.card + B'.card ≤ d + 2 ∧
      (convexHull ℝ (A' : Set (Euc d)) ∩ convexHull ℝ (B' : Set (Euc d))).Nonempty := by
  classical
  obtain ⟨p, hpA, hpB⟩ := h
  -- Finite convex-combination witnesses for `p` on each side.
  rw [convexHull_eq] at hpA hpB
  obtain ⟨ιA, tA, wA, zA, hwA0, hwA1, hzA, hpA'⟩ := hpA
  obtain ⟨ιB, tB, wB, zB, hwB0, hwB1, hzB, hpB'⟩ := hpB
  have hsA : ∑ i ∈ tA, wA i • zA i = p := by
    rw [← hpA', Finset.centerMass_eq_of_sum_1 _ _ hwA1]
  have hsB : ∑ j ∈ tB, wB j • zB j = p := by
    rw [← hpB', Finset.centerMass_eq_of_sum_1 _ _ hwB1]
  -- The lifted difference set and `0 ∈ conv Z`.
  set Z : Set (Euc (d + 1)) := liftUp '' A ∪ liftDown '' B with hZ
  have hUp := weighted_sum_liftUp tA wA zA p hwA1 hsA
  have hDn : ∑ j ∈ tB, wB j • liftDown (zB j) = -liftUp p := by
    have e : ∀ j ∈ tB, wB j • liftDown (zB j) = -(wB j • liftUp (zB j)) :=
      fun j _ ↦ by rw [show liftDown (zB j) = -liftUp (zB j) from rfl, smul_neg]
    rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
    congr 1
    exact weighted_sum_liftUp tB wB zB p hwB1 hsB
  have h0 : (0 : Euc (d + 1)) ∈ convexHull ℝ Z := by
    refine mem_convexHull_of_exists_fintype
      (fun i : tA ⊕ tB ↦ Sum.elim (fun i : ↥tA ↦ wA i / 2) (fun j : ↥tB ↦ wB j / 2) i)
      (fun i : tA ⊕ tB ↦
        Sum.elim (fun i : ↥tA ↦ liftUp (zA i)) (fun j : ↥tB ↦ liftDown (zB j)) i)
      ?_ ?_ ?_ ?_
    · intro i
      rcases i with ⟨i, hi⟩ | ⟨j, hj⟩
      · show 0 ≤ wA i / 2
        exact div_nonneg (hwA0 i hi) (by norm_num)
      · show 0 ≤ wB j / 2
        exact div_nonneg (hwB0 j hj) (by norm_num)
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.sum_div, ← Finset.sum_div,
        Finset.sum_coe_sort tA wA, Finset.sum_coe_sort tB wB, hwA1, hwB1]
      norm_num
    · intro i
      rcases i with ⟨i, hi⟩ | ⟨j, hj⟩
      · show liftUp (zA i) ∈ Z
        exact Set.mem_union_left _ ⟨zA i, hzA i hi, rfl⟩
      · show liftDown (zB j) ∈ Z
        exact Set.mem_union_right _ ⟨zB j, hzB j hj, rfl⟩
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Finset.sum_coe_sort tA (fun x ↦ (wA x / 2) • liftUp (zA x)),
        Finset.sum_coe_sort tB (fun x ↦ (wB x / 2) • liftDown (zB x))]
      have e1 : ∀ i ∈ tA,
          (wA i / 2) • liftUp (zA i) = (1 / 2 : ℝ) • (wA i • liftUp (zA i)) :=
        fun i _ ↦ by rw [show wA i / 2 = (1 / 2 : ℝ) * wA i from by ring, ← smul_smul]
      have e2 : ∀ j ∈ tB,
          (wB j / 2) • liftDown (zB j) = (1 / 2 : ℝ) • (wB j • liftDown (zB j)) :=
        fun j _ ↦ by rw [show wB j / 2 = (1 / 2 : ℝ) * wB j from by ring, ← smul_smul]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2,
        ← Finset.smul_sum, ← Finset.smul_sum, hUp, hDn, smul_neg, add_neg_cancel]
  -- Carathéodory: an affinely independent `Z' ⊆ Z` with `0 ∈ conv Z'`.
  rw [convexHull_eq_union] at h0
  simp only [Set.mem_iUnion, exists_prop] at h0
  obtain ⟨Z', hZ'sub, hZ'ind, h0'⟩ := h0
  -- The cardinality bound.
  have hZcard : Z'.card ≤ d + 2 := by
    have h1 := hZ'ind.card_le_finrank_succ
    rw [Fintype.card_coe] at h1
    have h2 : Module.finrank ℝ
        (vectorSpan ℝ (Set.range ((↑) : ↥Z' → Euc (d + 1))))
        ≤ Module.finrank ℝ (Euc (d + 1)) := Submodule.finrank_le _
    rw [finrank_euclideanSpace_fin] at h2
    omega
  -- Split `Z'` by the last-coordinate sign.
  set ZA : Finset (Euc (d + 1)) := Z'.filter (· ∈ liftUp '' A) with hZA
  set ZB : Finset (Euc (d + 1)) := Z'.filter (· ∈ liftDown '' B) with hZB
  have hZmem : ∀ z ∈ Z', z ∈ liftUp '' A ∨ z ∈ liftDown '' B := fun z hz ↦
    (Set.mem_union z _ _).1 (hZ'sub hz)
  have hZdisj : Disjoint ZA ZB := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    rw [Finset.mem_filter] at hzA hzB
    exact Set.disjoint_left.1 liftUp_liftDown_disjoint hzA.2 hzB.2
  have hZunion : ZA ∪ ZB = Z' := by
    rw [hZA, hZB, ← Finset.filter_or]
    exact Finset.filter_true_of_mem fun z hz ↦ hZmem z hz
  have hZcard' : ZA.card + ZB.card = Z'.card := by
    rw [← Finset.card_union_of_disjoint hZdisj, hZunion]
  -- Pull back to `A' ⊆ A`, `B' ⊆ B`.
  set A' : Finset (Euc d) := ZA.image projDown with hA'
  set B' : Finset (Euc d) := ZB.image (fun z ↦ -projDown z) with hB'
  have hA'sub : (A' : Set (Euc d)) ⊆ A := by
    intro a ha
    rw [hA', Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨z, hzZ, rfl⟩ := ha
    rw [Finset.mem_filter] at hzZ
    obtain ⟨a₀, ha₀A, hzup⟩ := hzZ.2
    rw [← hzup, projDown_liftUp]
    exact ha₀A
  have hB'sub : (B' : Set (Euc d)) ⊆ B := by
    intro b hb
    rw [hB', Finset.mem_coe, Finset.mem_image] at hb
    obtain ⟨z, hzZ, rfl⟩ := hb
    rw [Finset.mem_filter] at hzZ
    obtain ⟨b₀, hb₀B, hzdn⟩ := hzZ.2
    rw [← hzdn, projDown_liftDown, neg_neg]
    exact hb₀B
  have hcard : A'.card + B'.card ≤ d + 2 := by
    have hA'le : A'.card ≤ ZA.card := Finset.card_image_le
    have hB'le : B'.card ≤ ZB.card := Finset.card_image_le
    omega
  -- The combination weights: `0 ∈ conv Z'` gives `w ≥ 0`, `Σ w = 1`, `Σ w·z = 0`.
  rw [Finset.convexHull_eq] at h0'
  obtain ⟨w, hw0, hw1, hcm⟩ := h0'
  have hsum : ∑ z ∈ Z', w z • z = 0 := by
    have h0'' := hcm
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at h0''
    simpa [id] using h0''
  -- Last-coordinate balance: `Σ_{ZA} w = Σ_{ZB} w = 1/2`.
  have hlast : ∑ z ∈ Z', w z * ((WithLp.ofLp z) (Fin.last d)) = 0 := by
    have h := congrArg (EuclideanSpace.projₗ (Fin.last d)) hsum
    rw [map_zero, map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    have e : ∀ z ∈ Z', w z * ((WithLp.ofLp z) (Fin.last d))
        = w z * EuclideanSpace.projₗ (Fin.last d) z :=
      fun z _ ↦ by rw [PiLp.projₗ_apply]
    rw [Finset.sum_congr rfl e]
    exact h
  have hlastA : ∀ z ∈ ZA, (WithLp.ofLp z) (Fin.last d) = 1 := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨a, _, rfl⟩ := hz.2
    exact liftUp_last a
  have hlastB : ∀ z ∈ ZB, (WithLp.ofLp z) (Fin.last d) = -1 := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨b, _, rfl⟩ := hz.2
    exact liftDown_last b
  rw [← hZunion, Finset.sum_union hZdisj] at hlast hw1
  have e1 : ∑ z ∈ ZA, w z * (WithLp.ofLp z) (Fin.last d) = ∑ z ∈ ZA, w z :=
    Finset.sum_congr rfl fun z hz ↦ by rw [hlastA z hz, mul_one]
  have e2 : ∑ z ∈ ZB, w z * (WithLp.ofLp z) (Fin.last d) = -∑ z ∈ ZB, w z := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z hz ↦ by rw [hlastB z hz]; ring
  rw [e1, e2] at hlast
  -- hlast : Σ_{ZA} w − Σ_{ZB} w = 0 ; hw1 : Σ_{ZA} w + Σ_{ZB} w = 1.
  have htA : ∑ z ∈ ZA, w z = 1 / 2 := by linarith
  have htB : ∑ z ∈ ZB, w z = 1 / 2 := by linarith
  -- projDown balance: `Σ_{ZA} w·a = Σ_{ZB} w·b` after sign flip.
  have hproj : ∑ z ∈ Z', w z • projDown z = 0 := by
    have h := congrArg projDown hsum
    rw [map_zero, map_sum] at h
    simpa [map_smul] using h
  rw [← hZunion, Finset.sum_union hZdisj] at hproj
  have hprojB : ∀ z ∈ ZB, w z • projDown z = -(w z • (-projDown z)) :=
    fun z _ ↦ by rw [smul_neg, neg_neg]
  rw [Finset.sum_congr rfl hprojB, Finset.sum_neg_distrib] at hproj
  have heq : ∑ z ∈ ZA, w z • projDown z = ∑ z ∈ ZB, w z • (-projDown z) := by
    rw [← sub_eq_add_neg] at hproj
    exact sub_eq_zero.1 hproj
  -- Injectivity of the projected maps, needed for `Finset.sum_image`.
  have hInjA : Set.InjOn projDown (ZA : Set (Euc (d + 1))) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    obtain ⟨ax, -, rfl⟩ := hx.2
    obtain ⟨ay, -, rfl⟩ := hy.2
    rw [projDown_liftUp, projDown_liftUp] at hxy
    rw [hxy]
  have hInjB : Set.InjOn (fun z ↦ -projDown z) (ZB : Set (Euc (d + 1))) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    obtain ⟨bx, -, rfl⟩ := hx.2
    obtain ⟨byv, -, rfl⟩ := hy.2
    simp only [projDown_liftDown, neg_inj] at hxy
    rw [hxy]
  -- The common point `q = 2 Σ_{ZA} w·projDown`.
  refine ⟨A', B', hA'sub, hB'sub, hcard,
    ⟨((2 : ℝ) • ∑ z ∈ ZA, w z • projDown z), ?_, ?_⟩⟩
  · -- q ∈ conv A':  weights `2 w (liftUp a)` on `a = projDown z`, `z ∈ ZA`.
    have hw'0 : ∀ a ∈ A', 0 ≤ 2 * w (liftUp a) := by
      intro a ha
      obtain ⟨z, hzZ, rfl⟩ := Finset.mem_image.1 (hA' ▸ ha)
      rw [Finset.mem_filter] at hzZ
      rw [liftUp_surjective_projDown hzZ.2]
      exact mul_nonneg (by norm_num) (hw0 z hzZ.1)
    have hw'1 : ∑ a ∈ A', 2 * w (liftUp a) = 1 := by
      rw [hA', Finset.sum_image hInjA]
      calc ∑ z ∈ ZA, 2 * w (liftUp (projDown z))
          = ∑ z ∈ ZA, 2 * w z := Finset.sum_congr rfl fun z hz ↦ by
            rw [Finset.mem_filter] at hz
            rw [liftUp_surjective_projDown hz.2]
        _ = 2 * (∑ z ∈ ZA, w z) := by rw [← Finset.mul_sum]
        _ = 1 := by rw [htA]; norm_num
    have hcm' := Finset.centerMass_mem_convexHull A' hw'0
      (by simpa using hw'1.symm ▸ zero_lt_one) fun a ha ↦ Finset.mem_coe.2 ha
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw'1] at hcm'
    change ∑ a ∈ A', (2 * w (liftUp a)) • a ∈ convexHull ℝ ↑A' at hcm'
    have hq : ∑ a ∈ A', (2 * w (liftUp a)) • a = (2 : ℝ) • ∑ z ∈ ZA, w z • projDown z := by
      rw [hA', Finset.sum_image hInjA]
      calc ∑ z ∈ ZA, (2 * w (liftUp (projDown z))) • projDown z
          = ∑ z ∈ ZA, (2 : ℝ) • (w z • projDown z) := Finset.sum_congr rfl fun z hz ↦ by
            rw [Finset.mem_filter] at hz
            simp only [liftUp_surjective_projDown hz.2, mul_smul]
        _ = (2 : ℝ) • ∑ z ∈ ZA, w z • projDown z := by rw [← Finset.smul_sum]
    rwa [hq] at hcm'
  · -- q ∈ conv B':  weights `2 w (liftDown b)` on `b = -projDown z`, `z ∈ ZB`,
    -- and `q = 2 Σ_{ZB} w·(−projDown)` by `heq`.
    have hw'0 : ∀ b ∈ B', 0 ≤ 2 * w (liftDown b) := by
      intro b hb
      obtain ⟨z, hzZ, rfl⟩ := Finset.mem_image.1 (hB' ▸ hb)
      rw [Finset.mem_filter] at hzZ
      rw [liftDown_surjective_projDown hzZ.2]
      exact mul_nonneg (by norm_num) (hw0 z hzZ.1)
    have hw'1 : ∑ b ∈ B', 2 * w (liftDown b) = 1 := by
      rw [hB', Finset.sum_image hInjB]
      calc ∑ z ∈ ZB, 2 * w (liftDown (-projDown z))
          = ∑ z ∈ ZB, 2 * w z := Finset.sum_congr rfl fun z hz ↦ by
            rw [Finset.mem_filter] at hz
            rw [liftDown_surjective_projDown hz.2]
        _ = 2 * (∑ z ∈ ZB, w z) := by rw [← Finset.mul_sum]
        _ = 1 := by rw [htB]; norm_num
    have hcm' := Finset.centerMass_mem_convexHull B' hw'0
      (by simpa using hw'1.symm ▸ zero_lt_one) fun b hb ↦ Finset.mem_coe.2 hb
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw'1] at hcm'
    change ∑ b ∈ B', (2 * w (liftDown b)) • b ∈ convexHull ℝ ↑B' at hcm'
    have hq : ∑ b ∈ B', (2 * w (liftDown b)) • b = (2 : ℝ) • ∑ z ∈ ZA, w z • projDown z := by
      rw [hB', Finset.sum_image hInjB]
      calc ∑ z ∈ ZB, (2 * w (liftDown (-projDown z))) • (-projDown z)
          = ∑ z ∈ ZB, (2 : ℝ) • (w z • (-projDown z)) := Finset.sum_congr rfl fun z hz ↦ by
            rw [Finset.mem_filter] at hz
            simp only [liftDown_surjective_projDown hz.2, mul_smul]
        _ = (2 : ℝ) • ∑ z ∈ ZB, w z • (-projDown z) := by rw [← Finset.smul_sum]
        _ = (2 : ℝ) • ∑ z ∈ ZA, w z • projDown z := congrArg ((2 : ℝ) • ·) heq.symm
    rwa [hq] at hcm'

end
