import JSPProblem.Kirchberger
import JSPProblem.HamSandwich

/-!
# JSP-000527 — Above/below separation (Propositions 2.3 and 2.7)

Paper items:

* **Prop 2.3** (`prop_2_3`): the "all `x₁x₃` above `x₂x₄`" configuration forces
  `conv(X₁∪X₃) ∩ conv(X₂∪X₄) = ∅` — via Kirchberger.
* **Prop 2.7** (`prop_2_7`): a 2-separated collection in convex position can be
  re-separated by one plane matching any prescribed sign pattern read off a
  transversal — via Kirchberger + continuity.

Prop 2.2 / Cor 2.4 live in `SeparationRamsey.lean`; Prop 2.5 lives in
`SeparationHalving.lean`.
-/

noncomputable section

open scoped Topology

/-! ### Scalar triple product

The determinant `det3 a b c = det [a b c]` on `Euc 3`, with multilinearity and
the Cramer identity — the algebraic engine behind the "persistence of
transversal contact" step of Proposition 2.7. -/

private def det3 (a b c : Euc 3) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) +
    a 2 * (b 0 * c 1 - b 1 * c 0)

private lemma det3_add_left (a a' b c : Euc 3) :
    det3 (a + a') b c = det3 a b c + det3 a' b c := by
  simp only [det3, PiLp.add_apply]; ring

private lemma det3_add_mid (a b b' c : Euc 3) :
    det3 a (b + b') c = det3 a b c + det3 a b' c := by
  simp only [det3, PiLp.add_apply]; ring

private lemma det3_add_right (a b c c' : Euc 3) :
    det3 a b (c + c') = det3 a b c + det3 a b c' := by
  simp only [det3, PiLp.add_apply]; ring

private lemma det3_sub_left (a a' b c : Euc 3) :
    det3 (a - a') b c = det3 a b c - det3 a' b c := by
  simp only [det3, PiLp.sub_apply]; ring

private lemma det3_sub_mid (a b b' c : Euc 3) :
    det3 a (b - b') c = det3 a b c - det3 a b' c := by
  simp only [det3, PiLp.sub_apply]; ring

private lemma det3_sub_right (a b c c' : Euc 3) :
    det3 a b (c - c') = det3 a b c - det3 a b c' := by
  simp only [det3, PiLp.sub_apply]; ring

private lemma det3_smul_left (s : ℝ) (a b c : Euc 3) :
    det3 (s • a) b c = s * det3 a b c := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring

private lemma det3_smul_mid (s : ℝ) (a b c : Euc 3) :
    det3 a (s • b) c = s * det3 a b c := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring

private lemma det3_smul_right (s : ℝ) (a b c : Euc 3) :
    det3 a b (s • c) = s * det3 a b c := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring

private lemma det3_self_left (a c : Euc 3) : det3 a a c = 0 := by
  simp only [det3]; ring

private lemma det3_self_mid (a b : Euc 3) : det3 a b a = 0 := by
  simp only [det3]; ring

private lemma det3_self_right (a b : Euc 3) : det3 a b b = 0 := by
  simp only [det3]; ring

/-- Cramer's rule as a vector identity in `Euc 3`. -/
private lemma det3_cramer (d e₁ e₂ r : Euc 3) :
    det3 d e₁ e₂ • r =
      det3 r e₁ e₂ • d + det3 d r e₂ • e₁ + det3 d e₁ r • e₂ := by
  ext i
  fin_cases i
  · show det3 d e₁ e₂ * r 0 =
      det3 r e₁ e₂ * d 0 + det3 d r e₂ * e₁ 0 + det3 d e₁ r * e₂ 0
    simp only [det3]; ring
  · show det3 d e₁ e₂ * r 1 =
      det3 r e₁ e₂ * d 1 + det3 d r e₂ * e₁ 1 + det3 d e₁ r * e₂ 1
    simp only [det3]; ring
  · show det3 d e₁ e₂ * r 2 =
      det3 r e₁ e₂ * d 2 + det3 d r e₂ * e₁ 2 + det3 d e₁ r * e₂ 2
    simp only [det3]; ring

/-- `det3` is continuous in its three vector arguments. -/
private lemma det3_continuous :
    Continuous fun p : Euc 3 × Euc 3 × Euc 3 ↦ det3 p.1 p.2.1 p.2.2 := by
  have c1 : ∀ i : Fin 3, Continuous fun p : Euc 3 × Euc 3 × Euc 3 ↦ p.1 i :=
    fun i ↦ ((EuclideanSpace.proj i).continuous.comp continuous_fst :
      Continuous fun p : Euc 3 × Euc 3 × Euc 3 ↦ p.1 i)
  have c2 : ∀ i : Fin 3, Continuous fun p : Euc 3 × Euc 3 × Euc 3 ↦ p.2.1 i :=
    fun i ↦ ((EuclideanSpace.proj i).continuous.comp
      (continuous_fst.comp continuous_snd) :
      Continuous fun p : Euc 3 × Euc 3 × Euc 3 ↦ p.2.1 i)
  have c3 : ∀ i : Fin 3, Continuous fun p : Euc 3 × Euc 3 × Euc 3 ↦ p.2.2 i :=
    fun i ↦ ((EuclideanSpace.proj i).continuous.comp
      (continuous_snd.comp continuous_snd) :
      Continuous fun p : Euc 3 × Euc 3 × Euc 3 ↦ p.2.2 i)
  exact (((c1 0).mul (((c2 1).mul (c3 2)).sub ((c2 2).mul (c3 1)))).sub
      ((c1 1).mul (((c2 0).mul (c3 2)).sub ((c2 2).mul (c3 0))))).add
    ((c1 2).mul (((c2 0).mul (c3 1)).sub ((c2 1).mul (c3 0))))

/-- If `a` is in the span of `{b, c}` then `det3 a b c = 0`. -/
private lemma det3_eq_zero_of_mem_span {a b c : Euc 3}
    (h : a ∈ Submodule.span ℝ ({b, c} : Set (Euc 3))) : det3 a b c = 0 := by
  rw [Submodule.mem_span_pair] at h
  obtain ⟨r, s, h⟩ := h
  rw [← h]
  simp only [det3_add_left, det3_smul_left, det3_self_left, det3_self_mid]
  ring

/-- `det3` agrees with `Matrix.det` on row-vectors. -/
private lemma det3_eq_det (a b c : Euc 3) :
    det3 a b c = Matrix.det (Matrix.of fun i j : Fin 3 ↦ ![a, b, c] i j) := by
  rw [det3, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val]
  ring

/-- If `a` is outside the span of the linearly independent pair `{b, c}`,
then `det3 a b c ≠ 0`. -/
private lemma det3_ne_zero {a b c : Euc 3}
    (hind : LinearIndependent ℝ ![b, c])
    (h : a ∉ Submodule.span ℝ ({b, c} : Set (Euc 3))) : det3 a b c ≠ 0 := by
  intro hdet
  apply h
  set M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j ↦ ![a, b, c] i j
    with hM
  have hd : M.det = 0 := by
    rw [← det3_eq_det a b c]
    exact hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  -- `v ᵥ* M = 0` is the relation `v 0 • a + v 1 • b + v 2 • c = 0`.
  have hrel : v 0 • a + v 1 • b + v 2 • c = 0 := by
    ext j
    have hj := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, hM,
      Matrix.of_apply, Matrix.cons_val, Pi.zero_apply] at hj
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul]
    linarith [hj]
  by_cases hv00 : v 0 = 0
  · -- then `v 1 • b + v 2 • c = 0` with `(v 1, v 2) ≠ 0`, contradicting `hind`.
    exfalso
    rw [hv00, zero_smul, zero_add] at hrel
    rw [Fintype.linearIndependent_iff] at hind
    have h2 := hind ![v 1, v 2] (by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hrel)
    have h10 : v 1 = 0 := by simpa using h2 0
    have h20 : v 2 = 0 := by simpa using h2 1
    exact hv0 (funext fun i ↦ by fin_cases i <;> simp [hv00, h10, h20])
  · -- then `a = -(v 1 / v 0) • b - (v 2 / v 0) • c`.
    refine Submodule.mem_span_pair.mpr ⟨-(v 1) / v 0, -(v 2) / v 0, ?_⟩
    have h1 : v 0 • a = -(v 1 • b + v 2 • c) := by
      rw [add_assoc] at hrel
      exact add_eq_zero_iff_eq_neg.mp hrel
    have h2 : a = (v 0)⁻¹ • (-(v 1 • b + v 2 • c)) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hv00, one_smul]
    rw [h2]
    module

/-- The segment interpolation `slidePt y z j t` slides `y j` to `z j`. -/
private abbrev slidePt (y z : Fin 5 → Euc 3) (j : Fin 5) (t : ℝ) : Euc 3 :=
  (1 - t) • y j + t • z j

/-- `1-s`/`s` affine combination as a base point plus a scalar multiple of the
difference. -/
private lemma seg_smul_eq (s : ℝ) (a b : Euc 3) :
    (1 - s) • a + s • b = a + s • (b - a) := by
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- `1-α-β`/`α`/`β` affine combination as a base point plus two difference
terms. -/
private lemma tri_smul_eq (α β : ℝ) (v₀ v₁ v₂ : Euc 3) :
    (1 - α - β) • v₀ + α • v₁ + β • v₂ = v₀ + α • (v₁ - v₀) + β • (v₂ - v₀) := by
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- If the two edge vectors of a triangle are linearly dependent, its vertices
are collinear. -/
private lemma collinear_triple_of_dep {a b c : Euc 3}
    (h : ¬ LinearIndependent ℝ ![b - a, c - a]) :
    Collinear ℝ ({a, b, c} : Set (Euc 3)) := by
  rw [collinear_iff_of_mem (show a ∈ ({a, b, c} : Set (Euc 3)) from Set.mem_insert _ _)]
  rw [Fintype.linearIndependent_iff] at h
  push Not at h
  obtain ⟨g, hg, i, hi⟩ := h
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  by_cases hg0 : g 0 = 0
  · rw [hg0, zero_smul, zero_add] at hg
    have hg1 : g 1 ≠ 0 := by
      fin_cases i
      · exact absurd hg0 hi
      · exact hi
    have hca : c = a := sub_eq_zero.mp (by
      rcases smul_eq_zero.mp hg with h1 | h1
      · exact absurd h1 hg1
      · exact h1)
    refine ⟨b - a, fun p hp ↦ ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simpa using hca⟩
  · refine ⟨c - a, fun p hp ↦ ?_⟩
    have hba : b - a = (-(g 1) / g 0) • (c - a) := by
      have h1 : g 0 • (b - a) = -(g 1 • (c - a)) := add_eq_zero_iff_eq_neg.mp hg
      have h2 : b - a = (g 0)⁻¹ • (-(g 1 • (c - a))) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ hg0, one_smul]
      rw [h2]
      module
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨-(g 1) / g 0, by simp only [vadd_eq_add]; rw [← hba, sub_add_cancel]⟩
    · exact ⟨1, by simp [vadd_eq_add]⟩

/-- The compact "contact box": parameters `(t, σ, lmm)` witnessing an
intersection of the moving segment `[w₀t, w₁t]` with the moving triangle
`conv{w₂t, w₃t, w₄t}`, where `wⱼt = slidePt y z j t`. -/
private def contactBox (y z : Fin 5 → Euc 3) : Set (ℝ × ℝ × (Fin 3 → ℝ)) :=
  {p | p.1 ∈ Set.Icc 0 1 ∧ p.2.1 ∈ Set.Icc 0 1 ∧
    (∀ j : Fin 3, 0 ≤ p.2.2 j) ∧ (∑ j : Fin 3, p.2.2 j = 1) ∧
    (1 - p.2.1) • slidePt y z 0 p.1 + p.2.1 • slidePt y z 1 p.1 =
      ∑ j : Fin 3, p.2.2 j • slidePt y z (![2, 3, 4] j) p.1}

private lemma isCompact_contactBox (y z : Fin 5 → Euc 3) :
    IsCompact (contactBox y z) := by
  have hw : ∀ j : Fin 5, Continuous fun t : ℝ ↦ slidePt y z j t := fun j ↦
    ((continuous_const.sub continuous_id').smul continuous_const).add
      (continuous_id'.smul continuous_const)
  have hL : Continuous fun p : ℝ × ℝ × (Fin 3 → ℝ) ↦
      (1 - p.2.1) • slidePt y z 0 p.1 + p.2.1 • slidePt y z 1 p.1 :=
    (((continuous_const.sub (continuous_fst.comp continuous_snd)).smul
        ((hw 0).comp continuous_fst)).add
      ((continuous_fst.comp continuous_snd).smul ((hw 1).comp continuous_fst)))
  have hR : Continuous fun p : ℝ × ℝ × (Fin 3 → ℝ) ↦
      ∑ j : Fin 3, p.2.2 j • slidePt y z (![2, 3, 4] j) p.1 :=
    continuous_finsetSum _ fun j _ ↦
      Continuous.smul ((continuous_apply j).comp (continuous_snd.comp continuous_snd))
        ((hw (![2, 3, 4] j)).comp continuous_fst)
  have hcl : IsClosed (contactBox y z) := by
    have heq : contactBox y z =
        ({p : ℝ × ℝ × (Fin 3 → ℝ) | p.1 ∈ Set.Icc 0 1 ∧ p.2.1 ∈ Set.Icc 0 1 ∧
          (∀ j : Fin 3, 0 ≤ p.2.2 j) ∧ ∑ j : Fin 3, p.2.2 j = 1}) ∩
        {p : ℝ × ℝ × (Fin 3 → ℝ) | (1 - p.2.1) • slidePt y z 0 p.1 +
            p.2.1 • slidePt y z 1 p.1 =
          ∑ j : Fin 3, p.2.2 j • slidePt y z (![2, 3, 4] j) p.1} := by
      ext p
      simp only [contactBox, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [heq]
    refine IsClosed.inter ?_ (isClosed_eq hL hR)
    have hI1 : IsClosed {p : ℝ × ℝ × (Fin 3 → ℝ) | p.1 ∈ Set.Icc 0 1} :=
      isClosed_Icc.preimage continuous_fst
    have hI2 : IsClosed {p : ℝ × ℝ × (Fin 3 → ℝ) | p.2.1 ∈ Set.Icc 0 1} :=
      isClosed_Icc.preimage (continuous_fst.comp continuous_snd)
    have hI3 : IsClosed {p : ℝ × ℝ × (Fin 3 → ℝ) | ∀ j : Fin 3, 0 ≤ p.2.2 j} := by
      rw [show {p : ℝ × ℝ × (Fin 3 → ℝ) | ∀ j : Fin 3, 0 ≤ p.2.2 j} =
          ⋂ j : Fin 3, {p | 0 ≤ p.2.2 j} from Set.ofPred_forall _]
      exact isClosed_iInter fun j ↦
        isClosed_le continuous_const ((continuous_apply j).comp
          (continuous_snd.comp continuous_snd))
    have hI4 : IsClosed {p : ℝ × ℝ × (Fin 3 → ℝ) | ∑ j : Fin 3, p.2.2 j = 1} :=
      isClosed_eq (continuous_finsetSum _ fun j _ ↦
        (continuous_apply j).comp (continuous_snd.comp continuous_snd))
        continuous_const
    have hsplit : {p : ℝ × ℝ × (Fin 3 → ℝ) | p.1 ∈ Set.Icc 0 1 ∧
        p.2.1 ∈ Set.Icc 0 1 ∧ (∀ j : Fin 3, 0 ≤ p.2.2 j) ∧
        ∑ j : Fin 3, p.2.2 j = 1} =
        {p : ℝ × ℝ × (Fin 3 → ℝ) | p.1 ∈ Set.Icc 0 1} ∩
          {p | p.2.1 ∈ Set.Icc 0 1} ∩
          {p | ∀ j : Fin 3, 0 ≤ p.2.2 j} ∩ {p | ∑ j : Fin 3, p.2.2 j = 1} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [hsplit]
    exact ((hI1.inter hI2).inter hI3).inter hI4
  -- the box is contained in the compact product `Icc × Icc × closedBall 0 1`
  have hsub : contactBox y z ⊆
      Set.Icc 0 1 ×ˢ (Set.Icc 0 1 ×ˢ Metric.closedBall (0 : Fin 3 → ℝ) 1) := by
    intro p hp
    refine ⟨hp.1, hp.2.1, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hp.2.2.1 j], by
      have hle := Finset.single_le_sum (f := fun j : Fin 3 ↦ p.2.2 j)
        (fun i _ ↦ hp.2.2.1 i) (Finset.mem_univ j)
      rw [hp.2.2.2.1] at hle
      exact hle⟩
  exact (isCompact_Icc.prod (isCompact_Icc.prod
    (isCompact_closedBall (0 : Fin 3 → ℝ) 1))).of_isClosed_subset hcl hsub

/-- **Sliding triangle–segment contact.**  If at `t = 0` the segment `[y₀,y₁]`
meets the triangle `conv{y₂,y₃,y₄}` but at `t = 1` the segment `[z₀,z₁]` misses
`conv{z₂,z₃,z₄}`, then at some intermediate `t` they still meet, and the
meeting point is constrained: either it lies on an edge of the moving
triangle, or it is an endpoint of the moving segment lying inside the moving
triangle. -/
private lemma slide_triangle_boundary {y z : Fin 5 → Euc 3}
    (h0 : (segment ℝ (y 0) (y 1) ∩
      convexHull ℝ ({y 2, y 3, y 4} : Set (Euc 3))).Nonempty)
    (h1 : Disjoint (segment ℝ (z 0) (z 1))
      (convexHull ℝ ({z 2, z 3, z 4} : Set (Euc 3)))) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ u : Euc 3,
      u ∈ segment ℝ (slidePt y z 0 t) (slidePt y z 1 t) ∧
      (u ∈ segment ℝ (slidePt y z 2 t) (slidePt y z 3 t) ∨
       u ∈ segment ℝ (slidePt y z 3 t) (slidePt y z 4 t) ∨
       u ∈ segment ℝ (slidePt y z 4 t) (slidePt y z 2 t) ∨
       ((u = slidePt y z 0 t ∨ u = slidePt y z 1 t) ∧
        u ∈ convexHull ℝ
          ({slidePt y z 2 t, slidePt y z 3 t, slidePt y z 4 t} : Set (Euc 3)))) := by
  obtain ⟨q, hqseg, hqtri⟩ := h0
  rw [segment_eq_image] at hqseg
  obtain ⟨σ0, hσ0, hq0⟩ := hqseg
  have w0eq : ∀ j : Fin 5, slidePt y z j 0 = y j := fun j ↦ by simp [slidePt]
  have w1eq : ∀ j : Fin 5, slidePt y z j 1 = z j := fun j ↦ by simp [slidePt]
  -- Degenerate triangles at `t = 0` already give an edge contact.
  by_cases h23 : y 2 = y 3
  · have hqtri' : q ∈ segment ℝ (y 3) (y 4) := by
      have hs : ({y 2, y 3, y 4} : Set (Euc 3)) = {y 3, y 4} := by
        rw [h23]
        exact Set.insert_eq_of_mem (Set.mem_insert _ _)
      rwa [hs, convexHull_pair] at hqtri
    refine ⟨0, Set.left_mem_Icc.mpr zero_le_one, q, ?_, Or.inr (Or.inl ?_)⟩
    · rw [w0eq 0, w0eq 1, segment_eq_image]
      exact ⟨σ0, hσ0, hq0⟩
    · rw [w0eq 3, w0eq 4]
      exact hqtri'
  by_cases h34 : y 3 = y 4
  · have hqtri' : q ∈ segment ℝ (y 4) (y 2) := by
      have hs : ({y 2, y 3, y 4} : Set (Euc 3)) = {y 2, y 4} := by
        rw [h34]
        ext v
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hs, convexHull_pair] at hqtri
      rwa [segment_symm]
    refine ⟨0, Set.left_mem_Icc.mpr zero_le_one, q, ?_, Or.inr (Or.inr (Or.inl ?_))⟩
    · rw [w0eq 0, w0eq 1, segment_eq_image]
      exact ⟨σ0, hσ0, hq0⟩
    · rw [w0eq 4, w0eq 2]
      exact hqtri'
  by_cases h42 : y 4 = y 2
  · have hqtri' : q ∈ segment ℝ (y 2) (y 3) := by
      have hs : ({y 2, y 3, y 4} : Set (Euc 3)) = {y 2, y 3} := by
        rw [h42]
        ext v
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rwa [hs, convexHull_pair] at hqtri
    refine ⟨0, Set.left_mem_Icc.mpr zero_le_one, q, ?_, Or.inl ?_⟩
    · rw [w0eq 0, w0eq 1, segment_eq_image]
      exact ⟨σ0, hσ0, hq0⟩
    · rw [w0eq 2, w0eq 3]
      exact hqtri'
  -- Non-degenerate start triangle: barycentric coordinates of the `t = 0`
  -- contact point.
  have hqtri' : q ∈ convexHull ℝ (↑({y 2, y 3, y 4} : Finset (Euc 3))) := by
    rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
    exact hqtri
  obtain ⟨μ, hμ0, hμ1, hμ2⟩ := Finset.mem_convexHull'.mp hqtri'
  have hy23 : y 2 ∉ ({y 3, y 4} : Finset (Euc 3)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨h23, Ne.symm h42⟩
  have hy34 : y 3 ∉ ({y 4} : Finset (Euc 3)) := by
    simp only [Finset.mem_singleton]
    exact h34
  rw [Finset.sum_insert hy23, Finset.sum_insert hy34, Finset.sum_singleton] at hμ1 hμ2
  set K := contactBox y z with hKdef
  set Tset := Prod.fst '' K with hTdef
  have hTne : Tset.Nonempty := by
    refine ⟨0, (0, σ0, ![μ (y 2), μ (y 3), μ (y 4)]), ?_, rfl⟩
    simp only [hKdef, contactBox, Set.mem_ofPred_eq]
    refine ⟨Set.left_mem_Icc.mpr zero_le_one, hσ0, ?_, ?_, ?_⟩
    · intro j
      fin_cases j
      · exact hμ0 _ (Finset.mem_insert_self _ _)
      · exact hμ0 _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _)))
      · exact hμ0 _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton_self _)))))
    · rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linarith [hμ1]
    · rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, w0eq]
      exact hq0.trans (hμ2.symm.trans (add_assoc _ _ _).symm)
  have hTc : IsCompact Tset := (isCompact_contactBox y z).image continuous_fst
  set t' := sSup Tset with ht'
  have ht'mem : t' ∈ Tset := hTc.sSup_mem hTne
  obtain ⟨⟨tv, σ', lmm'⟩, hK', htv⟩ := ht'mem
  have htv' : tv = t' := htv
  subst htv'
  simp only [hKdef, contactBox, Set.mem_ofPred_eq] at hK'
  obtain ⟨ht'I, hσ'I, hlmm'nn, hlmm'sum, heq⟩ := hK'
  have hlmm'sum3 : lmm' 0 + lmm' 1 + lmm' 2 = 1 := by
    rw [Fin.sum_univ_three] at hlmm'sum
    exact hlmm'sum
  -- `t' < 1`: otherwise `h1` fails.
  have ht'lt : t' < 1 := by
    by_contra h
    push Not at h
    have ht1 : t' = 1 := le_antisymm ht'I.2 h
    rw [ht1] at heq
    simp only [w1eq] at heq
    have hseg1 : (1 - σ') • z 0 + σ' • z 1 ∈ segment ℝ (z 0) (z 1) := by
      rw [segment_eq_image]
      exact ⟨σ', hσ'I, rfl⟩
    have htri1 : (1 - σ') • z 0 + σ' • z 1 ∈
        convexHull ℝ ({z 2, z 3, z 4} : Set (Euc 3)) := by
      rw [heq]
      exact mem_convexHull_of_exists_fintype lmm' (fun j : Fin 3 ↦ z (![2, 3, 4] j))
        hlmm'nn hlmm'sum (fun j ↦ by fin_cases j <;> simp) rfl
    exact (Set.disjoint_left.mp h1) hseg1 htri1
  set u : Euc 3 := (1 - σ') • slidePt y z 0 t' + σ' • slidePt y z 1 t' with hu
  have huseg : u ∈ segment ℝ (slidePt y z 0 t') (slidePt y z 1 t') := by
    rw [hu, segment_eq_image]
    exact ⟨σ', hσ'I, rfl⟩
  have huV : u = ∑ j : Fin 3, lmm' j • slidePt y z (![2, 3, 4] j) t' := hu.trans heq
  have hutri : u ∈ convexHull ℝ
      ({slidePt y z 2 t', slidePt y z 3 t', slidePt y z 4 t'} : Set (Euc 3)) := by
    rw [huV]
    exact mem_convexHull_of_exists_fintype lmm'
      (fun j : Fin 3 ↦ slidePt y z (![2, 3, 4] j) t') hlmm'nn hlmm'sum
      (fun j ↦ by fin_cases j <;> simp) rfl
  -- Endpoint cases of `σ'`.
  by_cases hσ'0 : σ' = 0
  · refine ⟨t', ht'I, u, huseg, Or.inr (Or.inr (Or.inr ⟨Or.inl ?_, hutri⟩))⟩
    rw [hu, hσ'0]
    simp
  by_cases hσ'1 : σ' = 1
  · refine ⟨t', ht'I, u, huseg, Or.inr (Or.inr (Or.inr ⟨Or.inr ?_, hutri⟩))⟩
    rw [hu, hσ'1]
    simp
  have hσ'pos : 0 < σ' := lt_of_le_of_ne hσ'I.1 (Ne.symm hσ'0)
  have hσ'lt : σ' < 1 := lt_of_le_of_ne hσ'I.2 hσ'1
  -- Vanishing `lmm'`-coordinates put `u` on a triangle edge.
  by_cases hlmm'0 : lmm' 0 = 0
  · refine ⟨t', ht'I, u, huseg, Or.inr (Or.inl ?_)⟩
    have hlmm'1 : lmm' 1 = 1 - lmm' 2 := by linarith [hlmm'sum3]
    have hue : u = (1 - lmm' 2) • slidePt y z 3 t' + lmm' 2 • slidePt y z 4 t' := by
      rw [huV, Fin.sum_univ_three]
      simp only [Matrix.cons_val]
      rw [hlmm'0]
      simp only [zero_smul, zero_add]
      rw [hlmm'1]
    rw [segment_eq_image]
    exact ⟨lmm' 2, ⟨hlmm'nn 2, by linarith [hlmm'sum3, hlmm'0, hlmm'nn 1]⟩,
      hue.symm⟩
  by_cases hlmm'1 : lmm' 1 = 0
  · refine ⟨t', ht'I, u, huseg, Or.inr (Or.inr (Or.inl ?_))⟩
    have hlmm'2 : lmm' 2 = 1 - lmm' 0 := by linarith [hlmm'sum3]
    have hue : u = (1 - lmm' 0) • slidePt y z 4 t' + lmm' 0 • slidePt y z 2 t' := by
      rw [huV, Fin.sum_univ_three]
      simp only [Matrix.cons_val]
      rw [hlmm'1, hlmm'2]
      simp only [zero_smul, add_zero]
      exact add_comm _ _
    rw [segment_eq_image]
    exact ⟨lmm' 0, ⟨hlmm'nn 0, by linarith [hlmm'sum3, hlmm'1, hlmm'nn 2]⟩,
      hue.symm⟩
  by_cases hlmm'2 : lmm' 2 = 0
  · refine ⟨t', ht'I, u, huseg, Or.inl ?_⟩
    have hlmm'0' : lmm' 0 = 1 - lmm' 1 := by linarith [hlmm'sum3]
    have hue : u = (1 - lmm' 1) • slidePt y z 2 t' + lmm' 1 • slidePt y z 3 t' := by
      rw [huV, Fin.sum_univ_three]
      simp only [Matrix.cons_val]
      rw [hlmm'2, hlmm'0']
      simp only [zero_smul, add_zero]
    rw [segment_eq_image]
    exact ⟨lmm' 1, ⟨hlmm'nn 1, by linarith [hlmm'sum3, hlmm'2, hlmm'nn 0]⟩,
      hue.symm⟩
  have hlmm'pos : ∀ j : Fin 3, 0 < lmm' j := fun j ↦
    lt_of_le_of_ne (hlmm'nn j) (by fin_cases j <;> exact Ne.symm (by assumption))
  -- Degenerate triangle at `t'`: collinear, so its hull is a segment.
  by_cases hdep : LinearIndependent ℝ ![slidePt y z 3 t' - slidePt y z 2 t',
      slidePt y z 4 t' - slidePt y z 2 t']
  swap
  · have hcol := collinear_triple_of_dep hdep
    obtain hw | hw | hw := hcol.wbtw_or_wbtw_or_wbtw
    · -- `w₃ ∈ [w₂, w₄]`
      refine ⟨t', ht'I, u, huseg, Or.inr (Or.inr (Or.inl ?_))⟩
      rw [segment_symm]
      have hsub : ({slidePt y z 2 t', slidePt y z 3 t', slidePt y z 4 t'} :
          Set (Euc 3)) ⊆
          convexHull ℝ ({slidePt y z 2 t', slidePt y z 4 t'} : Set (Euc 3)) := by
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl
        · exact subset_convexHull ℝ _ (Set.mem_insert _ _)
        · rw [convexHull_pair]
          exact mem_segment_iff_wbtw.mpr hw
        · exact subset_convexHull ℝ _
            (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
      have hinc := convexHull_min hsub (convex_convexHull ℝ _)
      rw [convexHull_pair] at hinc
      exact hinc hutri
    · -- `w₄ ∈ [w₃, w₂]`
      refine ⟨t', ht'I, u, huseg, Or.inl ?_⟩
      have hsub : ({slidePt y z 2 t', slidePt y z 3 t', slidePt y z 4 t'} :
          Set (Euc 3)) ⊆
          convexHull ℝ ({slidePt y z 3 t', slidePt y z 2 t'} : Set (Euc 3)) := by
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl
        · exact subset_convexHull ℝ _
            (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
        · exact subset_convexHull ℝ _ (Set.mem_insert _ _)
        · rw [convexHull_pair]
          exact mem_segment_iff_wbtw.mpr hw
      have hinc := convexHull_min hsub (convex_convexHull ℝ _)
      rw [convexHull_pair, segment_symm] at hinc
      exact hinc hutri
    · -- `w₂ ∈ [w₄, w₃]`
      refine ⟨t', ht'I, u, huseg, Or.inr (Or.inl ?_)⟩
      have hsub : ({slidePt y z 2 t', slidePt y z 3 t', slidePt y z 4 t'} :
          Set (Euc 3)) ⊆
          convexHull ℝ ({slidePt y z 4 t', slidePt y z 3 t'} : Set (Euc 3)) := by
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl
        · rw [convexHull_pair]
          exact mem_segment_iff_wbtw.mpr hw
        · exact subset_convexHull ℝ _
            (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
        · exact subset_convexHull ℝ _ (Set.mem_insert _ _)
      have hinc := convexHull_min hsub (convex_convexHull ℝ _)
      rw [convexHull_pair, segment_symm] at hinc
      exact hinc hutri
  -- The segment direction `d` relative to the triangle plane.
  by_cases hspan : slidePt y z 1 t' - slidePt y z 0 t' ∈
      Submodule.span ℝ ({slidePt y z 3 t' - slidePt y z 2 t',
        slidePt y z 4 t' - slidePt y z 2 t'} : Set (Euc 3))
  · -- in-plane contact: push `u` inside the segment to the triangle boundary.
    obtain ⟨γ1, γ2, hγ⟩ := Submodule.mem_span_pair.mp hspan
    set gv : Fin 3 → ℝ := ![-(γ1 + γ2), γ1, γ2] with hgvdef
    by_cases hgam : ∃ j : Fin 3, gv j < 0
    swap
    · -- `gv ≥ 0` with `∑ gv = 0` forces `d = 0`, i.e. `u = w₀`.
      push Not at hgam
      have hg1 : γ1 = 0 := by
        have h1 : 0 ≤ γ1 := by
          have htmp := hgam 1
          simpa only [hgvdef, Matrix.cons_val] using htmp
        have h2 : 0 ≤ γ2 := by
          have htmp := hgam 2
          simpa only [hgvdef, Matrix.cons_val] using htmp
        have h0 : 0 ≤ -(γ1 + γ2) := by
          have htmp := hgam 0
          simpa only [hgvdef, Matrix.cons_val] using htmp
        linarith
      have hg2 : γ2 = 0 := by
        have h1 : 0 ≤ γ1 := by
          have htmp := hgam 1
          simpa only [hgvdef, Matrix.cons_val] using htmp
        have h2 : 0 ≤ γ2 := by
          have htmp := hgam 2
          simpa only [hgvdef, Matrix.cons_val] using htmp
        have h0 : 0 ≤ -(γ1 + γ2) := by
          have htmp := hgam 0
          simpa only [hgvdef, Matrix.cons_val] using htmp
        linarith
      refine ⟨t', ht'I, u, huseg, Or.inr (Or.inr (Or.inr ⟨Or.inl ?_, hutri⟩))⟩
      have hd0 : slidePt y z 1 t' - slidePt y z 0 t' = 0 := by
        rw [← hγ, hg1, hg2]
        simp
      rw [hu, seg_smul_eq, hd0, smul_zero, add_zero]
    · -- genuinely in-plane: push `u` by `ε` along `d` until the segment
      -- endpoint or a barycentric coordinate hits the boundary.
      set F : Finset ℝ := (Finset.univ.filter fun j : Fin 3 ↦ gv j < 0).image
        (fun j ↦ lmm' j / (-gv j)) with hFdef
      have hFne : F.Nonempty := by
        obtain ⟨j, hj⟩ := hgam
        exact ⟨lmm' j / (-gv j), Finset.mem_image.mpr
          ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩⟩
      set εp := F.min' hFne with hεpdef
      obtain ⟨jM, hjMfilt, hjMeq⟩ :=
        Finset.mem_image.mp (Finset.min'_mem F hFne)
      have hjM : gv jM < 0 := (Finset.mem_filter.mp hjMfilt).2
      have hεppos : 0 < εp := by
        rw [hεpdef, ← hjMeq]
        exact div_pos (hlmm'pos jM) (neg_pos.mpr hjM)
      set εh := min εp (1 - σ') with hεhdef
      have hεhpos : 0 < εh := lt_min hεppos (sub_pos.mpr hσ'lt)
      have hεhle : ∀ j : Fin 3, gv j < 0 → εh ≤ lmm' j / (-gv j) := fun j hj ↦
        le_trans (min_le_left _ _)
          (Finset.min'_le _ _ (Finset.mem_image.mpr
            ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩))
      set lmm'' : Fin 3 → ℝ := fun j ↦ lmm' j + εh * gv j with hlmm''def
      have hlmm''nn : ∀ j : Fin 3, 0 ≤ lmm'' j := fun j ↦ by
        by_cases hj : gv j < 0
        · have hle := hεhle j hj
          rw [le_div_iff₀ (neg_pos.mpr hj), mul_neg] at hle
          simp only [hlmm''def]
          linarith
        · push Not at hj
          have h3 : 0 ≤ εh * gv j := mul_nonneg hεhpos.le hj
          simp only [hlmm''def]
          linarith [hlmm'nn j]
      have hgvsum : gv 0 + gv 1 + gv 2 = 0 := by
        simp only [hgvdef, Matrix.cons_val]
        ring
      have hlmm''sum : lmm'' 0 + lmm'' 1 + lmm'' 2 = 1 := by
        simp only [hlmm''def]
        linear_combination hlmm'sum3 + εh * hgvsum
      have hlmm''sumF : ∑ j : Fin 3, lmm'' j = 1 := by
        rw [Fin.sum_univ_three]
        exact hlmm''sum
      -- the pushed point `v`
      set σ'' := σ' + εh with hσ''def
      set v : Euc 3 := slidePt y z 0 t' +
        σ'' • (slidePt y z 1 t' - slidePt y z 0 t') with hvdef
      have hσ''I : σ'' ∈ Set.Icc 0 1 := ⟨by
          rw [hσ''def]
          linarith [hσ'pos, hεhpos], by
          rw [hσ''def, hεhdef]
          have h2 := min_le_right εp (1 - σ')
          linarith⟩
      have hvseg : v ∈ segment ℝ (slidePt y z 0 t') (slidePt y z 1 t') := by
        rw [hvdef, ← seg_smul_eq, segment_eq_image]
        exact ⟨σ'', hσ''I, rfl⟩
      have hsplit : ∑ j : Fin 3, gv j • slidePt y z (![2, 3, 4] j) t' =
          slidePt y z 1 t' - slidePt y z 0 t' := by
        rw [Fin.sum_univ_three]
        simp only [hgvdef, Matrix.cons_val]
        rw [← hγ]
        module
      have hsum : ∑ j : Fin 3, lmm'' j • slidePt y z (![2, 3, 4] j) t' =
          (∑ j : Fin 3, lmm' j • slidePt y z (![2, 3, 4] j) t') +
            εh • (∑ j : Fin 3, gv j • slidePt y z (![2, 3, 4] j) t') := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [hlmm''def, add_smul, smul_smul]
      have hvtri : v = ∑ j : Fin 3, lmm'' j • slidePt y z (![2, 3, 4] j) t' := by
        rw [hsum, hsplit, ← huV, hvdef, hσ''def, hu]
        module
      have hvconv : v ∈ convexHull ℝ
          ({slidePt y z 2 t', slidePt y z 3 t', slidePt y z 4 t'} : Set (Euc 3)) :=
        mem_convexHull_of_exists_fintype lmm''
          (fun j : Fin 3 ↦ slidePt y z (![2, 3, 4] j) t') hlmm''nn hlmm''sumF
          (fun j ↦ by fin_cases j <;> simp) hvtri.symm
      rcases min_choice εp (1 - σ') with hmin | hmin
      · -- `εh = εp`: coordinate `jM` of `lmm''` vanishes → `v` on the opposite
        -- edge.
        have h1 : εh = lmm' jM / (-gv jM) := by
          rw [hεhdef, hmin, hjMeq]
        have hlmm''jM : lmm'' jM = 0 := by
          simp only [hlmm''def]
          rw [h1]
          have hjM0 : gv jM ≠ 0 := ne_of_lt hjM
          field_simp
          ring
        fin_cases jM
        · -- `jM = 0`: `v = lmm''1 • w₃ + lmm''2 • w₄ ∈ [w₃, w₄]`
          have hlmm''0 : lmm'' 0 = 0 := hlmm''jM
          refine ⟨t', ht'I, v, hvseg, Or.inr (Or.inl ?_)⟩
          rw [segment_eq_image]
          refine ⟨lmm'' 2, ⟨hlmm''nn 2,
            by linarith [hlmm''sum, hlmm''0, hlmm''nn 1]⟩, ?_⟩
          have hv2 : v = (1 - lmm'' 2) • slidePt y z 3 t' +
              lmm'' 2 • slidePt y z 4 t' := by
            rw [hvtri, Fin.sum_univ_three]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
            rw [hlmm''0]
            simp only [zero_smul, zero_add]
            have hlmm1 : lmm'' 1 = 1 - lmm'' 2 := by linarith [hlmm''sum]
            rw [hlmm1]
          exact hv2.symm
        · -- `jM = 1`: `v = lmm''0 • w₂ + lmm''2 • w₄ ∈ [w₄, w₂]`
          have hlmm''1 : lmm'' 1 = 0 := hlmm''jM
          refine ⟨t', ht'I, v, hvseg, Or.inr (Or.inr (Or.inl ?_))⟩
          rw [segment_eq_image]
          refine ⟨lmm'' 0, ⟨hlmm''nn 0,
            by linarith [hlmm''sum, hlmm''1, hlmm''nn 2]⟩, ?_⟩
          have hv2 : v = (1 - lmm'' 0) • slidePt y z 4 t' +
              lmm'' 0 • slidePt y z 2 t' := by
            rw [hvtri, Fin.sum_univ_three]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
            rw [hlmm''1]
            simp only [zero_smul, add_zero]
            have hlmm2 : lmm'' 2 = 1 - lmm'' 0 := by linarith [hlmm''sum]
            rw [hlmm2]
            exact add_comm _ _
          exact hv2.symm
        · -- `jM = 2`: `v = lmm''0 • w₂ + lmm''1 • w₃ ∈ [w₂, w₃]`
          have hlmm''2 : lmm'' 2 = 0 := hlmm''jM
          refine ⟨t', ht'I, v, hvseg, Or.inl ?_⟩
          rw [segment_eq_image]
          refine ⟨lmm'' 1, ⟨hlmm''nn 1,
            by linarith [hlmm''sum, hlmm''nn 0, hlmm''2]⟩, ?_⟩
          have hv2 : v = (1 - lmm'' 1) • slidePt y z 2 t' +
              lmm'' 1 • slidePt y z 3 t' := by
            rw [hvtri, Fin.sum_univ_three]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
            rw [hlmm''2]
            simp only [zero_smul, add_zero]
            have hlmm0 : lmm'' 0 = 1 - lmm'' 1 := by linarith [hlmm''sum]
            rw [hlmm0]
          exact hv2.symm
      · -- `εh = 1 - σ'`: `σ'' = 1`, so `v = w₁` inside the triangle.
        have hσ''1 : σ'' = 1 := by
          rw [hσ''def, hεhdef, hmin]
          ring
        have hv1 : v = slidePt y z 1 t' := by
          rw [hvdef, hσ''1]
          module
        exact ⟨t', ht'I, v, hvseg, Or.inr (Or.inr (Or.inr ⟨Or.inr hv1, hvconv⟩))⟩
  · -- transversal contact: `det3 d e₁ e₂ ≠ 0`, so the contact persists to
    -- `t' + δ`, contradicting the maximality of `t'`.
    exfalso
    have hD : det3 (slidePt y z 1 t' - slidePt y z 0 t')
        (slidePt y z 3 t' - slidePt y z 2 t')
        (slidePt y z 4 t' - slidePt y z 2 t') ≠ 0 := det3_ne_zero hdep hspan
    have hwcont : ∀ j : Fin 5, Continuous fun t : ℝ ↦ slidePt y z j t :=
      fun j ↦ ((continuous_const.sub continuous_id').smul continuous_const).add
        (continuous_id'.smul continuous_const)
    set Dv : ℝ → ℝ := fun t ↦ det3 (slidePt y z 1 t - slidePt y z 0 t)
      (slidePt y z 3 t - slidePt y z 2 t) (slidePt y z 4 t - slidePt y z 2 t)
      with hDv
    set σf : ℝ → ℝ := fun t ↦
      det3 (slidePt y z 2 t - slidePt y z 0 t) (slidePt y z 3 t - slidePt y z 2 t)
        (slidePt y z 4 t - slidePt y z 2 t) / Dv t with hσf
    set αf : ℝ → ℝ := fun t ↦
      -det3 (slidePt y z 1 t - slidePt y z 0 t) (slidePt y z 2 t - slidePt y z 0 t)
        (slidePt y z 4 t - slidePt y z 2 t) / Dv t with hαf
    set βf : ℝ → ℝ := fun t ↦
      -det3 (slidePt y z 1 t - slidePt y z 0 t) (slidePt y z 3 t - slidePt y z 2 t)
        (slidePt y z 2 t - slidePt y z 0 t) / Dv t with hβf
    have hDcont : Continuous Dv := by
      simp only [hDv]
      exact det3_continuous.comp (((hwcont 1).sub (hwcont 0)).prodMk
        (((hwcont 3).sub (hwcont 2)).prodMk ((hwcont 4).sub (hwcont 2))))
    have hNσ : Continuous fun t : ℝ ↦ det3 (slidePt y z 2 t - slidePt y z 0 t)
        (slidePt y z 3 t - slidePt y z 2 t) (slidePt y z 4 t - slidePt y z 2 t) :=
      det3_continuous.comp (((hwcont 2).sub (hwcont 0)).prodMk
        (((hwcont 3).sub (hwcont 2)).prodMk ((hwcont 4).sub (hwcont 2))))
    have hNα : Continuous fun t : ℝ ↦ det3 (slidePt y z 1 t - slidePt y z 0 t)
        (slidePt y z 2 t - slidePt y z 0 t) (slidePt y z 4 t - slidePt y z 2 t) :=
      det3_continuous.comp (((hwcont 1).sub (hwcont 0)).prodMk
        (((hwcont 2).sub (hwcont 0)).prodMk ((hwcont 4).sub (hwcont 2))))
    have hNβ : Continuous fun t : ℝ ↦ det3 (slidePt y z 1 t - slidePt y z 0 t)
        (slidePt y z 3 t - slidePt y z 2 t) (slidePt y z 2 t - slidePt y z 0 t) :=
      det3_continuous.comp (((hwcont 1).sub (hwcont 0)).prodMk
        (((hwcont 3).sub (hwcont 2)).prodMk ((hwcont 2).sub (hwcont 0))))
    have hDv' : Dv t' ≠ 0 := hD
    -- the Cramer solution coincides with `(σ', lmm' 1, lmm' 2)` at `t'`
    have hkey : slidePt y z 2 t' - slidePt y z 0 t' =
        σ' • (slidePt y z 1 t' - slidePt y z 0 t') -
          lmm' 1 • (slidePt y z 3 t' - slidePt y z 2 t') -
          lmm' 2 • (slidePt y z 4 t' - slidePt y z 2 t') := by
      have heq' : (1 - σ') • slidePt y z 0 t' + σ' • slidePt y z 1 t' =
          lmm' 0 • slidePt y z 2 t' + lmm' 1 • slidePt y z 3 t' +
            lmm' 2 • slidePt y z 4 t' := by
        have h := hu.symm.trans huV
        rw [Fin.sum_univ_three] at h
        simpa only [Matrix.cons_val] using h
      have hsumv : (lmm' 0 + lmm' 1 + lmm' 2) • slidePt y z 2 t' =
          (1 : ℝ) • slidePt y z 2 t' := congrArg (· • _) hlmm'sum3
      linear_combination (norm := module) -heq' - hsumv
    have hNσ' : det3 (slidePt y z 2 t' - slidePt y z 0 t')
        (slidePt y z 3 t' - slidePt y z 2 t')
        (slidePt y z 4 t' - slidePt y z 2 t') = σ' * Dv t' := by
      rw [hkey]
      simp only [hDv, det3_sub_left, det3_smul_left, det3_self_left,
        det3_self_mid, mul_zero, sub_zero]
    have hNα' : det3 (slidePt y z 1 t' - slidePt y z 0 t')
        (slidePt y z 2 t' - slidePt y z 0 t')
        (slidePt y z 4 t' - slidePt y z 2 t') = -(lmm' 1) * Dv t' := by
      rw [hkey]
      simp only [hDv, det3_sub_mid, det3_smul_mid, det3_self_left,
        det3_self_right, mul_zero, sub_zero, zero_sub]
      ring
    have hNβ' : det3 (slidePt y z 1 t' - slidePt y z 0 t')
        (slidePt y z 3 t' - slidePt y z 2 t')
        (slidePt y z 2 t' - slidePt y z 0 t') = -(lmm' 2) * Dv t' := by
      rw [hkey]
      simp only [hDv, det3_sub_right, det3_smul_right, det3_self_mid,
        det3_self_right, mul_zero, sub_zero, zero_sub]
      ring
    have hσ'eq : σf t' = σ' := by
      simp only [hσf]
      rw [hNσ', mul_div_cancel_right₀ _ hDv']
    have hα'eq : αf t' = lmm' 1 := by
      simp only [hαf]
      rw [hNα']
      simp only [neg_mul, neg_neg, mul_div_cancel_right₀ _ hDv']
    have hβ'eq : βf t' = lmm' 2 := by
      simp only [hβf]
      rw [hNβ']
      simp only [neg_mul, neg_neg, mul_div_cancel_right₀ _ hDv']
    have hγ'eq : 1 - αf t' - βf t' = lmm' 0 := by
      rw [hα'eq, hβ'eq]
      linarith [hlmm'sum3]
    have hσcat : ContinuousAt σf t' := by
      rw [hσf]
      exact hNσ.continuousAt.div hDcont.continuousAt hDv'
    have hαcat : ContinuousAt αf t' := by
      rw [hαf]
      exact (hNα.continuousAt.neg).div hDcont.continuousAt hDv'
    have hβcat : ContinuousAt βf t' := by
      rw [hβf]
      exact (hNβ.continuousAt.neg).div hDcont.continuousAt hDv'
    have hγcat : ContinuousAt (fun t : ℝ ↦ 1 - αf t - βf t) t' :=
      (continuousAt_const.sub hαcat).sub hβcat
    have E1 : ∀ᶠ t in 𝓝 t', σf t ∈ Set.Ioo 0 1 :=
      hσcat.eventually (isOpen_Ioo.mem_nhds
        (by rw [hσ'eq]; exact ⟨hσ'pos, hσ'lt⟩))
    have E2 : ∀ᶠ t in 𝓝 t', 0 < αf t :=
      hαcat.eventually (isOpen_Ioi.mem_nhds (by rw [hα'eq]; exact hlmm'pos 1))
    have E3 : ∀ᶠ t in 𝓝 t', 0 < βf t :=
      hβcat.eventually (isOpen_Ioi.mem_nhds (by rw [hβ'eq]; exact hlmm'pos 2))
    have E4 : ∀ᶠ t in 𝓝 t', 0 < 1 - αf t - βf t :=
      hγcat.eventually (isOpen_Ioi.mem_nhds
        (by show 1 - αf t' - βf t' ∈ Set.Ioi 0
            rw [hγ'eq]; exact hlmm'pos 0))
    have E5 : ∀ᶠ t in 𝓝 t', Dv t ≠ 0 :=
      hDcont.continuousAt.eventually_ne hDv'
    obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.mp
      (E1.and (E2.and (E3.and (E4.and E5))))
    set δ := min (ε / 2) ((1 - t') / 2) with hδdef
    have hδpos : 0 < δ := lt_min (half_pos hε) (half_pos (sub_pos.mpr ht'lt))
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    set tt := t' + δ with httdef
    have htt : t' < tt := by
      rw [httdef]
      exact lt_add_of_pos_right _ hδpos
    have htt1 : tt < 1 := by
      have h1 := min_le_right (ε / 2) ((1 - t') / 2)
      rw [httdef, hδdef]
      linarith [ht'lt]
    have hd : dist tt t' = δ := by
      rw [httdef, dist_eq_norm]
      simp [abs_of_nonneg hδpos.le]
    have hdε : dist tt t' < ε := hd ▸ hδε
    obtain ⟨hσ'I', hα'pos, hβ'pos, hγ'pos, hDt'⟩ := hε' hdε
    set σ'' := σf tt with hσ''def
    set α' := αf tt with hα'def
    set β' := βf tt with hβ'def
    -- the Cramer equation at `tt`
    have hDv2 : det3 (slidePt y z 1 tt - slidePt y z 0 tt)
        (slidePt y z 3 tt - slidePt y z 2 tt)
        (slidePt y z 4 tt - slidePt y z 2 tt) ≠ 0 := hDt'
    have hcra := det3_cramer (slidePt y z 1 tt - slidePt y z 0 tt)
      (slidePt y z 3 tt - slidePt y z 2 tt)
      (slidePt y z 4 tt - slidePt y z 2 tt)
      (slidePt y z 2 tt - slidePt y z 0 tt)
    have heq' : σ'' • (slidePt y z 1 tt - slidePt y z 0 tt) -
        α' • (slidePt y z 3 tt - slidePt y z 2 tt) -
        β' • (slidePt y z 4 tt - slidePt y z 2 tt) =
        slidePt y z 2 tt - slidePt y z 0 tt := by
      rw [show slidePt y z 2 tt - slidePt y z 0 tt =
          (det3 (slidePt y z 1 tt - slidePt y z 0 tt)
            (slidePt y z 3 tt - slidePt y z 2 tt)
            (slidePt y z 4 tt - slidePt y z 2 tt))⁻¹ •
            (det3 (slidePt y z 1 tt - slidePt y z 0 tt)
              (slidePt y z 3 tt - slidePt y z 2 tt)
              (slidePt y z 4 tt - slidePt y z 2 tt) •
              (slidePt y z 2 tt - slidePt y z 0 tt))
        from (inv_smul_smul₀ hDv2 _).symm]
      rw [hcra]
      simp only [smul_add, smul_smul, hσ''def, hα'def, hβ'def, hσf, hαf, hβf,
        hDv, div_eq_mul_inv]
      module
    -- `(tt, σ'', ![1-α'-β', α', β'])` is a contact parameter.
    have hmem' : (tt, σ'', ![1 - α' - β', α', β']) ∈ contactBox y z := by
      simp only [contactBox, Set.mem_ofPred_eq]
      refine ⟨⟨le_trans ht'I.1 htt.le, htt1.le⟩, ⟨hσ'I'.1.le, hσ'I'.2.le⟩,
        ?_, ?_, ?_⟩
      · intro j
        fin_cases j <;> simp only
        · exact hγ'pos.le
        · exact hα'pos.le
        · exact hβ'pos.le
      · rw [Fin.sum_univ_three]
        simp only [Matrix.cons_val]
        ring
      · rw [seg_smul_eq]
        calc slidePt y z 0 tt + σ'' • (slidePt y z 1 tt - slidePt y z 0 tt)
            = slidePt y z 0 tt +
                (σ'' • (slidePt y z 1 tt - slidePt y z 0 tt) -
                  α' • (slidePt y z 3 tt - slidePt y z 2 tt) -
                  β' • (slidePt y z 4 tt - slidePt y z 2 tt)) +
                (α' • (slidePt y z 3 tt - slidePt y z 2 tt) +
                  β' • (slidePt y z 4 tt - slidePt y z 2 tt)) := by module
          _ = slidePt y z 0 tt + (slidePt y z 2 tt - slidePt y z 0 tt) +
                (α' • (slidePt y z 3 tt - slidePt y z 2 tt) +
                  β' • (slidePt y z 4 tt - slidePt y z 2 tt)) := by rw [heq']
          _ = ∑ j : Fin 3, ![1 - α' - β', α', β'] j •
                slidePt y z (![2, 3, 4] j) tt := by
            rw [Fin.sum_univ_three]
            simp only [Matrix.cons_val]
            module
    have htt'mem : tt ∈ Tset := ⟨_, hmem', rfl⟩
    have httle : tt ≤ t' := by
      have hs := le_csSup hTc.bddAbove htt'mem
      rwa [← ht'] at hs
    exact absurd httle (not_le.mpr htt)

/-- The convex hulls of the unions over two sign-separated index sets are
disjoint.  Kirchberger reduces an intersection to a configuration of at most
five points; the singleton cases are ruled out by `CollectionConvex`, the
`2+2` case by `TwoSeparated`, and the `2+3`/`3+2` cases by the sliding lemma
`slide_triangle_boundary` (moving the small witnesses to the separating
representatives `x i`, on opposite sides of `{f = c}`). -/
private lemma disjoint_hull_union {k : ℕ} (X : Fin k → Finset (Euc 3))
    (x : Fin k → Euc 3) (hx : ∀ i, x i ∈ X i)
    (hcc : CollectionConvex X) (hsep : TwoSeparated X)
    (f : Euc 3 →ₗ[ℝ] ℝ) (c : ℝ) (S T : Finset (Fin k))
    (hS : ∀ i ∈ S, c < f (x i)) (hT : ∀ i ∈ T, f (x i) < c) :
    Disjoint (convexHull ℝ ((S.biUnion X : Finset (Euc 3)) : Set (Euc 3)))
      (convexHull ℝ ((T.biUnion X : Finset (Euc 3)) : Set (Euc 3))) := by
  classical
  rw [Set.disjoint_left]
  intro q hqA hqB
  obtain ⟨A', B', hA', hB', hcard, hAB⟩ := kirchberger ⟨q, hqA, hqB⟩
  obtain ⟨q', hq'A, hq'B⟩ := hAB
  have hAne : A'.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hq'A
    simp at hq'A
  have hBne : B'.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hq'B
    simp at hq'B
  have hApos : 1 ≤ A'.card := Finset.card_pos.mpr hAne
  have hBpos : 1 ≤ B'.card := Finset.card_pos.mpr hBne
  -- index choices for the small witnesses
  have selA : ∀ a ∈ A', ∃ i : Fin k, i ∈ S ∧ a ∈ X i := fun a ha ↦
    Finset.mem_biUnion.mp (Finset.mem_coe.mp (hA' (Finset.mem_coe.mpr ha)))
  have selB : ∀ b ∈ B', ∃ i : Fin k, i ∈ T ∧ b ∈ X i := fun b hb ↦
    Finset.mem_biUnion.mp (Finset.mem_coe.mp (hB' (Finset.mem_coe.mpr hb)))
  have hne : ∀ i ∈ S, ∀ j ∈ T, i ≠ j := fun i hi j hj ↦ by
    rintro rfl
    exact absurd (lt_trans (hT i hj) (hS i hi)) (lt_irrefl _)
  -- `T`-indexed components avoid `i ∈ S`, and conversely
  have subT : ∀ j i : Fin k, j ∈ T → j ≠ i →
      (X j : Set (Euc 3)) ⊆ ⋃ l : Fin k, ⋃ _ : l ≠ i, (X l : Set (Euc 3)) :=
    fun j i _ hn v hv ↦ by
      simp only [Set.mem_iUnion]
      exact ⟨j, hn, hv⟩
  have subS : ∀ j i : Fin k, j ∈ S → j ≠ i →
      (X j : Set (Euc 3)) ⊆ ⋃ l : Fin k, ⋃ _ : l ≠ i, (X l : Set (Euc 3)) :=
    fun j i _ hn v hv ↦ by
      simp only [Set.mem_iUnion]
      exact ⟨j, hn, hv⟩
  by_cases hA1 : A'.card = 1
  · -- `#A' = 1`: the point `q'` is an element of `X_{i₀}`, `i₀ ∈ S`, inside
    -- `conv(⋃_{j≠i₀} Xⱼ)` — contradicting `CollectionConvex`.
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA1
    rw [Finset.coe_singleton, convexHull_singleton] at hq'A
    have hqa := Set.mem_singleton_iff.mp hq'A
    subst hqa
    obtain ⟨ia, hia, hai⟩ := selA q' (Finset.mem_singleton_self q')
    have hd := Set.disjoint_left.mp (hcc ia)
    have hq1 : q' ∈ convexHull ℝ (X ia : Set (Euc 3)) :=
      subset_convexHull ℝ _ hai
    have hq2 : q' ∈ convexHull ℝ
        (⋃ j : Fin k, ⋃ _ : j ≠ ia, (X j : Set (Euc 3))) :=
      convexHull_mono (Set.Subset.trans hB' (fun v hv ↦ by
        obtain ⟨j, hjT, hvj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hv)
        exact subT j ia hjT (hne ia hia j hjT).symm hvj)) hq'B
    exact absurd hq2 (hd hq1)
  by_cases hB1 : B'.card = 1
  · -- symmetric singleton case
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hB1
    rw [Finset.coe_singleton, convexHull_singleton] at hq'B
    have hqb := Set.mem_singleton_iff.mp hq'B
    subst hqb
    obtain ⟨ib, hib, hbi⟩ := selB q' (Finset.mem_singleton_self q')
    have hd := Set.disjoint_left.mp (hcc ib)
    have hq1 : q' ∈ convexHull ℝ (X ib : Set (Euc 3)) :=
      subset_convexHull ℝ _ hbi
    have hq2 : q' ∈ convexHull ℝ
        (⋃ j : Fin k, ⋃ _ : j ≠ ib, (X j : Set (Euc 3))) :=
      convexHull_mono (Set.Subset.trans hA' (fun v hv ↦ by
        obtain ⟨j, hjS, hvj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hv)
        exact subS j ib hjS (hne j hjS ib hib) hvj)) hq'A
    exact absurd hq2 (hd hq1)
  have hA2 : 2 ≤ A'.card := by omega
  have hB2 : 2 ≤ B'.card := by omega
  have hA3 : A'.card ≤ 3 := by omega
  have hB3 : B'.card ≤ 3 := by omega
  interval_cases hAc : A'.card
  · -- `#A' = 2`
    obtain ⟨a0, a1, ha01, rfl⟩ := Finset.card_eq_two.mp hAc
    rw [Finset.coe_pair, convexHull_pair] at hq'A
    obtain ⟨ia0, hia0, ha0i⟩ := selA a0 (Finset.mem_insert_self _ _)
    obtain ⟨ia1, hia1, ha1i⟩ := selA a1
      (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
    interval_cases hBc : B'.card
    · -- `#B' = 2`: two crossing segments give a `TwoSeparated` pair.
      obtain ⟨b0, b1, hb01, rfl⟩ := Finset.card_eq_two.mp hBc
      rw [Finset.coe_pair, convexHull_pair] at hq'B
      obtain ⟨ib0, hib0, hb0i⟩ := selB b0 (Finset.mem_insert_self _ _)
      obtain ⟨ib1, hib1, hb1i⟩ := selB b1
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
      have hq1 : q' ∈ convexHull ℝ ↑(X ia0 ∪ X ia1) :=
        (convex_convexHull ℝ _).segment_subset
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_union_left _ ha0i)))
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_union_right _ ha1i))) hq'A
      have hq2 : q' ∈ convexHull ℝ ↑(X ib0 ∪ X ib1) :=
        (convex_convexHull ℝ _).segment_subset
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_union_left _ hb0i)))
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_union_right _ hb1i))) hq'B
      exact (Set.disjoint_left.mp
        (hsep ia0 ia1 ib0 ib1 (hne ia0 hia0 ib0 hib0) (hne ia0 hia0 ib1 hib1)
          (hne ia1 hia1 ib0 hib0) (hne ia1 hia1 ib1 hib1))) hq1 hq2
    · -- `#B' = 3`: slide the segment–triangle configuration.
      obtain ⟨b0, b1, b2, hb01, hb02, hb12, rfl⟩ := Finset.card_eq_three.mp hBc
      obtain ⟨ib0, hib0, hb0i⟩ := selB b0 (Finset.mem_insert_self _ _)
      obtain ⟨ib1, hib1, hb1i⟩ := selB b1 (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert_self _ _)))
      obtain ⟨ib2, hib2, hb2i⟩ := selB b2 (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))))
      obtain ⟨t, htI, u, huseg, hflag⟩ := slide_triangle_boundary
        (y := ![a0, a1, b0, b1, b2])
        (z := ![x ia0, x ia1, x ib0, x ib1, x ib2])
        ⟨q', by simpa using hq'A, by simpa using hq'B⟩
        (by
          simp only [Matrix.cons_val]
          refine Set.disjoint_left.mpr fun v hv1 hv2 ↦ ?_
          have hv1' : c < f v :=
            (convex_halfSpace_gt f.isLinear c).segment_subset (hS ia0 hia0)
              (hS ia1 hia1) hv1
          have hv2' : f v < c := convexHull_min (fun w hw ↦ by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
            rcases hw with rfl | rfl | rfl
            · exact hT ib0 hib0
            · exact hT ib1 hib1
            · exact hT ib2 hib2) (convex_halfSpace_lt f.isLinear c) hv2
          linarith)
      -- every slid point stays inside its own component's convex hull
      have hwmem : ∀ (j : Fin 5) (i : Fin k),
          ![a0, a1, b0, b1, b2] j ∈ X i →
          ![x ia0, x ia1, x ib0, x ib1, x ib2] j ∈ X i →
          slidePt ![a0, a1, b0, b1, b2] ![x ia0, x ia1, x ib0, x ib1, x ib2] j t ∈
            convexHull ℝ ↑(X i) := fun j i hyi hzi ↦
        (convex_convexHull ℝ _).segment_subset
          (subset_convexHull ℝ _ hyi) (subset_convexHull ℝ _ hzi)
          (by rw [segment_eq_image]; exact ⟨t, htI, rfl⟩)
      have huS : u ∈ convexHull ℝ ↑(X ia0 ∪ X ia1) :=
        (convex_convexHull ℝ _).segment_subset
          (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
            (hwmem 0 ia0 ha0i (hx ia0)))
          (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
            (hwmem 1 ia1 ha1i (hx ia1))) huseg
      rcases hflag with hed23 | hed34 | hed42 | hend
      · -- `u` on the `b₀b₁` edge
        have huT : u ∈ convexHull ℝ ↑(X ib0 ∪ X ib1) :=
          (convex_convexHull ℝ _).segment_subset
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
              (hwmem 2 ib0 hb0i (hx ib0)))
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
              (hwmem 3 ib1 hb1i (hx ib1))) hed23
        exact (Set.disjoint_left.mp
          (hsep ia0 ia1 ib0 ib1 (hne ia0 hia0 ib0 hib0) (hne ia0 hia0 ib1 hib1)
            (hne ia1 hia1 ib0 hib0) (hne ia1 hia1 ib1 hib1))) huS huT
      · -- `u` on the `b₁b₂` edge
        have huT : u ∈ convexHull ℝ ↑(X ib1 ∪ X ib2) :=
          (convex_convexHull ℝ _).segment_subset
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
              (hwmem 3 ib1 hb1i (hx ib1)))
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
              (hwmem 4 ib2 hb2i (hx ib2))) hed34
        exact (Set.disjoint_left.mp
          (hsep ia0 ia1 ib1 ib2 (hne ia0 hia0 ib1 hib1) (hne ia0 hia0 ib2 hib2)
            (hne ia1 hia1 ib1 hib1) (hne ia1 hia1 ib2 hib2))) huS huT
      · -- `u` on the `b₂b₀` edge
        have huT : u ∈ convexHull ℝ ↑(X ib2 ∪ X ib0) :=
          (convex_convexHull ℝ _).segment_subset
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
              (hwmem 4 ib2 hb2i (hx ib2)))
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
              (hwmem 2 ib0 hb0i (hx ib0))) hed42
        exact (Set.disjoint_left.mp
          (hsep ia0 ia1 ib2 ib0 (hne ia0 hia0 ib2 hib2) (hne ia0 hia0 ib0 hib0)
            (hne ia1 hia1 ib2 hib2) (hne ia1 hia1 ib0 hib0))) huS huT
      · -- `u` is a segment endpoint lying in the `T`-triangle hull
        obtain rfl | rfl := hend.1
        · -- `u = w₀ ∈ conv X_{ia0}`, and `u ∈ conv(X_{ib0}∪X_{ib1}∪X_{ib2})`
          -- `⊆ conv(⋃_{j≠ia0} Xⱼ)`.
          have huA := hwmem 0 ia0 ha0i (hx ia0)
          have huU : slidePt ![a0, a1, b0, b1, b2] ![x ia0, x ia1, x ib0, x ib1,
              x ib2] 0 t ∈
              convexHull ℝ (⋃ j : Fin k, ⋃ _ : j ≠ ia0, (X j : Set (Euc 3))) :=
            convexHull_min (fun v hv ↦ by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
              rcases hv with rfl | rfl | rfl
              · exact convexHull_mono
                  (subT ib0 ia0 hib0 (hne ia0 hia0 ib0 hib0).symm)
                  (hwmem 2 ib0 hb0i (hx ib0))
              · exact convexHull_mono
                  (subT ib1 ia0 hib1 (hne ia0 hia0 ib1 hib1).symm)
                  (hwmem 3 ib1 hb1i (hx ib1))
              · exact convexHull_mono
                  (subT ib2 ia0 hib2 (hne ia0 hia0 ib2 hib2).symm)
                  (hwmem 4 ib2 hb2i (hx ib2))) (convex_convexHull ℝ _) hend.2
          exact (Set.disjoint_left.mp (hcc ia0)) huA huU
        · have huA := hwmem 1 ia1 ha1i (hx ia1)
          have huU :=
            convexHull_min (fun v hv ↦ by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
              rcases hv with rfl | rfl | rfl
              · exact convexHull_mono
                  (subT ib0 ia1 hib0 (hne ia1 hia1 ib0 hib0).symm)
                  (hwmem 2 ib0 hb0i (hx ib0))
              · exact convexHull_mono
                  (subT ib1 ia1 hib1 (hne ia1 hia1 ib1 hib1).symm)
                  (hwmem 3 ib1 hb1i (hx ib1))
              · exact convexHull_mono
                  (subT ib2 ia1 hib2 (hne ia1 hia1 ib2 hib2).symm)
                  (hwmem 4 ib2 hb2i (hx ib2))) (convex_convexHull ℝ _) hend.2
          exact (Set.disjoint_left.mp (hcc ia1)) huA huU
  · -- `#A' = 3`: symmetric sliding (segment on the `T`-side).
    obtain ⟨a0, a1, a2, ha01, ha02, ha12, rfl⟩ := Finset.card_eq_three.mp hAc
    obtain ⟨ia0, hia0, ha0i⟩ := selA a0 (Finset.mem_insert_self _ _)
    obtain ⟨ia1, hia1, ha1i⟩ := selA a1 (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert_self _ _)))
    obtain ⟨ia2, hia2, ha2i⟩ := selA a2 (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))))
    interval_cases hBc : B'.card
    · -- `#B' = 2`
      obtain ⟨b0, b1, hb01, rfl⟩ := Finset.card_eq_two.mp hBc
      rw [Finset.coe_pair, convexHull_pair] at hq'B
      obtain ⟨ib0, hib0, hb0i⟩ := selB b0 (Finset.mem_insert_self _ _)
      obtain ⟨ib1, hib1, hb1i⟩ := selB b1
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
      obtain ⟨t, htI, u, huseg, hflag⟩ := slide_triangle_boundary
        (y := ![b0, b1, a0, a1, a2])
        (z := ![x ib0, x ib1, x ia0, x ia1, x ia2])
        ⟨q', by simpa using hq'B, by simpa using hq'A⟩
        (by
          simp only [Matrix.cons_val]
          refine Set.disjoint_left.mpr fun v hv1 hv2 ↦ ?_
          have hv1' : f v < c :=
            (convex_halfSpace_lt f.isLinear c).segment_subset (hT ib0 hib0)
              (hT ib1 hib1) hv1
          have hv2' : c < f v := convexHull_min (fun w hw ↦ by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
            rcases hw with rfl | rfl | rfl
            · exact hS ia0 hia0
            · exact hS ia1 hia1
            · exact hS ia2 hia2) (convex_halfSpace_gt f.isLinear c) hv2
          linarith)
      have hwmem : ∀ (j : Fin 5) (i : Fin k),
          ![b0, b1, a0, a1, a2] j ∈ X i →
          ![x ib0, x ib1, x ia0, x ia1, x ia2] j ∈ X i →
          slidePt ![b0, b1, a0, a1, a2] ![x ib0, x ib1, x ia0, x ia1, x ia2] j t ∈
            convexHull ℝ ↑(X i) := fun j i hyi hzi ↦
        (convex_convexHull ℝ _).segment_subset
          (subset_convexHull ℝ _ hyi) (subset_convexHull ℝ _ hzi)
          (by rw [segment_eq_image]; exact ⟨t, htI, rfl⟩)
      have huT : u ∈ convexHull ℝ ↑(X ib0 ∪ X ib1) :=
        (convex_convexHull ℝ _).segment_subset
          (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
            (hwmem 0 ib0 hb0i (hx ib0)))
          (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
            (hwmem 1 ib1 hb1i (hx ib1))) huseg
      rcases hflag with hed01 | hed12 | hed20 | hend
      · -- `u` on the `a₀a₁` edge
        have huS : u ∈ convexHull ℝ ↑(X ia0 ∪ X ia1) :=
          (convex_convexHull ℝ _).segment_subset
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
              (hwmem 2 ia0 ha0i (hx ia0)))
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
              (hwmem 3 ia1 ha1i (hx ia1))) hed01
        exact (Set.disjoint_left.mp
          (hsep ia0 ia1 ib0 ib1 (hne ia0 hia0 ib0 hib0) (hne ia0 hia0 ib1 hib1)
            (hne ia1 hia1 ib0 hib0) (hne ia1 hia1 ib1 hib1))) huS huT
      · -- `u` on the `a₁a₂` edge
        have huS : u ∈ convexHull ℝ ↑(X ia1 ∪ X ia2) :=
          (convex_convexHull ℝ _).segment_subset
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
              (hwmem 3 ia1 ha1i (hx ia1)))
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
              (hwmem 4 ia2 ha2i (hx ia2))) hed12
        exact (Set.disjoint_left.mp
          (hsep ia1 ia2 ib0 ib1 (hne ia1 hia1 ib0 hib0) (hne ia1 hia1 ib1 hib1)
            (hne ia2 hia2 ib0 hib0) (hne ia2 hia2 ib1 hib1))) huS huT
      · -- `u` on the `a₂a₀` edge
        have huS : u ∈ convexHull ℝ ↑(X ia2 ∪ X ia0) :=
          (convex_convexHull ℝ _).segment_subset
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
              (hwmem 4 ia2 ha2i (hx ia2)))
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
              (hwmem 2 ia0 ha0i (hx ia0))) hed20
        exact (Set.disjoint_left.mp
          (hsep ia2 ia0 ib0 ib1 (hne ia2 hia2 ib0 hib0) (hne ia2 hia2 ib1 hib1)
            (hne ia0 hia0 ib0 hib0) (hne ia0 hia0 ib1 hib1))) huS huT
      · -- `u` is a `B'`-side endpoint inside the `A'`-triangle hull
        obtain rfl | rfl := hend.1
        · have huB := hwmem 0 ib0 hb0i (hx ib0)
          have huU :=
            convexHull_min (fun v hv ↦ by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
              rcases hv with rfl | rfl | rfl
              · exact convexHull_mono
                  (subS ia0 ib0 hia0 (hne ia0 hia0 ib0 hib0))
                  (hwmem 2 ia0 ha0i (hx ia0))
              · exact convexHull_mono
                  (subS ia1 ib0 hia1 (hne ia1 hia1 ib0 hib0))
                  (hwmem 3 ia1 ha1i (hx ia1))
              · exact convexHull_mono
                  (subS ia2 ib0 hia2 (hne ia2 hia2 ib0 hib0))
                  (hwmem 4 ia2 ha2i (hx ia2))) (convex_convexHull ℝ _) hend.2
          exact (Set.disjoint_left.mp (hcc ib0)) huB huU
        · have huB := hwmem 1 ib1 hb1i (hx ib1)
          have huU :=
            convexHull_min (fun v hv ↦ by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
              rcases hv with rfl | rfl | rfl
              · exact convexHull_mono
                  (subS ia0 ib1 hia0 (hne ia0 hia0 ib1 hib1))
                  (hwmem 2 ia0 ha0i (hx ia0))
              · exact convexHull_mono
                  (subS ia1 ib1 hia1 (hne ia1 hia1 ib1 hib1))
                  (hwmem 3 ia1 ha1i (hx ia1))
              · exact convexHull_mono
                  (subS ia2 ib1 hia2 (hne ia2 hia2 ib1 hib1))
                  (hwmem 4 ia2 ha2i (hx ia2))) (convex_convexHull ℝ _) hend.2
          exact (Set.disjoint_left.mp (hcc ib1)) huB huU
    · -- `#B' = 3`: `3 + 3 > 5`, impossible.
      omega

/-- The vertical unit vector in `Euc 3`. -/
private def z3 : Euc 3 := PiLp.single 2 (2 : Fin 3) (1 : ℝ)

private lemma z3_apply (i : Fin 3) : z3 i = if i = 2 then 1 else 0 := by
  rw [z3, PiLp.single_apply]

private lemma z3_apply_two : z3 (2 : Fin 3) = 1 := by simp [z3_apply]

private lemma z3_proj2 : proj2 z3 = 0 := by
  ext i
  have hi : (Fin.castSucc i) ≠ (2 : Fin 3) := by
    apply Fin.ne_of_val_ne
    have hv2 : (2 : Fin 3).val = 2 := rfl
    simp only [Fin.val_castSucc, hv2]
    have : i.val < 2 := i.isLt
    omega
  show z3 i.castSucc = 0
  simp [z3_apply, hi]

private lemma proj2_add_z3 (x : Euc 3) (σ : ℝ) :
    proj2 (x + σ • z3) = proj2 x := by
  rw [map_add, map_smul, z3_proj2, smul_zero, add_zero]

private lemma add_z3_two (x : Euc 3) (σ : ℝ) :
    (x + σ • z3) (2 : Fin 3) = x 2 + σ := by
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, z3_apply_two, mul_one]

private lemma sub_z3_two (x : Euc 3) (σ : ℝ) :
    (x - σ • z3) (2 : Fin 3) = x 2 - σ := by
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, z3_apply_two, mul_one]

private lemma proj2_sub_z3 (x : Euc 3) (σ : ℝ) :
    proj2 (x - σ • z3) = proj2 x := by
  rw [map_sub, map_smul, z3_proj2, smul_zero, sub_zero]

/-- `proj2` of a point of a convex hull lies in the hull of the `proj2`-image. -/
private lemma proj2_mem_convexHull {S : Set (Euc 3)} {x : Euc 3}
    (hx : x ∈ convexHull ℝ S) : proj2 x ∈ convexHull ℝ (proj2 '' S) := by
  have h : proj2 x ∈ proj2 '' convexHull ℝ S := ⟨x, hx, rfl⟩
  rwa [LinearMap.image_convexHull] at h

/-- `proj2` of a point of a segment lies in the projected segment. -/
private lemma proj2_mem_segment {a b x : Euc 3} (hx : x ∈ segment ℝ a b) :
    proj2 x ∈ segment ℝ (proj2 a) (proj2 b) := by
  rw [← convexHull_pair] at hx ⊢
  have := proj2_mem_convexHull hx
  rwa [Set.image_insert_eq, Set.image_singleton] at this

/-- `1-s`/`s` affine combination as a base point plus a scalar multiple of the
difference, in an arbitrary real module. -/
private lemma seg_smul_eq_mod {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : ℝ) (a b : V) : (1 - s) • a + s • b = a + s • (b - a) := by
  module

/-- If two planar segments share two distinct points, an endpoint of one lies
in the other segment. -/
private lemma seg_overlap_endpoint {p0 p1 q0 q1 : Euc 2}
    (hp : p0 ≠ p1)
    {α α' β β' : ℝ} (hα : α ∈ Set.Icc 0 1) (hα' : α' ∈ Set.Icc 0 1)
    (hβ : β ∈ Set.Icc 0 1) (hβ' : β' ∈ Set.Icc 0 1) (hαα' : α ≠ α')
    (e1 : (1 - α) • p0 + α • p1 = (1 - β) • q0 + β • q1)
    (e2 : (1 - α') • p0 + α' • p1 = (1 - β') • q0 + β' • q1) :
    q0 ∈ segment ℝ p0 p1 ∨ q1 ∈ segment ℝ p0 p1 ∨
      p0 ∈ segment ℝ q0 q1 ∨ p1 ∈ segment ℝ q0 q1 := by
  set d := p1 - p0 with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have e1' : p0 + α • d = q0 + β • (q1 - q0) := by
    rw [← seg_smul_eq_mod β q0 q1, ← e1, seg_smul_eq_mod α p0 p1, ← hd]
  have e2' : p0 + α' • d = q0 + β' • (q1 - q0) := by
    rw [← seg_smul_eq_mod β' q0 q1, ← e2, seg_smul_eq_mod α' p0 p1, ← hd]
  have hsub : (α - α') • d = (β - β') • (q1 - q0) := by
    linear_combination (norm := module) e1' - e2'
  have hββ' : β ≠ β' := by
    rintro rfl
    rw [sub_self, zero_smul] at hsub
    rcases smul_eq_zero.mp hsub with h | h
    · exact hαα' (sub_eq_zero.mp h)
    · exact hd0 h
  set c := (α - α') / (β - β') with hc
  have hdir : q1 - q0 = c • d := by
    have h : q1 - q0 = (β - β')⁻¹ • ((β - β') • (q1 - q0)) := by
      rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hββ'), one_smul]
    rw [h, ← hsub, smul_smul, hc]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  set u0 := α - β * c with hu0
  set u1 := u0 + c with hu1
  have hq0eq : q0 = p0 + u0 • d := by
    have e1'' : p0 + α • d = q0 + β • (c • d) := hdir ▸ e1'
    rw [hu0]
    linear_combination (norm := module) -e1''
  have hq1eq : q1 = p0 + u1 • d := by
    have h : q1 = q0 + (q1 - q0) := by module
    rw [h, hdir, hq0eq, hu1]
    module
  have hα'rel : α - α' = (β - β') * c := by
    have h1 : (α - α' - (β - β') * c) • d = 0 := by
      have h2 : (α - α') • d - (β - β') • (q1 - q0) = 0 :=
        sub_eq_zero.mpr hsub
      rw [hdir] at h2
      linear_combination (norm := module) h2
    rcases smul_eq_zero.mp h1 with h3 | h3
    · linarith
    · exact absurd h3 hd0
  have hmem : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ v : ℝ, v = u0 + θ * c →
      v ∈ Set.Icc (min u0 u1) (max u0 u1) := by
    intro θ hθ v hv
    rw [hv, hu1]
    rcases le_total u0 (u0 + c) with h | h
    · rw [min_eq_left h, max_eq_right h]
      constructor <;> nlinarith [hθ.1, hθ.2, h]
    · rw [min_eq_right h, max_eq_left h]
      constructor <;> nlinarith [hθ.1, hθ.2, h]
  have hαJ : α ∈ Set.Icc (min u0 u1) (max u0 u1) :=
    hmem β hβ α (by rw [hu0]; ring)
  have hα'J : α' ∈ Set.Icc (min u0 u1) (max u0 u1) :=
    hmem β' hβ' α' (by rw [hu0]; linear_combination -hα'rel)
  rcases em (u0 ∈ Set.Icc (0 : ℝ) 1) with hu0I | hu0I
  · refine Or.inl ?_
    rw [segment_eq_image]
    refine ⟨u0, hu0I, ?_⟩
    show (1 - u0) • p0 + u0 • p1 = q0
    rw [seg_smul_eq_mod]; exact hq0eq.symm
  rcases em (u1 ∈ Set.Icc (0 : ℝ) 1) with hu1I | hu1I
  · refine Or.inr (Or.inl ?_)
    rw [segment_eq_image]
    refine ⟨u1, hu1I, ?_⟩
    show (1 - u1) • p0 + u1 • p1 = q1
    rw [seg_smul_eq_mod]; exact hq1eq.symm
  -- both `u0, u1` outside `[0,1]`: then `[0,1] ⊆ J`, so `p0 ∈ [q0,q1]`.
  have hu0c : u0 < 0 ∨ 1 < u0 := by
    rcases lt_or_ge u0 0 with h | h
    · exact Or.inl h
    · rcases lt_or_ge 1 u0 with h' | h'
      · exact Or.inr h'
      · exact absurd ⟨h, h'⟩ hu0I
  have hu1c : u1 < 0 ∨ 1 < u1 := by
    rcases lt_or_ge u1 0 with h | h
    · exact Or.inl h
    · rcases lt_or_ge 1 u1 with h' | h'
      · exact Or.inr h'
      · exact absurd ⟨h, h'⟩ hu1I
  have hsgn : (u0 < 0 ∧ 1 < u1) ∨ (1 < u0 ∧ u1 < 0) := by
    rcases hu0c with hu0n | hu0p
    · rcases hu1c with hu1n | hu1p
      · exfalso
        have hm : max u0 u1 < 0 := max_lt hu0n hu1n
        linarith [hαJ.2, hα.1]
      · exact Or.inl ⟨hu0n, hu1p⟩
    · rcases hu1c with hu1n | hu1p
      · exact Or.inr ⟨hu0p, hu1n⟩
      · exfalso
        have hm : 1 < min u0 u1 := lt_min hu0p hu1p
        linarith [hα'J.1, hα'.2]
  have hne : u1 ≠ u0 := by
    rcases hsgn with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hJ0 : (0 : ℝ) ∈ Set.Icc (min u0 u1) (max u0 u1) := by
    rcases hsgn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [min_eq_left (le_of_lt (lt_trans h1 (lt_trans zero_lt_one h2))),
        max_eq_right (le_of_lt (lt_trans h1 (lt_trans zero_lt_one h2)))]
      exact ⟨h1.le, by linarith⟩
    · rw [min_eq_right (le_of_lt (lt_trans h2 (lt_trans zero_lt_one h1))),
        max_eq_left (le_of_lt (lt_trans h2 (lt_trans zero_lt_one h1)))]
      exact ⟨h2.le, by linarith⟩
  have hpar : ∀ v ∈ Set.Icc (min u0 u1) (max u0 u1),
      ∃ t ∈ Set.Icc (0 : ℝ) 1, v = u0 + t * (u1 - u0) := by
    intro v hv
    rcases lt_or_ge u0 u1 with h | h
    · rw [min_eq_left h.le, max_eq_right h.le] at hv
      refine ⟨(v - u0) / (u1 - u0), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (sub_nonneg.mpr hv.1) (sub_pos.mpr h).le
      · rw [div_le_one (sub_pos.mpr h)]
        exact sub_le_sub_right hv.2 _
      · rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm (ne_of_lt h)))]
        ring
    · have h' : u1 < u0 := lt_of_le_of_ne h hne
      rw [min_eq_right h'.le, max_eq_left h'.le] at hv
      refine ⟨(v - u0) / (u1 - u0), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg_of_nonpos (sub_nonpos.mpr hv.2) (sub_nonpos.mpr h'.le)
      · rw [div_le_iff_of_neg (sub_neg.mpr h')]
        linarith [hv.1]
      · rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_lt h'))]
        ring
  obtain ⟨t0, ht0, ht0e⟩ := hpar 0 hJ0
  have hdir2 : (u1 - u0) • d = q1 - q0 := by
    rw [hu1, hdir]
    module
  have hp0eq : p0 = (1 - t0) • q0 + t0 • q1 := by
    have key : t0 * (u1 - u0) = -u0 := by linarith [ht0e]
    have key' : (t0 * (u1 - u0)) • d = (-u0) • d := congrArg (· • d) key
    rw [seg_smul_eq_mod, ← hdir2]
    linear_combination (norm := module) -hq0eq - key'
  refine Or.inr (Or.inr (Or.inl ?_))
  rw [segment_eq_image]
  refine ⟨t0, ht0, ?_⟩
  show (1 - t0) • q0 + t0 • q1 = p0
  exact hp0eq.symm

/-- **Proposition 2.3, core.**  If the four projected sets are in convex
position (`hconv`) and every `X₁X₃` segment lies strictly above every `X₂X₄`
segment at their (necessarily interior) projected crossings (`habove`), then
`conv(X₁∪X₃)` and `conv(X₂∪X₄)` are disjoint. -/
private lemma conv13_conv24_disjoint {X1 X2 X3 X4 : Finset (Euc 3)}
    (hconv : ∀ i : Fin 4, Disjoint
      (convexHull ℝ (proj2 ''
        ((![X1, X2, X3, X4] i : Finset (Euc 3)) : Set (Euc 3))))
      (convexHull ℝ (⋃ j : Fin 4, ⋃ _ : j ≠ i,
        proj2 '' ((![X1, X2, X3, X4] j : Finset (Euc 3)) : Set (Euc 3)))))
    (habove : ∀ x1 ∈ X1, ∀ x2 ∈ X2, ∀ x3 ∈ X3, ∀ x4 ∈ X4,
      AboveSeg x1 x3 x2 x4) :
    Disjoint (convexHull ℝ ((X1 ∪ X3 : Finset (Euc 3)) : Set (Euc 3)))
             (convexHull ℝ ((X2 ∪ X4 : Finset (Euc 3)) : Set (Euc 3))) := by
  classical
  rw [Set.disjoint_left]
  intro q hqA hqB
  -- `hpt i v`: a projected point in both the class-`i` hull and the hull of
  -- the remaining classes contradicts `hconv i`.
  have hpt : ∀ i : Fin 4, ∀ v : Euc 2,
      v ∈ convexHull ℝ (proj2 ''
        ((![X1, X2, X3, X4] i : Finset (Euc 3)) : Set (Euc 3))) →
      v ∈ convexHull ℝ (⋃ j : Fin 4, ⋃ _ : j ≠ i,
        proj2 '' ((![X1, X2, X3, X4] j : Finset (Euc 3)) : Set (Euc 3))) →
      False := fun i v h1 h2 ↦ Set.disjoint_left.mp (hconv i) h1 h2
  -- a class-`i` point projects into its own hull
  have hown : ∀ {i : Fin 4} {x : Euc 3},
      x ∈ (![X1, X2, X3, X4] i : Finset (Euc 3)) →
      proj2 x ∈ convexHull ℝ (proj2 ''
        ((![X1, X2, X3, X4] i : Finset (Euc 3)) : Set (Euc 3))) := by
    intro i x hx
    exact subset_convexHull ℝ _ ⟨x, Finset.mem_coe.mpr hx, rfl⟩
  -- a class-`j` point projects into the `i`-rest hull when `j ≠ i`
  have hrest : ∀ {j i : Fin 4}, j ≠ i → ∀ {x : Euc 3},
      x ∈ (![X1, X2, X3, X4] j : Finset (Euc 3)) →
      proj2 x ∈ convexHull ℝ (⋃ l : Fin 4, ⋃ _ : l ≠ i,
        proj2 '' ((![X1, X2, X3, X4] l : Finset (Euc 3)) : Set (Euc 3))) := by
    intro j i hji x hx
    exact subset_convexHull ℝ _
      (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji,
        ⟨x, Finset.mem_coe.mpr hx, rfl⟩⟩⟩)
  -- `conv (proj2 '' (X1∪X3))` is inside the `i`-rest hull for `i ∉ {0,2}`
  have subA : ∀ i : Fin 4, i ≠ 0 → i ≠ 2 →
      convexHull ℝ (proj2 '' ((X1 ∪ X3 : Finset (Euc 3)) : Set (Euc 3))) ⊆
        convexHull ℝ (⋃ j : Fin 4, ⋃ _ : j ≠ i,
          proj2 '' ((![X1, X2, X3, X4] j : Finset (Euc 3)) : Set (Euc 3))) := by
    intro i hi0 hi2
    apply convexHull_mono
    rintro v ⟨x, hx, rfl⟩
    rw [Finset.mem_coe, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨Ne.symm hi0,
        ⟨x, Finset.mem_coe.mpr (by simpa using hx), rfl⟩⟩⟩
    · exact Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨Ne.symm hi2,
        ⟨x, Finset.mem_coe.mpr (by simpa using hx), rfl⟩⟩⟩
  -- `conv (proj2 '' (X2∪X4))` is inside the `i`-rest hull for `i ∉ {1,3}`
  have subB : ∀ i : Fin 4, i ≠ 1 → i ≠ 3 →
      convexHull ℝ (proj2 '' ((X2 ∪ X4 : Finset (Euc 3)) : Set (Euc 3))) ⊆
        convexHull ℝ (⋃ j : Fin 4, ⋃ _ : j ≠ i,
          proj2 '' ((![X1, X2, X3, X4] j : Finset (Euc 3)) : Set (Euc 3))) := by
    intro i hi1 hi3
    apply convexHull_mono
    rintro v ⟨x, hx, rfl⟩
    rw [Finset.mem_coe, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨Ne.symm hi1,
        ⟨x, Finset.mem_coe.mpr (by simpa using hx), rfl⟩⟩⟩
    · exact Set.mem_iUnion.mpr ⟨3, Set.mem_iUnion.mpr ⟨Ne.symm hi3,
        ⟨x, Finset.mem_coe.mpr (by simpa using hx), rfl⟩⟩⟩
  -- push a hull membership through a set inclusion, then project
  have hullmem : ∀ {S T : Finset (Euc 3)} {v : Euc 3}, v ∈ convexHull ℝ ↑S →
      ↑S ⊆ ↑T →
      proj2 v ∈ convexHull ℝ (proj2 '' (↑T : Set (Euc 3))) := by
    intro S T v hv hST
    exact convexHull_mono (Set.image_mono hST) (proj2_mem_convexHull hv)
  -- `proj2 v` is in `conv (proj2 '' (X1∪X3))` for `v` on a `13`-segment
  have hull13 : ∀ {v x y : Euc 3}, v ∈ segment ℝ x y →
      x ∈ (X1 ∪ X3 : Finset (Euc 3)) → y ∈ (X1 ∪ X3 : Finset (Euc 3)) →
      proj2 v ∈ convexHull ℝ
        (proj2 '' ((X1 ∪ X3 : Finset (Euc 3)) : Set (Euc 3))) := by
    intro v x y hv hx hy
    exact hullmem (by rwa [Finset.coe_pair, convexHull_pair])
      (Finset.coe_subset.mpr (Finset.insert_subset_iff.mpr
        ⟨hx, Finset.singleton_subset_iff.mpr hy⟩))
  -- `proj2 v` is in `conv (proj2 '' (X2∪X4))` for `v` on a `24`-segment
  have hull24 : ∀ {v x y : Euc 3}, v ∈ segment ℝ x y →
      x ∈ (X2 ∪ X4 : Finset (Euc 3)) → y ∈ (X2 ∪ X4 : Finset (Euc 3)) →
      proj2 v ∈ convexHull ℝ
        (proj2 '' ((X2 ∪ X4 : Finset (Euc 3)) : Set (Euc 3))) := by
    intro v x y hv hx hy
    exact hullmem (by rwa [Finset.coe_pair, convexHull_pair])
      (Finset.coe_subset.mpr (Finset.insert_subset_iff.mpr
        ⟨hx, Finset.singleton_subset_iff.mpr hy⟩))
  -- a projected point on the join of two class-`i` points is in the class hull
  have segown : ∀ (i : Fin 4) {v x y : Euc 3},
      x ∈ (![X1, X2, X3, X4] i : Finset (Euc 3)) →
      y ∈ (![X1, X2, X3, X4] i : Finset (Euc 3)) →
      proj2 v ∈ segment ℝ (proj2 x) (proj2 y) →
      proj2 v ∈ convexHull ℝ (proj2 ''
        ((![X1, X2, X3, X4] i : Finset (Euc 3)) : Set (Euc 3))) := by
    intro i v x y hx hy hseg
    have h1 : proj2 v ∈ convexHull ℝ ({proj2 x, proj2 y} : Set (Euc 2)) := by
      rw [convexHull_pair]; exact hseg
    refine convexHull_mono ?_ h1
    rintro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact ⟨x, Finset.mem_coe.mpr hx, rfl⟩
    · exact ⟨y, Finset.mem_coe.mpr hy, rfl⟩
  -- the segment–segment lemma: an `X₁X₃` segment shifted up by `σa` cannot
  -- meet an `X₂X₄` segment shifted vertically by `σb ≤ σa`.
  have segseg : ∀ {a0' a1' b0' b1' : Euc 3} {σa σb : ℝ}, σb ≤ σa →
      a0' ∈ X1 → a1' ∈ X3 → b0' ∈ X2 → b1' ∈ X4 →
      ∀ {u : Euc 3}, u ∈ segment ℝ (a0' + σa • z3) (a1' + σa • z3) →
      u ∈ segment ℝ (b0' + σb • z3) (b1' + σb • z3) → False := by
    intro a0' a1' b0' b1' σa σb hσ ha0 ha1 hb0 hb1 u huA huB
    rw [segment_eq_image] at huA huB
    obtain ⟨α, hα, hAeq⟩ := huA
    obtain ⟨β, hβ, hBeq⟩ := huB
    have hAeq' : (1 - α) • a0' + α • a1' + σa • z3 = u := by
      rw [← hAeq]
      show (1 - α) • a0' + α • a1' + σa • z3 =
        (1 - α) • (a0' + σa • z3) + α • (a1' + σa • z3)
      module
    have hBeq' : (1 - β) • b0' + β • b1' + σb • z3 = u := by
      rw [← hBeq]
      show (1 - β) • b0' + β • b1' + σb • z3 =
        (1 - β) • (b0' + σb • z3) + β • (b1' + σb • z3)
      module
    have hru : proj2 u = (1 - α) • proj2 a0' + α • proj2 a1' := by
      rw [← hAeq']
      simp only [map_add, map_smul, z3_proj2, smul_zero, add_zero]
    have hrv : proj2 u = (1 - β) • proj2 b0' + β • proj2 b1' := by
      rw [← hBeq']
      simp only [map_add, map_smul, z3_proj2, smul_zero, add_zero]
    -- the projected endpoints are distinct, else `hconv` is contradicted
    have hpa : proj2 a0' ≠ proj2 a1' := by
      intro h
      have h2 : proj2 a1' ∈ convexHull ℝ (⋃ j : Fin 4, ⋃ _ : j ≠ (0 : Fin 4),
          proj2 '' ((![X1, X2, X3, X4] j : Finset (Euc 3)) : Set (Euc 3))) :=
        hrest (show (2 : Fin 4) ≠ 0 by decide) (by simpa using ha1)
      rw [← h] at h2
      exact hpt 0 _ (hown (by simpa using ha0)) h2
    have hpb : proj2 b0' ≠ proj2 b1' := by
      intro h
      have h2 : proj2 b1' ∈ convexHull ℝ (⋃ j : Fin 4, ⋃ _ : j ≠ (1 : Fin 4),
          proj2 '' ((![X1, X2, X3, X4] j : Finset (Euc 3)) : Set (Euc 3))) :=
        hrest (show (3 : Fin 4) ≠ 1 by decide) (by simpa using hb1)
      rw [← h] at h2
      exact hpt 1 _ (hown (by simpa using hb0)) h2
    -- `proj2 u` sits in both union hulls
    have huA' : proj2 u ∈ convexHull ℝ
        (proj2 '' ((X1 ∪ X3 : Finset (Euc 3)) : Set (Euc 3))) := by
      have h1 : proj2 u ∈ convexHull ℝ
          ({proj2 a0', proj2 a1'} : Set (Euc 2)) := by
        rw [convexHull_pair, segment_eq_image]
        exact ⟨α, hα, hru.symm⟩
      refine convexHull_mono ?_ h1
      rintro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨a0', Finset.mem_coe.mpr (Finset.mem_union_left _ ha0), rfl⟩
      · exact ⟨a1', Finset.mem_coe.mpr (Finset.mem_union_right _ ha1), rfl⟩
    have huB' : proj2 u ∈ convexHull ℝ
        (proj2 '' ((X2 ∪ X4 : Finset (Euc 3)) : Set (Euc 3))) := by
      have h1 : proj2 u ∈ convexHull ℝ
          ({proj2 b0', proj2 b1'} : Set (Euc 2)) := by
        rw [convexHull_pair, segment_eq_image]
        exact ⟨β, hβ, hrv.symm⟩
      refine convexHull_mono ?_ h1
      rintro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨b0', Finset.mem_coe.mpr (Finset.mem_union_left _ hb0), rfl⟩
      · exact ⟨b1', Finset.mem_coe.mpr (Finset.mem_union_right _ hb1), rfl⟩
    -- endpoint meetings are excluded by `hconv`
    rcases eq_or_ne α 0 with hα0 | hα0
    · have hp : (1 - β) • proj2 b0' + β • proj2 b1' = proj2 a0' := by
        have hp0 : proj2 u = proj2 a0' := by
          rw [hα0] at hru; simpa using hru
        rw [hp0] at hrv; exact hrv.symm
      have hseg : proj2 a0' ∈ segment ℝ (proj2 b0') (proj2 b1') := by
        rw [segment_eq_image]; exact ⟨β, hβ, hp⟩
      have h1 : proj2 a0' ∈ convexHull ℝ
          ({proj2 b0', proj2 b1'} : Set (Euc 2)) := by
        rwa [convexHull_pair]
      refine hpt 0 _ (hown (by simpa using ha0))
        (subB 0 (by decide) (by decide) (convexHull_mono ?_ h1))
      rintro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨b0', Finset.mem_coe.mpr (Finset.mem_union_left _ hb0), rfl⟩
      · exact ⟨b1', Finset.mem_coe.mpr (Finset.mem_union_right _ hb1), rfl⟩
    rcases eq_or_ne α 1 with hα1 | hα1
    · have hp : (1 - β) • proj2 b0' + β • proj2 b1' = proj2 a1' := by
        have hp0 : proj2 u = proj2 a1' := by
          rw [hα1] at hru; simpa using hru
        rw [hp0] at hrv; exact hrv.symm
      have hseg : proj2 a1' ∈ segment ℝ (proj2 b0') (proj2 b1') := by
        rw [segment_eq_image]; exact ⟨β, hβ, hp⟩
      have h1 : proj2 a1' ∈ convexHull ℝ
          ({proj2 b0', proj2 b1'} : Set (Euc 2)) := by
        rwa [convexHull_pair]
      refine hpt 2 _ (hown (by simpa using ha1))
        (subB 2 (by decide) (by decide) (convexHull_mono ?_ h1))
      rintro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨b0', Finset.mem_coe.mpr (Finset.mem_union_left _ hb0), rfl⟩
      · exact ⟨b1', Finset.mem_coe.mpr (Finset.mem_union_right _ hb1), rfl⟩
    rcases eq_or_ne β 0 with hβ0 | hβ0
    · have hp : (1 - α) • proj2 a0' + α • proj2 a1' = proj2 b0' := by
        have hp0 : proj2 u = proj2 b0' := by
          rw [hβ0] at hrv; simpa using hrv
        rw [hp0] at hru; exact hru.symm
      have hseg : proj2 b0' ∈ segment ℝ (proj2 a0') (proj2 a1') := by
        rw [segment_eq_image]; exact ⟨α, hα, hp⟩
      have h1 : proj2 b0' ∈ convexHull ℝ
          ({proj2 a0', proj2 a1'} : Set (Euc 2)) := by
        rwa [convexHull_pair]
      refine hpt 1 _ (hown (by simpa using hb0))
        (subA 1 (by decide) (by decide) (convexHull_mono ?_ h1))
      rintro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨a0', Finset.mem_coe.mpr (Finset.mem_union_left _ ha0), rfl⟩
      · exact ⟨a1', Finset.mem_coe.mpr (Finset.mem_union_right _ ha1), rfl⟩
    rcases eq_or_ne β 1 with hβ1 | hβ1
    · have hp : (1 - α) • proj2 a0' + α • proj2 a1' = proj2 b1' := by
        have hp0 : proj2 u = proj2 b1' := by
          rw [hβ1] at hrv; simpa using hrv
        rw [hp0] at hru; exact hru.symm
      have hseg : proj2 b1' ∈ segment ℝ (proj2 a0') (proj2 a1') := by
        rw [segment_eq_image]; exact ⟨α, hα, hp⟩
      have h1 : proj2 b1' ∈ convexHull ℝ
          ({proj2 a0', proj2 a1'} : Set (Euc 2)) := by
        rwa [convexHull_pair]
      refine hpt 3 _ (hown (by simpa using hb1))
        (subA 3 (by decide) (by decide) (convexHull_mono ?_ h1))
      rintro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨a0', Finset.mem_coe.mpr (Finset.mem_union_left _ ha0), rfl⟩
      · exact ⟨a1', Finset.mem_coe.mpr (Finset.mem_union_right _ ha1), rfl⟩
    -- interior parameters: use `AboveSeg`
    obtain ⟨s, t, hs0, hs1, ht0, ht1, hproj, hgt⟩ :=
      habove a0' ha0 b0' hb0 a1' ha1 b1' hb1
    have hproj' : (1 - s) • proj2 a0' + s • proj2 a1' =
        (1 - t) • proj2 b0' + t • proj2 b1' := by
      simp only [← map_smul, ← map_add]
      exact hproj
    by_cases hrr : proj2 u = (1 - s) • proj2 a0' + s • proj2 a1'
    · -- the meeting projection is the `AboveSeg` crossing: heights collide
      have hαs : α = s := by
        have e : (1 - α) • proj2 a0' + α • proj2 a1' =
            (1 - s) • proj2 a0' + s • proj2 a1' := hru.symm.trans hrr
        have e2 : α • (proj2 a1' - proj2 a0') =
            s • (proj2 a1' - proj2 a0') := by
          rw [seg_smul_eq_mod, seg_smul_eq_mod] at e
          linear_combination (norm := module) e
        rcases smul_eq_zero.mp (show (α - s) • (proj2 a1' - proj2 a0') = 0
            from by linear_combination (norm := module) e2) with h | h
        · linarith
        · exact absurd (sub_eq_zero.mp h) (Ne.symm hpa)
      have hβt : β = t := by
        have e : (1 - β) • proj2 b0' + β • proj2 b1' =
            (1 - t) • proj2 b0' + t • proj2 b1' :=
          hrv.symm.trans (hrr.trans hproj')
        have e2 : β • (proj2 b1' - proj2 b0') =
            t • (proj2 b1' - proj2 b0') := by
          rw [seg_smul_eq_mod, seg_smul_eq_mod] at e
          linear_combination (norm := module) e
        rcases smul_eq_zero.mp (show (β - t) • (proj2 b1' - proj2 b0') = 0
            from by linear_combination (norm := module) e2) with h | h
        · linarith
        · exact absurd (sub_eq_zero.mp h) (Ne.symm hpb)
      have hzu : u 2 = ((1 - s) • a0' + s • a1') 2 + σa := by
        have e : u = (1 - s) • a0' + s • a1' + σa • z3 := by
          rw [← hAeq', hαs]
        rw [e]
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, z3_apply_two,
          mul_one]
      have hzv : u 2 = ((1 - t) • b0' + t • b1') 2 + σb := by
        have e : u = (1 - t) • b0' + t • b1' + σb • z3 := by
          rw [← hBeq', hβt]
        rw [e]
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, z3_apply_two,
          mul_one]
      linarith [hgt]
    · -- two distinct common projected points: the segments overlap
      have hne2 : α ≠ s := by
        intro h'
        exact hrr (h' ▸ hru)
      rcases seg_overlap_endpoint hpa hα ⟨hs0.le, hs1.le⟩ hβ ⟨ht0.le, ht1.le⟩
          hne2 (hru.symm.trans hrv) hproj' with hL0 | hL1 | hU0 | hU1
      · have h1 : proj2 b0' ∈ convexHull ℝ
            ({proj2 a0', proj2 a1'} : Set (Euc 2)) := by
          rwa [convexHull_pair]
        refine hpt 1 _ (hown (by simpa using hb0))
          (subA 1 (by decide) (by decide) (convexHull_mono ?_ h1))
        rintro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact ⟨a0', Finset.mem_coe.mpr (Finset.mem_union_left _ ha0), rfl⟩
        · exact ⟨a1', Finset.mem_coe.mpr (Finset.mem_union_right _ ha1), rfl⟩
      · have h1 : proj2 b1' ∈ convexHull ℝ
            ({proj2 a0', proj2 a1'} : Set (Euc 2)) := by
          rwa [convexHull_pair]
        refine hpt 3 _ (hown (by simpa using hb1))
          (subA 3 (by decide) (by decide) (convexHull_mono ?_ h1))
        rintro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact ⟨a0', Finset.mem_coe.mpr (Finset.mem_union_left _ ha0), rfl⟩
        · exact ⟨a1', Finset.mem_coe.mpr (Finset.mem_union_right _ ha1), rfl⟩
      · have h1 : proj2 a0' ∈ convexHull ℝ
            ({proj2 b0', proj2 b1'} : Set (Euc 2)) := by
          rwa [convexHull_pair]
        refine hpt 0 _ (hown (by simpa using ha0))
          (subB 0 (by decide) (by decide) (convexHull_mono ?_ h1))
        rintro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact ⟨b0', Finset.mem_coe.mpr (Finset.mem_union_left _ hb0), rfl⟩
        · exact ⟨b1', Finset.mem_coe.mpr (Finset.mem_union_right _ hb1), rfl⟩
      · have h1 : proj2 a1' ∈ convexHull ℝ
            ({proj2 b0', proj2 b1'} : Set (Euc 2)) := by
          rwa [convexHull_pair]
        refine hpt 2 _ (hown (by simpa using ha1))
          (subB 2 (by decide) (by decide) (convexHull_mono ?_ h1))
        rintro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact ⟨b0', Finset.mem_coe.mpr (Finset.mem_union_left _ hb0), rfl⟩
        · exact ⟨b1', Finset.mem_coe.mpr (Finset.mem_union_right _ hb1), rfl⟩
  -- Kirchberger reduction to subsets of size ≤ 3 + 2
  obtain ⟨A', B', hA', hB', hcard, hAB⟩ := kirchberger ⟨q, hqA, hqB⟩
  obtain ⟨q', hq'A, hq'B⟩ := hAB
  have projqA : proj2 q' ∈ convexHull ℝ
      (proj2 '' ((X1 ∪ X3 : Finset (Euc 3)) : Set (Euc 3))) :=
    hullmem hq'A hA'
  have projqB : proj2 q' ∈ convexHull ℝ
      (proj2 '' ((X2 ∪ X4 : Finset (Euc 3)) : Set (Euc 3))) :=
    hullmem hq'B hB'
  have hAne : A'.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.coe_empty, convexHull_empty] at hq'A
    simp at hq'A
  have hBne : B'.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.coe_empty, convexHull_empty] at hq'B
    simp at hq'B
  have hApos : 1 ≤ A'.card := Finset.card_pos.mpr hAne
  have hBpos : 1 ≤ B'.card := Finset.card_pos.mpr hBne
  have selA : ∀ a ∈ A', a ∈ X1 ∪ X3 := fun a ha ↦
    Finset.mem_coe.mp (hA' (Finset.mem_coe.mpr ha))
  have selB : ∀ b ∈ B', b ∈ X2 ∪ X4 := fun b hb ↦
    Finset.mem_coe.mp (hB' (Finset.mem_coe.mpr hb))
  by_cases hA1 : A'.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA1
    rw [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff]
      at hq'A
    rw [hq'A] at projqB
    rcases Finset.mem_union.mp (selA a (Finset.mem_singleton_self a))
        with ha | ha
    · exact hpt 0 _ (hown (by simpa using ha))
        (subB 0 (by decide) (by decide) projqB)
    · exact hpt 2 _ (hown (by simpa using ha))
        (subB 2 (by decide) (by decide) projqB)
  by_cases hB1 : B'.card = 1
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hB1
    rw [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff]
      at hq'B
    rw [hq'B] at projqA
    rcases Finset.mem_union.mp (selB b (Finset.mem_singleton_self b))
        with hb | hb
    · exact hpt 1 _ (hown (by simpa using hb))
        (subA 1 (by decide) (by decide) projqA)
    · exact hpt 3 _ (hown (by simpa using hb))
        (subA 3 (by decide) (by decide) projqA)
  have hA2 : 2 ≤ A'.card := by omega
  have hB2 : 2 ≤ B'.card := by omega
  have hA3 : A'.card ≤ 3 := by omega
  have hB3 : B'.card ≤ 3 := by omega
  interval_cases hAc : A'.card
  · -- `#A' = 2`: `q'` lies on a `13`-segment
    obtain ⟨a0, a1, ha01, rfl⟩ := Finset.card_eq_two.mp hAc
    have ha0m := selA a0 (Finset.mem_insert_self _ _)
    have ha1m := selA a1
      (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
    interval_cases hBc : B'.card
    · -- `#B' = 2`: two segments meet
      obtain ⟨b0, b1, hb01, rfl⟩ := Finset.card_eq_two.mp hBc
      rw [Finset.coe_pair, convexHull_pair] at hq'A hq'B
      have hb0m := selB b0 (Finset.mem_insert_self _ _)
      have hb1m := selB b1
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
      rcases Finset.mem_union.mp ha0m with ha0X1 | ha0X3
      · rcases Finset.mem_union.mp ha1m with ha1X1 | ha1X3
        · exact hpt 0 _
            (segown 0 (by simpa using ha0X1) (by simpa using ha1X1)
              (proj2_mem_segment hq'A))
            (subB 0 (by decide) (by decide) projqB)
        · rcases Finset.mem_union.mp hb0m with hb0X2 | hb0X4
          · rcases Finset.mem_union.mp hb1m with hb1X2 | hb1X4
            · exact hpt 1 _
                (segown 1 (by simpa using hb0X2) (by simpa using hb1X2)
                  (proj2_mem_segment hq'B))
                (subA 1 (by decide) (by decide) projqA)
            · exact segseg (le_refl 0) ha0X1 ha1X3 hb0X2 hb1X4
                (by simpa using hq'A) (by simpa using hq'B)
          · rcases Finset.mem_union.mp hb1m with hb1X2 | hb1X4
            · exact segseg (le_refl 0) ha0X1 ha1X3 hb1X2 hb0X4
                (by simpa using hq'A)
                (by rw [segment_symm]; simpa using hq'B)
            · exact hpt 3 _
                (segown 3 (by simpa using hb0X4) (by simpa using hb1X4)
                  (proj2_mem_segment hq'B))
                (subA 3 (by decide) (by decide) projqA)
      · rcases Finset.mem_union.mp ha1m with ha1X1 | ha1X3
        · rcases Finset.mem_union.mp hb0m with hb0X2 | hb0X4
          · rcases Finset.mem_union.mp hb1m with hb1X2 | hb1X4
            · exact hpt 1 _
                (segown 1 (by simpa using hb0X2) (by simpa using hb1X2)
                  (proj2_mem_segment hq'B))
                (subA 1 (by decide) (by decide) projqA)
            · exact segseg (le_refl 0) ha1X1 ha0X3 hb0X2 hb1X4
                (by rw [segment_symm]; simpa using hq'A)
                (by simpa using hq'B)
          · rcases Finset.mem_union.mp hb1m with hb1X2 | hb1X4
            · exact segseg (le_refl 0) ha1X1 ha0X3 hb1X2 hb0X4
                (by rw [segment_symm]; simpa using hq'A)
                (by rw [segment_symm]; simpa using hq'B)
            · exact hpt 3 _
                (segown 3 (by simpa using hb0X4) (by simpa using hb1X4)
                  (proj2_mem_segment hq'B))
                (subA 3 (by decide) (by decide) projqA)
        · exact hpt 2 _
            (segown 2 (by simpa using ha0X3) (by simpa using ha1X3)
              (proj2_mem_segment hq'A))
            (subB 2 (by decide) (by decide) projqB)
    · -- `#B' = 3`: slide the triangle down to first contact
      obtain ⟨b0, b1, b2, hb01, hb02, hb12, rfl⟩ := Finset.card_eq_three.mp hBc
      rw [Finset.coe_pair, convexHull_pair] at hq'A
      have hb0m := selB b0 (Finset.mem_insert_self _ _)
      have hb1m := selB b1 (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert_self _ _)))
      have hb2m := selB b2 (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))))
      -- the sliding argument, for a genuine `X₁X₃` segment
      have slide23 : ∀ {a a' : Euc 3}, a ∈ X1 → a' ∈ X3 →
          q' ∈ segment ℝ a a' → False := by
        intro a a' haa haa' hqseg
        set M := max 0 (max (b0 2) (max (b1 2) (b2 2)) - min (a 2) (a' 2) + 1)
          with hMdef
        have hM0 : 0 ≤ M := le_max_left _ _
        have hMbig : max (b0 2) (max (b1 2) (b2 2)) - M < min (a 2) (a' 2) := by
          have h := le_max_right (0 : ℝ)
            (max (b0 2) (max (b1 2) (b2 2)) - min (a 2) (a' 2) + 1)
          rw [← hMdef] at h; linarith
        -- at `t = 1` the lowered triangle misses the segment entirely
        have hdisj : Disjoint (segment ℝ a a')
            (convexHull ℝ ({b0 - M • z3, b1 - M • z3, b2 - M • z3} :
              Set (Euc 3))) := by
          refine Set.disjoint_left.mpr fun v hv1 hv2 ↦ ?_
          have hlo : min (a 2) (a' 2) ≤ v 2 := by
            rw [segment_eq_image] at hv1
            obtain ⟨θ, hθ, rfl⟩ := hv1
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
            rcases le_total (a 2) (a' 2) with h | h
            · rw [min_eq_left h]
              have h1 : 0 ≤ θ * a' 2 - θ * a 2 := by
                rw [← mul_sub]; exact mul_nonneg hθ.1 (sub_nonneg.mpr h)
              linarith
            · rw [min_eq_right h]
              have h1 : 0 ≤ (1 - θ) * a 2 - (1 - θ) * a' 2 := by
                rw [← mul_sub]; exact mul_nonneg (sub_nonneg.mpr hθ.2)
                  (sub_nonneg.mpr h)
              linarith
          have hup : v 2 ≤ max (b0 2) (max (b1 2) (b2 2)) - M := by
            have hsub : ({b0 - M • z3, b1 - M • z3, b2 - M • z3} :
                Set (Euc 3)) ⊆ {x : Euc 3 | EuclideanSpace.projₗ (2 : Fin 3) x ≤
                  max (b0 2) (max (b1 2) (b2 2)) - M} := by
              intro x hx
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
              rcases hx with rfl | rfl | rfl
              · rw [Set.mem_ofPred_eq, PiLp.projₗ_apply, sub_z3_two]
                exact sub_le_sub_right (le_max_left _ _) _
              · rw [Set.mem_ofPred_eq, PiLp.projₗ_apply, sub_z3_two]
                exact sub_le_sub_right
                  ((le_max_left _ _).trans (le_max_right _ _)) _
              · rw [Set.mem_ofPred_eq, PiLp.projₗ_apply, sub_z3_two]
                exact sub_le_sub_right
                  ((le_max_right _ _).trans (le_max_right _ _)) _
            have hmem := convexHull_min hsub
              (convex_halfSpace_le
                (EuclideanSpace.projₗ (2 : Fin 3)).isLinear _) hv2
            simpa only [Set.mem_ofPred_eq, PiLp.projₗ_apply] using hmem
          linarith
        obtain ⟨t, htI, u, huseg, hflag⟩ := slide_triangle_boundary
          (y := ![a, a', b0, b1, b2])
          (z := ![a, a', b0 - M • z3, b1 - M • z3, b2 - M • z3])
          ⟨q', by simpa using hqseg, by simpa using hq'B⟩
          (by simpa using hdisj)
        -- compute the slid points
        have hw0 : slidePt ![a, a', b0, b1, b2]
            ![a, a', b0 - M • z3, b1 - M • z3, b2 - M • z3] (0 : Fin 5) t = a := by
          show (1 - t) • a + t • a = a; module
        have hw1 : slidePt ![a, a', b0, b1, b2]
            ![a, a', b0 - M • z3, b1 - M • z3, b2 - M • z3] (1 : Fin 5) t = a' := by
          show (1 - t) • a' + t • a' = a'; module
        have hw2 : slidePt ![a, a', b0, b1, b2]
            ![a, a', b0 - M • z3, b1 - M • z3, b2 - M • z3] (2 : Fin 5) t =
            b0 - (t * M) • z3 := by
          show (1 - t) • b0 + t • (b0 - M • z3) = b0 - (t * M) • z3; module
        have hw3 : slidePt ![a, a', b0, b1, b2]
            ![a, a', b0 - M • z3, b1 - M • z3, b2 - M • z3] (3 : Fin 5) t =
            b1 - (t * M) • z3 := by
          show (1 - t) • b1 + t • (b1 - M • z3) = b1 - (t * M) • z3; module
        have hw4 : slidePt ![a, a', b0, b1, b2]
            ![a, a', b0 - M • z3, b1 - M • z3, b2 - M • z3] (4 : Fin 5) t =
            b2 - (t * M) • z3 := by
          show (1 - t) • b2 + t • (b2 - M • z3) = b2 - (t * M) • z3; module
        have huseg' : u ∈ segment ℝ a a' := by
          simpa only [hw0, hw1] using huseg
        have huA13 : proj2 u ∈ convexHull ℝ
            (proj2 '' ((X1 ∪ X3 : Finset (Euc 3)) : Set (Euc 3))) :=
          hull13 huseg' (Finset.mem_union_left _ haa)
            (Finset.mem_union_right _ haa')
        have hσb : -(t * M) ≤ 0 := neg_nonpos.mpr (mul_nonneg htI.1 hM0)
        -- dispatch an edge contact `{x - tM·e₃, y - tM·e₃}` (in `B'`)
        have edge23 : ∀ {x y : Euc 3}, x ∈ X2 ∪ X4 → y ∈ X2 ∪ X4 →
            u ∈ segment ℝ (x - (t * M) • z3) (y - (t * M) • z3) → False := by
          intro x y hxm hym hedge
          have hpj : proj2 u ∈ segment ℝ (proj2 x) (proj2 y) := by
            have h := proj2_mem_segment hedge
            rwa [proj2_sub_z3, proj2_sub_z3] at h
          rcases Finset.mem_union.mp hxm with hx2 | hx4 <;>
            rcases Finset.mem_union.mp hym with hy2 | hy4
          · exact hpt 1 _ (segown 1 (by simpa using hx2) (by simpa using hy2) hpj)
              (subA 1 (by decide) (by decide) huA13)
          · exact segseg hσb haa haa' hx2 hy4 (by simpa using huseg')
              (by simpa only [sub_eq_add_neg, ← neg_smul] using hedge)
          · exact segseg hσb haa haa' hy2 hx4 (by simpa using huseg')
              (by rw [segment_symm]
                  simpa only [sub_eq_add_neg, ← neg_smul] using hedge)
          · exact hpt 3 _ (segown 3 (by simpa using hx4) (by simpa using hy4) hpj)
              (subA 3 (by decide) (by decide) huA13)
        rcases hflag with hed23 | hed34 | hed42 | hend
        · exact edge23 hb0m hb1m (by simpa only [hw2, hw3] using hed23)
        · exact edge23 hb1m hb2m (by simpa only [hw3, hw4] using hed34)
        · exact edge23 hb2m hb0m (by simpa only [hw4, hw2] using hed42)
        · -- a segment endpoint lies in the lowered triangle
          obtain rfl | rfl := hend.1
          · have hmem : a ∈ convexHull ℝ ({b0 - (t * M) • z3, b1 - (t * M) • z3,
                b2 - (t * M) • z3} : Set (Euc 3)) := by
              simpa only [hw0, hw2, hw3, hw4] using hend.2
            have h2 : proj2 a ∈ convexHull ℝ
                ({proj2 b0, proj2 b1, proj2 b2} : Set (Euc 2)) := by
              have h := proj2_mem_convexHull hmem
              rwa [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
                proj2_sub_z3, proj2_sub_z3, proj2_sub_z3] at h
            refine hpt 0 _ (hown (by simpa using haa))
              (subB 0 (by decide) (by decide) (convexHull_mono ?_ h2))
            rintro w hw
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
            rcases hw with rfl | rfl | rfl
            · exact ⟨b0, Finset.mem_coe.mpr hb0m, rfl⟩
            · exact ⟨b1, Finset.mem_coe.mpr hb1m, rfl⟩
            · exact ⟨b2, Finset.mem_coe.mpr hb2m, rfl⟩
          · have hmem : a' ∈ convexHull ℝ ({b0 - (t * M) • z3, b1 - (t * M) • z3,
                b2 - (t * M) • z3} : Set (Euc 3)) := by
              simpa only [hw1, hw2, hw3, hw4] using hend.2
            have h2 : proj2 a' ∈ convexHull ℝ
                ({proj2 b0, proj2 b1, proj2 b2} : Set (Euc 2)) := by
              have h := proj2_mem_convexHull hmem
              rwa [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
                proj2_sub_z3, proj2_sub_z3, proj2_sub_z3] at h
            refine hpt 2 _ (hown (by simpa using haa'))
              (subB 2 (by decide) (by decide) (convexHull_mono ?_ h2))
            rintro w hw
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
            rcases hw with rfl | rfl | rfl
            · exact ⟨b0, Finset.mem_coe.mpr hb0m, rfl⟩
            · exact ⟨b1, Finset.mem_coe.mpr hb1m, rfl⟩
            · exact ⟨b2, Finset.mem_coe.mpr hb2m, rfl⟩
      rcases Finset.mem_union.mp ha0m with ha0X1 | ha0X3
      · rcases Finset.mem_union.mp ha1m with ha1X1 | ha1X3
        · exact hpt 0 _
            (segown 0 (by simpa using ha0X1) (by simpa using ha1X1)
              (proj2_mem_segment hq'A))
            (subB 0 (by decide) (by decide) projqB)
        · exact slide23 ha0X1 ha1X3 hq'A
      · rcases Finset.mem_union.mp ha1m with ha1X1 | ha1X3
        · exact slide23 ha1X1 ha0X3 (by rwa [segment_symm])
        · exact hpt 2 _
            (segown 2 (by simpa using ha0X3) (by simpa using ha1X3)
              (proj2_mem_segment hq'A))
            (subB 2 (by decide) (by decide) projqB)
  · -- `#A' = 3`: symmetric sliding (the `13`-triangle moves up)
    obtain ⟨a0, a1, a2, ha01, ha02, ha12, rfl⟩ := Finset.card_eq_three.mp hAc
    have ha0m := selA a0 (Finset.mem_insert_self _ _)
    have ha1m := selA a1 (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert_self _ _)))
    have ha2m := selA a2 (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))))
    interval_cases hBc : B'.card
    · -- `#B' = 2`
      obtain ⟨b0, b1, hb01, rfl⟩ := Finset.card_eq_two.mp hBc
      rw [Finset.coe_pair, convexHull_pair] at hq'B
      have hb0m := selB b0 (Finset.mem_insert_self _ _)
      have hb1m := selB b1
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
      -- the sliding argument, for a genuine `X₂X₄` segment
      have slide32 : ∀ {b b' : Euc 3}, b ∈ X2 → b' ∈ X4 →
          q' ∈ segment ℝ b b' → False := by
        intro b b' hbb hbb' hqseg
        set M := max 0 (max (b 2) (b' 2) - min (a0 2) (min (a1 2) (a2 2)) + 1)
          with hMdef
        have hM0 : 0 ≤ M := le_max_left _ _
        have hMbig : max (b 2) (b' 2) <
            min (a0 2) (min (a1 2) (a2 2)) + M := by
          have h := le_max_right (0 : ℝ)
            (max (b 2) (b' 2) - min (a0 2) (min (a1 2) (a2 2)) + 1)
          rw [← hMdef] at h; linarith
        -- at `t = 1` the raised triangle misses the segment entirely
        have hdisj : Disjoint (segment ℝ b b')
            (convexHull ℝ ({a0 + M • z3, a1 + M • z3, a2 + M • z3} :
              Set (Euc 3))) := by
          refine Set.disjoint_left.mpr fun v hv1 hv2 ↦ ?_
          have hup : v 2 ≤ max (b 2) (b' 2) := by
            rw [segment_eq_image] at hv1
            obtain ⟨θ, hθ, rfl⟩ := hv1
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
            rcases le_total (b 2) (b' 2) with h | h
            · rw [max_eq_right h]
              have h1 : 0 ≤ (1 - θ) * b' 2 - (1 - θ) * b 2 := by
                rw [← mul_sub]
                exact mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr h)
              linarith
            · rw [max_eq_left h]
              have h1 : 0 ≤ θ * b 2 - θ * b' 2 := by
                rw [← mul_sub]; exact mul_nonneg hθ.1 (sub_nonneg.mpr h)
              linarith
          have hlo : min (a0 2) (min (a1 2) (a2 2)) + M ≤ v 2 := by
            have hsub : ({a0 + M • z3, a1 + M • z3, a2 + M • z3} :
                Set (Euc 3)) ⊆ {x : Euc 3 |
                  min (a0 2) (min (a1 2) (a2 2)) + M ≤
                    EuclideanSpace.projₗ (2 : Fin 3) x} := by
              intro x hx
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
              rcases hx with rfl | rfl | rfl
              · show min (a0 2) (min (a1 2) (a2 2)) + M ≤
                    EuclideanSpace.projₗ (2 : Fin 3) (a0 + M • z3)
                rw [PiLp.projₗ_apply, add_z3_two]
                linarith [min_le_left (a0 2) (min (a1 2) (a2 2))]
              · show min (a0 2) (min (a1 2) (a2 2)) + M ≤
                    EuclideanSpace.projₗ (2 : Fin 3) (a1 + M • z3)
                rw [PiLp.projₗ_apply, add_z3_two]
                linarith [(min_le_right (a0 2) (min (a1 2) (a2 2))).trans
                  (min_le_left (a1 2) (a2 2))]
              · show min (a0 2) (min (a1 2) (a2 2)) + M ≤
                    EuclideanSpace.projₗ (2 : Fin 3) (a2 + M • z3)
                rw [PiLp.projₗ_apply, add_z3_two]
                linarith [(min_le_right (a0 2) (min (a1 2) (a2 2))).trans
                  (min_le_right (a1 2) (a2 2))]
            have hmem := convexHull_min hsub
              (convex_halfSpace_ge
                (EuclideanSpace.projₗ (2 : Fin 3)).isLinear _) hv2
            simpa only [Set.mem_ofPred_eq, PiLp.projₗ_apply] using hmem
          linarith
        obtain ⟨t, htI, u, huseg, hflag⟩ := slide_triangle_boundary
          (y := ![b, b', a0, a1, a2])
          (z := ![b, b', a0 + M • z3, a1 + M • z3, a2 + M • z3])
          ⟨q', by simpa using hqseg, by simpa using hq'A⟩
          (by simpa using hdisj)
        -- compute the slid points
        have hw0 : slidePt ![b, b', a0, a1, a2]
            ![b, b', a0 + M • z3, a1 + M • z3, a2 + M • z3] (0 : Fin 5) t = b := by
          show (1 - t) • b + t • b = b; module
        have hw1 : slidePt ![b, b', a0, a1, a2]
            ![b, b', a0 + M • z3, a1 + M • z3, a2 + M • z3] (1 : Fin 5) t = b' := by
          show (1 - t) • b' + t • b' = b'; module
        have hw2 : slidePt ![b, b', a0, a1, a2]
            ![b, b', a0 + M • z3, a1 + M • z3, a2 + M • z3] (2 : Fin 5) t =
            a0 + (t * M) • z3 := by
          show (1 - t) • a0 + t • (a0 + M • z3) = a0 + (t * M) • z3; module
        have hw3 : slidePt ![b, b', a0, a1, a2]
            ![b, b', a0 + M • z3, a1 + M • z3, a2 + M • z3] (3 : Fin 5) t =
            a1 + (t * M) • z3 := by
          show (1 - t) • a1 + t • (a1 + M • z3) = a1 + (t * M) • z3; module
        have hw4 : slidePt ![b, b', a0, a1, a2]
            ![b, b', a0 + M • z3, a1 + M • z3, a2 + M • z3] (4 : Fin 5) t =
            a2 + (t * M) • z3 := by
          show (1 - t) • a2 + t • (a2 + M • z3) = a2 + (t * M) • z3; module
        have huseg' : u ∈ segment ℝ b b' := by
          simpa only [hw0, hw1] using huseg
        have huB24 : proj2 u ∈ convexHull ℝ
            (proj2 '' ((X2 ∪ X4 : Finset (Euc 3)) : Set (Euc 3))) :=
          hull24 huseg' (Finset.mem_union_left _ hbb)
            (Finset.mem_union_right _ hbb')
        have hσa : 0 ≤ t * M := mul_nonneg htI.1 hM0
        -- dispatch an edge contact `{x + tM·e₃, y + tM·e₃}` (in `A'`)
        have edge13 : ∀ {x y : Euc 3}, x ∈ X1 ∪ X3 → y ∈ X1 ∪ X3 →
            u ∈ segment ℝ (x + (t * M) • z3) (y + (t * M) • z3) → False := by
          intro x y hxm hym hedge
          have hpj : proj2 u ∈ segment ℝ (proj2 x) (proj2 y) := by
            have h := proj2_mem_segment hedge
            rwa [proj2_add_z3, proj2_add_z3] at h
          rcases Finset.mem_union.mp hxm with hx1 | hx3 <;>
            rcases Finset.mem_union.mp hym with hy1 | hy3
          · exact hpt 0 _ (segown 0 (by simpa using hx1) (by simpa using hy1) hpj)
              (subB 0 (by decide) (by decide) huB24)
          · exact segseg hσa hx1 hy3 hbb hbb' (by simpa using hedge)
              (by simpa using huseg')
          · exact segseg hσa hy1 hx3 hbb hbb'
              (by rw [segment_symm]; simpa using hedge)
              (by simpa using huseg')
          · exact hpt 2 _ (segown 2 (by simpa using hx3) (by simpa using hy3) hpj)
              (subB 2 (by decide) (by decide) huB24)
        rcases hflag with hed01 | hed12 | hed20 | hend
        · exact edge13 ha0m ha1m (by simpa only [hw2, hw3] using hed01)
        · exact edge13 ha1m ha2m (by simpa only [hw3, hw4] using hed12)
        · exact edge13 ha2m ha0m (by simpa only [hw4, hw2] using hed20)
        · -- a `B'`-segment endpoint lies in the raised triangle
          obtain rfl | rfl := hend.1
          · have hmem : b ∈ convexHull ℝ ({a0 + (t * M) • z3, a1 + (t * M) • z3,
                a2 + (t * M) • z3} : Set (Euc 3)) := by
              simpa only [hw0, hw2, hw3, hw4] using hend.2
            have h2 : proj2 b ∈ convexHull ℝ
                ({proj2 a0, proj2 a1, proj2 a2} : Set (Euc 2)) := by
              have h := proj2_mem_convexHull hmem
              rwa [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
                proj2_add_z3, proj2_add_z3, proj2_add_z3] at h
            refine hpt 1 _ (hown (by simpa using hbb))
              (subA 1 (by decide) (by decide) (convexHull_mono ?_ h2))
            rintro w hw
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
            rcases hw with rfl | rfl | rfl
            · exact ⟨a0, Finset.mem_coe.mpr ha0m, rfl⟩
            · exact ⟨a1, Finset.mem_coe.mpr ha1m, rfl⟩
            · exact ⟨a2, Finset.mem_coe.mpr ha2m, rfl⟩
          · have hmem : b' ∈ convexHull ℝ ({a0 + (t * M) • z3, a1 + (t * M) • z3,
                a2 + (t * M) • z3} : Set (Euc 3)) := by
              simpa only [hw1, hw2, hw3, hw4] using hend.2
            have h2 : proj2 b' ∈ convexHull ℝ
                ({proj2 a0, proj2 a1, proj2 a2} : Set (Euc 2)) := by
              have h := proj2_mem_convexHull hmem
              rwa [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
                proj2_add_z3, proj2_add_z3, proj2_add_z3] at h
            refine hpt 3 _ (hown (by simpa using hbb'))
              (subA 3 (by decide) (by decide) (convexHull_mono ?_ h2))
            rintro w hw
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
            rcases hw with rfl | rfl | rfl
            · exact ⟨a0, Finset.mem_coe.mpr ha0m, rfl⟩
            · exact ⟨a1, Finset.mem_coe.mpr ha1m, rfl⟩
            · exact ⟨a2, Finset.mem_coe.mpr ha2m, rfl⟩
      rcases Finset.mem_union.mp hb0m with hb0X2 | hb0X4
      · rcases Finset.mem_union.mp hb1m with hb1X2 | hb1X4
        · exact hpt 1 _
            (segown 1 (by simpa using hb0X2) (by simpa using hb1X2)
              (proj2_mem_segment hq'B))
            (subA 1 (by decide) (by decide) projqA)
        · exact slide32 hb0X2 hb1X4 hq'B
      · rcases Finset.mem_union.mp hb1m with hb1X2 | hb1X4
        · exact slide32 hb1X2 hb0X4 (by rwa [segment_symm])
        · exact hpt 3 _
            (segown 3 (by simpa using hb0X4) (by simpa using hb1X4)
              (proj2_mem_segment hq'B))
            (subA 3 (by decide) (by decide) projqA)
    · -- `#B' = 3`: `3 + 3 > 5`, impossible
      omega

/-- **Proposition 2.3.**  If every segment `x₁x₃` (`x₁ ∈ X₁, x₃ ∈ X₃`) lies
strictly above every segment `x₂x₄` (`x₂ ∈ X₂, x₄ ∈ X₄`) — in particular their
projections meet at interior points of both — then
`conv(X₁∪X₃) ∩ conv(X₂∪X₄) = ∅`.

The `Nonempty` hypotheses are necessary: with `X₃ = ∅` the `habove` hypothesis
is vacuous and the conclusion fails (e.g. `X₁ = {midpoint of bc}`,
`X₂ = {b}`, `X₄ = {c}`).  The strictness of the crossings in `AboveSeg`
(`0 < s, t < 1`) is likewise essential — it is what the paper's "the
collection `Y₁,…,Y₄` is in convex position" step uses.  That step is
factored out as the hypothesis `hconv` (collection of projected sets in
convex position), which is what the application in `cor_2_4` supplies. -/
theorem prop_2_3 {X1 X2 X3 X4 : Finset (Euc 3)}
    (hX1 : X1.Nonempty) (hX2 : X2.Nonempty) (hX3 : X3.Nonempty)
    (hX4 : X4.Nonempty)
    (hd : Disjoint X1 X2) (hd' : Disjoint X1 X3) (hd'' : Disjoint X1 X4)
    (hd''' : Disjoint X2 X3) (hd'''' : Disjoint X2 X4) (hd''''' : Disjoint X3 X4)
    (hgp : InGeneralPosition ((X1 ∪ X2 ∪ X3 ∪ X4 : Finset (Euc 3)) : Set (Euc 3)))
    (hconv : ∀ i : Fin 4, Disjoint
      (convexHull ℝ (proj2 ''
        ((![X1, X2, X3, X4] i : Finset (Euc 3)) : Set (Euc 3))))
      (convexHull ℝ (⋃ j : Fin 4, ⋃ _ : j ≠ i,
        proj2 '' ((![X1, X2, X3, X4] j : Finset (Euc 3)) : Set (Euc 3)))))
    (habove : ∀ x1 ∈ X1, ∀ x2 ∈ X2, ∀ x3 ∈ X3, ∀ x4 ∈ X4,
      AboveSeg x1 x3 x2 x4) :
    Disjoint (convexHull ℝ ((X1 ∪ X3 : Finset (Euc 3)) : Set (Euc 3)))
             (convexHull ℝ ((X2 ∪ X4 : Finset (Euc 3)) : Set (Euc 3))) := by
  classical
  -- The nonemptiness, pairwise-disjointness and general-position hypotheses
  -- are what make the statement well-posed (they rule out the vacuous and
  -- degenerate counterexamples); the separation argument itself only needs
  -- the projected convex-position and `AboveSeg` hypotheses.
  have _ : X1.Nonempty ∧ X2.Nonempty ∧ X3.Nonempty ∧ X4.Nonempty ∧
      Disjoint X1 X2 ∧ Disjoint X1 X3 ∧ Disjoint X1 X4 ∧ Disjoint X2 X3 ∧
      Disjoint X2 X4 ∧ Disjoint X3 X4 ∧
      InGeneralPosition ((X1 ∪ X2 ∪ X3 ∪ X4 : Finset (Euc 3)) : Set (Euc 3)) :=
    ⟨hX1, hX2, hX3, hX4, hd, hd', hd'', hd''', hd'''', hd''''', hgp⟩
  /- **Mathematical argument.**  Suppose `q` lies in the intersection.  The
  Kirchberger theorem (`kirchberger`, `d = 3`) yields `A' ⊆ X1∪X3` and
  `B' ⊆ X2∪X4` with `#A' + #B' ≤ 5` and `q ∈ conv A' ∩ conv B'`.  Split on
  the ordered pair `(#A', #B')` (the two `1+?` cases are symmetric):

  * `#A' = 1`, `#B' ≤ 4`: `q` is a point of `X1∪X3` lying in `conv(B')`.  From
    `AboveSeg` one can show `q ∉ conv(X2∪X4)` (each triangle of a convex
    position subset of `X2∪X4` is pierced from above by the `X1`/`X3`
    segments), a contradiction.
  * `#A' = 2`, `#B' = 3`: write `A' = {a13, a13'}` — or `{a1, a3}` split
    across the two groups — and `B' = {b2, b4, b24}`.  `conv A'` is a segment
    and `conv B'` a triangle whose edges all lie in `conv(X2∪X4)`.  By the
    sliding/continuity argument there is a first contact parameter at which
    the `X1X3`-segment meets the `X2X4`-hull *on a boundary edge*; that edge
    is a genuine `x₂x₄` or `x₁x₃` segment, and the crossing contradicts
    `AboveSeg` (a segment of the lower class cannot meet a segment of the
    upper class: projecting to `ℝ²` the `AboveSeg` hypothesis makes the
    projections disjoint — for `x₁x₃ ∩ x₂x₄` an `AboveSeg` with `≥`-height
    collision is impossible since the intersection point would satisfy both
    `z_up > z_low` and equality).
  * `#A' = 3`, `#B' = 2`: symmetric.
  * `#A' = 2`, `#B' = 2`: `q` lies on an `x₁x₃`-type segment and on an
    `x₂x₄`-type segment; either the segments share an endpoint (impossible:
    the four sets are pairwise disjoint) or they are skew/transversal, and
    `AboveSeg` — which gives a *strict* height comparison at every common
    `ℝ²`-projection — rules out any meeting point.
  * `#A' = 1`, `#B' = 1` and the `≥4` splittings are excluded by general
    position (`InGeneralPosition` forbids the needed degeneracies).

  The strictness of `AboveSeg` (interior crossings) plus the four `Nonempty`
  hypotheses make this the paper's Prop. 2.3: the earlier formulation without
  them was genuinely false (empty `X₃` makes `habove` vacuous, and endpoint
  crossings let an upper segment pierce the lower hull at a projected
  vertex). -/
  exact conv13_conv24_disjoint hconv habove

/-- **Proposition 2.7.**  For a 2-separated collection `X₁,…,X_k` in convex
position and representatives `xᵢ ∈ Xᵢ`, any plane `H = {f = c}` avoiding all
`xᵢ` can be replaced by a plane `H̃ = {g = c'}` placing each whole `Xᵢ` on the
side dictated by `xᵢ`'s side of `H`. -/
theorem prop_2_7 (X : Fin k → Finset (Euc 3))
    (hsep : TwoSeparated X) (hconv : CollectionConvex X)
    (x : Fin k → Euc 3) (hx : ∀ i, x i ∈ X i)
    (f : Euc 3 →ₗ[ℝ] ℝ) (c : ℝ) (_hf : ∀ i, f (x i) ≠ c) :
    ∃ g : Euc 3 →ₗ[ℝ] ℝ, ∃ c' : ℝ,
      ∀ i : Fin k,
        (c < f (x i) → ∀ y ∈ X i, c' < g y) ∧
        (f (x i) < c → ∀ y ∈ X i, g y < c') := by
  classical
  set S : Finset (Fin k) := Finset.univ.filter fun i ↦ c < f (x i) with hSdef
  set T : Finset (Fin k) := Finset.univ.filter fun i ↦ f (x i) < c with hTdef
  set A : Finset (Euc 3) := S.biUnion X with hAdef
  set B : Finset (Euc 3) := T.biUnion X with hBdef
  have hdisj := disjoint_hull_union X x hx hconv hsep f c S T
    (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    (fun i hi ↦ (Finset.mem_filter.mp hi).2)
  -- Separate `conv B` (compact) from `conv A` (closed): `g'` takes values `< u'`
  -- on the `T`-side and `> v'` on the `S`-side, so `c' := v'` works for both.
  obtain ⟨g', u', v', hB', huv', hA'⟩ := geometric_hahn_banach_compact_closed
    (s := convexHull ℝ (B : Set (Euc 3))) (t := convexHull ℝ (A : Set (Euc 3)))
    (convex_convexHull ℝ _) (B.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ _) (A.finite_toSet.isClosed_convexHull ℝ) hdisj.symm
  refine ⟨g'.toLinearMap, v', fun i ↦
    ⟨fun hi v hv ↦ hA' v (subset_convexHull ℝ _ (Finset.mem_coe.mpr
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, hi⟩, hv⟩))),
     fun hi v hv ↦ lt_trans (hB' v (subset_convexHull ℝ _ (Finset.mem_coe.mpr
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, hi⟩, hv⟩)))) huv'⟩⟩

end
