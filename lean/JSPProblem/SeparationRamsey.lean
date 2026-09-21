import JSPProblem.Separation
import JSPProblem.Ramsey

/-!
# JSP-000527 — Above/below Ramsey (Proposition 2.2 and Corollary 2.4)

Paper items:

* **Prop 2.2** (`aboveBelow_ramsey`): points of `X ⊂ ℝ³` in general position
  whose projections are consecutive vertices of a convex polygon contain a
  `k`-subset on which all crossing pairs `i<i'<j<j'` have `xᵢxⱼ` uniformly
  above (or uniformly below) `xᵢ'xⱼ'`.  Via Ramsey `R₄(k,k)`.
* **Corollary 2.4** (`cor_2_4`): the interval-split disjointness conclusion,
  combining `aboveBelow_ramsey` with `prop_2_3`.

## Proof outline for `aboveBelow_ramsey`

The projected points `proj2 (x i)` form the vertex set `V` of a convex polygon.
Fix a vertex `o`.  A separating line through `o` gives a linear functional `f`
with `f (v − o) > 0` for all other vertices; writing `g := cr2 (e − o) ·` for a
second fixed vertex `e`, the slope-like quantity `σ v := g (v − o) / f (v − o)`
orders `V ∖ {o}` exactly as the boundary order of the polygon (the two
containment criteria `mem_of_C_nonneg` / `C_pos_of_notMem` below encode the
convexity).  A 2-colouring of pairs by `σ`-comparison followed by a 4-colouring
by above/below (two applications of the finite Ramsey theorem of
`Ramsey.lean`) produces the required monochromatic set.
-/

noncomputable section

open Finset

/-! ### Planar algebra: the signed area `cr2` -/

/-- Signed area of the parallelogram spanned by two planar vectors. -/
private def cr2 (u v : Euc 2) : ℝ := u 0 * v 1 - u 1 * v 0

private lemma cr2_self (u : Euc 2) : cr2 u u = 0 := by
  simp [cr2]; ring

private lemma cr2_anticomm (u v : Euc 2) : cr2 u v = -cr2 v u := by
  simp [cr2]; ring

private lemma cr2_add_right (u v w : Euc 2) : cr2 u (v + w) = cr2 u v + cr2 u w := by
  simp [cr2, PiLp.add_apply]; ring

private lemma cr2_add_left (u v w : Euc 2) : cr2 (u + v) w = cr2 u w + cr2 v w := by
  simp [cr2, PiLp.add_apply]; ring

private lemma cr2_smul_right (c : ℝ) (u v : Euc 2) : cr2 u (c • v) = c * cr2 u v := by
  simp [cr2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma cr2_smul_left (c : ℝ) (u v : Euc 2) : cr2 (c • u) v = c * cr2 u v := by
  simp [cr2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma cr2_sub_right (u v w : Euc 2) : cr2 u (v - w) = cr2 u v - cr2 u w := by
  simp [cr2, PiLp.sub_apply]; ring

private lemma cr2_sub_left (u v w : Euc 2) : cr2 (u - v) w = cr2 u w - cr2 v w := by
  simp [cr2, PiLp.sub_apply]; ring

private lemma cr2_zero_left (v : Euc 2) : cr2 0 v = 0 := by
  simp [cr2, PiLp.zero_apply]

private lemma cr2_zero_right (u : Euc 2) : cr2 u 0 = 0 := by
  simp [cr2, PiLp.zero_apply]

/-- Twice the signed area of the triangle `u v w`. -/
private def crs (u v w : Euc 2) : ℝ := cr2 (v - u) (w - u)

private lemma crs_eq_cycle (u v w : Euc 2) :
    crs u v w = cr2 u v + cr2 v w + cr2 w u := by
  simp [crs, cr2, PiLp.sub_apply]; ring

private lemma crs_self_left (v w : Euc 2) : crs v v w = 0 := by
  simp [crs, cr2, PiLp.sub_apply]

private lemma crs_anticomm_mid (u v w : Euc 2) : crs u v w = -crs u w v := by
  simp [crs, cr2, PiLp.sub_apply]; ring

/-- A linear functional on `Euc 2` evaluated coordinatewise. -/
private lemma lm_apply (f : Euc 2 →ₗ[ℝ] ℝ) (v : Euc 2) :
    f v = f (EuclideanSpace.single 0 1) * v 0 +
      f (EuclideanSpace.single 1 1) * v 1 := by
  have hv : v = v 0 • EuclideanSpace.single 0 (1 : ℝ) +
      v 1 • EuclideanSpace.single 1 (1 : ℝ) := by
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [EuclideanSpace.single_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul]
  conv_lhs => rw [hv]
  simp [map_add, map_smul, smul_eq_mul]
  ring

/-- The determinant identity relating `cr2` and the `(f, g)`-coordinates where
`g = cr2 e ·`. -/
private lemma cr2_mul_fe (f : Euc 2 →ₗ[ℝ] ℝ) (e u v : Euc 2) :
    cr2 u v * f e = f u * cr2 e v - f v * cr2 e u := by
  rw [lm_apply f u, lm_apply f v, lm_apply f e]
  simp [cr2]
  ring

/-- If `cr2 p q = 0` and `p ≠ 0`, then `q` is a scalar multiple of `p`. -/
private lemma exists_smul_of_cr2_eq_zero {p q : Euc 2} (hp : p ≠ 0)
    (h : cr2 p q = 0) : ∃ c : ℝ, q = c • p := by
  have hq : p 0 * q 1 = p 1 * q 0 := by
    simp only [cr2, sub_eq_zero] at h
    linarith [h]
  by_cases hp0 : p 0 = 0
  · have hp1 : p 1 ≠ 0 := by
      intro h1
      apply hp
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [hp0, h1]
    have hq0 : q 0 = 0 := by
      rw [hp0] at hq
      simp at hq
      rcases hq with h | h
      · exact absurd h hp1
      · exact h
    refine ⟨q 1 / p 1, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [PiLp.smul_apply, smul_eq_mul, hp0, hq0, div_mul_cancel₀ _ hp1]
  · refine ⟨q 0 / p 0, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [PiLp.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hp0]
    · simp only [PiLp.smul_apply, smul_eq_mul]
      have hq1 : q 1 = q 0 / p 0 * p 1 := by
        field_simp
        linear_combination hq
      exact hq1

/-- A convex combination `(1 - t) • a + t • b` with `t ∈ [0,1]` lies in the
convex hull of any set containing `a, b`. -/
private lemma seg_conv {s : Set (Euc 2)} {a b : Euc 2} (ha : a ∈ s) (hb : b ∈ s)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • a + t • b ∈ convexHull ℝ s := by
  apply segment_subset_convexHull ha hb
  rw [segment_eq_image_lineMap]
  exact ⟨t, ⟨ht0, ht1⟩, AffineMap.lineMap_apply_module a b t⟩

/-- A vertex `p` of a convex-position set is never a convex combination
`(1-t)•a + t•b` of two other vertices with `0 < t < 1`. -/
private lemma not_mem_conv_pair {V : Finset (Euc 2)} (hV : InConvexPosition V)
    {p a b : Euc 2} (hp : p ∈ V) (ha : a ∈ V) (hb : b ∈ V)
    (hpa : p ≠ a) (hpb : p ≠ b) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (heq : p = (1 - t) • a + t • b) : False := by
  apply hV p hp
  exact heq ▸ seg_conv (s := ((V.erase p : Finset (Euc 2)) : Set (Euc 2)))
    (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨Ne.symm hpa, ha⟩))
    (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨Ne.symm hpb, hb⟩)) ht0.le ht1.le

/-- Coordinate evaluation of a convex combination. -/
private lemma smul_add_apply {u v : Euc 2} {a b : ℝ} (i : Fin 2) :
    (a • u + b • v) i = a * u i + b * v i := by
  simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- Three distinct vertices of a convex-position planar set have nonzero
signed area (they are not collinear). -/
private lemma crs_ne_zero_of_convex {V : Finset (Euc 2)} (hV : InConvexPosition V)
    {u v w : Euc 2} (hu : u ∈ V) (hv : v ∈ V) (hw : w ∈ V)
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) : crs u v w ≠ 0 := by
  intro h
  have hne : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  obtain ⟨c, hc⟩ := exists_smul_of_cr2_eq_zero hne h
  -- `w = (1 - c) • u + c • v`
  have hweq : w = (1 - c) • u + c • v := by
    have hw' : w = u + c • (v - u) := by
      rw [← hc]
      simp
    rw [hw', smul_sub, sub_smul, one_smul]
    abel
  have hcoor : ∀ i : Fin 2, w i = (1 - c) * u i + c * v i := by
    intro i
    have := congrArg (fun z : Euc 2 ↦ z i) hweq
    rwa [smul_add_apply] at this
  rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
  · -- c < 0 : u = (1 - t) • v + t • w with t = 1/(1-c) ∈ (0,1)
    have h1c : (0:ℝ) < 1 - c := by linarith
    have ht0 : (0:ℝ) < 1 / (1 - c) := by positivity
    have ht1 : 1 / (1 - c) < 1 := by
      rw [div_lt_one h1c]; linarith
    have h1c' : (1 : ℝ) - c ≠ 0 := ne_of_gt h1c
    have heq : u = (1 - 1 / (1 - c)) • v + (1 / (1 - c)) • w := by
      apply PiLp.ext
      intro i
      have h := hcoor i
      rw [smul_add_apply]
      field_simp
      linear_combination -h
    exact not_mem_conv_pair hV hu hv hw huv huw ht0 ht1 heq
  · -- c = 0 : w = u
    rw [hc0] at hweq
    simp at hweq
    exact huw hweq.symm
  · rcases lt_trichotomy c 1 with hc1 | hc1 | hc1
    · -- 0 < c < 1 : w lies strictly between u and v
      exact not_mem_conv_pair hV hw hu hv (Ne.symm huw) (Ne.symm hvw) hc0 hc1 hweq
    · -- c = 1 : w = v
      rw [hc1] at hweq
      simp at hweq
      exact hvw hweq.symm
    · -- c > 1 : v = (1 - 1/c) • u + (1/c) • w
      have hcpos : (0:ℝ) < c := by linarith
      have ht0 : (0:ℝ) < 1 / c := by positivity
      have ht1 : 1 / c < 1 := by rw [div_lt_one hcpos]; exact hc1
      have hc' : c ≠ 0 := ne_of_gt hcpos
      have heq : v = (1 - 1 / c) • u + (1 / c) • w := by
        apply PiLp.ext
        intro i
        have h := hcoor i
        rw [smul_add_apply]
        field_simp
        linear_combination -h
      exact not_mem_conv_pair hV hv hu hw (Ne.symm huv) hvw ht0 ht1 heq

/-- A vertex `p` of a convex-position set is never in the convex hull of three
other vertices. -/
private lemma not_mem_conv_triple {V : Finset (Euc 2)} (hV : InConvexPosition V)
    {p x y z : Euc 2} (hp : p ∈ V) (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V)
    (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) :
    p ∉ convexHull ℝ (({x, y, z} : Finset (Euc 2)) : Set (Euc 2)) := by
  intro h
  apply hV p hp
  apply convexHull_mono _ h
  intro q hq
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨Ne.symm hpx, hx⟩)
  · exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨Ne.symm hpy, hy⟩)
  · exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨Ne.symm hpz, hz⟩)

/-- Separating a vertex of a convex-position finite set from the other
vertices: `f` is strictly positive on all difference vectors `p - o`. -/
private lemma exists_sep {V : Finset (Euc 2)} (hV : InConvexPosition V)
    {o : Euc 2} (ho : o ∈ V) :
    ∃ f : Euc 2 →ₗ[ℝ] ℝ, ∀ p ∈ V, p ≠ o → 0 < f (p - o) := by
  have hKo : o ∉ convexHull ℝ ((V.erase o : Finset (Euc 2)) : Set (Euc 2)) :=
    hV o ho
  obtain ⟨F, u, hF1, hF2⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _)
    (Set.Finite.isClosed_convexHull ℝ (Finset.finite_toSet _))
    hKo
  refine ⟨-F.toLinearMap, fun p hp hpo ↦ ?_⟩
  have hpK : p ∈ convexHull ℝ ((V.erase o : Finset (Euc 2)) : Set (Euc 2)) :=
    subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hpo, hp⟩))
  have hlt : F p < F o := lt_trans (hF1 _ hpK) hF2
  have hneg : F (p - o) < 0 := by
    have hsub : F (p - o) = F p - F o := map_sub F p o
    rw [hsub]
    linarith [hlt]
  have : 0 < -(F.toLinearMap (p - o)) := by
    have : F.toLinearMap (p - o) = F (p - o) := rfl
    rw [this]; linarith
  simpa [LinearMap.neg_apply] using this

/-- `crs` expressed in differences from a basepoint `o`. -/
private lemma crs_sub (o u v w : Euc 2) :
    crs u v w = cr2 (u - o) (v - o) + cr2 (v - o) (w - o) + cr2 (w - o) (u - o) := by
  simp only [crs, cr2, PiLp.sub_apply]
  ring

/-- The key identity: `crs u v w · f e` factors through the `(f, cr2 e)`-slope
coordinates. -/
private lemma crs_C (f : Euc 2 →ₗ[ℝ] ℝ) (e o u v w : Euc 2)
    (hu : f (u - o) ≠ 0) (hv : f (v - o) ≠ 0) (hw : f (w - o) ≠ 0) :
    crs u v w * f e = f (u - o) * f (v - o) * f (w - o) *
      ((cr2 e (v - o) / f (v - o) - cr2 e (u - o) / f (u - o)) / f (w - o) -
       (cr2 e (v - o) / f (v - o) - cr2 e (w - o) / f (w - o)) / f (u - o) -
       (cr2 e (w - o) / f (w - o) - cr2 e (u - o) / f (u - o)) / f (v - o)) := by
  rw [crs_sub, add_mul, add_mul, cr2_mul_fe, cr2_mul_fe, cr2_mul_fe]
  field_simp
  ring

/-- A point with vanishing `(f, cr2 e)`-coordinates is zero. -/
private lemma eq_zero_of_f_cr2_eq_zero {f : Euc 2 →ₗ[ℝ] ℝ} {e D : Euc 2}
    (he : e ≠ 0) (hfe : 0 < f e) (h1 : f D = 0) (h2 : cr2 e D = 0) : D = 0 := by
  obtain ⟨c, hc⟩ := exists_smul_of_cr2_eq_zero he h2
  have hfD : c * f e = 0 := by
    have := map_smul f c e
    rw [← hc] at this
    rw [smul_eq_mul] at this
    rw [h1] at this
    exact this.symm
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hfD with h | h
    · exact h
    · exact absurd h (ne_of_gt hfe)
  rw [hc, hc0, zero_smul]

/-- If both `cr2 E p = 0` and `cr2 E q = 0` for linearly independent `p, q`,
then `E = 0`. -/
private lemma eq_zero_of_cr2_eq_zero_pair {E p q : Euc 2} (hpq : cr2 p q ≠ 0)
    (h1 : cr2 E p = 0) (h2 : cr2 E q = 0) : E = 0 := by
  have e1 : E 0 * p 1 - E 1 * p 0 = 0 := by
    have := h1; simp only [cr2, sub_eq_zero] at this; linarith [this]
  have e2 : E 0 * q 1 - E 1 * q 0 = 0 := by
    have := h2; simp only [cr2, sub_eq_zero] at this; linarith [this]
  apply PiLp.ext
  intro i
  fin_cases i
  · show E 0 = 0
    have key : E 0 * cr2 p q = p 0 * (E 0 * q 1 - E 1 * q 0) -
        q 0 * (E 0 * p 1 - E 1 * p 0) := by
      simp only [cr2]
      ring
    rw [e1, e2, mul_zero, mul_zero, sub_zero] at key
    exact (mul_eq_zero.mp key).resolve_right hpq
  · show E 1 = 0
    have key : E 1 * cr2 p q = p 1 * (E 0 * q 1 - E 1 * q 0) -
        q 1 * (E 0 * p 1 - E 1 * p 0) := by
      simp only [cr2]
      ring
    rw [e1, e2, mul_zero, mul_zero, sub_zero] at key
    exact (mul_eq_zero.mp key).resolve_right hpq

/-- The `C`-quantity flips sign when the first and third roles are swapped. -/
private lemma C_swap13 (fu fv fw su sv sw : ℝ)
    (hu : fu ≠ 0) (hv : fv ≠ 0) (hw : fw ≠ 0) :
    (sv - sw) / fu - (sv - su) / fw - (su - sw) / fv =
      -((sv - su) / fw - (sv - sw) / fu - (sw - su) / fv) := by
  field_simp
  ring

/-- The `M`-quantity used in `mem_conv_of_C` is the negative of the `K`-factor
produced by `crs_C`. -/
private lemma C_neg (fu fv fw su sv sw : ℝ) :
    (sw - su) / fv - (sw - sv) / fu - (sv - su) / fw =
      -((sv - su) / fw - (sv - sw) / fu - (sw - su) / fv) := by
  ring

/-- Negation in the first `cr2` argument. -/
private lemma cr2_neg_left (u v : Euc 2) : cr2 (-u) v = -cr2 u v := by
  simp [cr2, PiLp.neg_apply]
  ring

/-- Negation in the second `cr2` argument. -/
private lemma cr2_neg_right (u v : Euc 2) : cr2 u (-v) = -cr2 u v := by
  simp [cr2, PiLp.neg_apply]
  ring

/-- An explicit convex combination of three points lies in their convex hull. -/
private lemma mem_conv_triple_of_combination {o u w v : Euc 2} {α β γ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hsum : α + β + γ = 1)
    (heq : v = γ • o + α • u + β • w) :
    v ∈ convexHull ℝ (({o, u, w} : Finset (Euc 2)) : Set (Euc 2)) := by
  rcases lt_or_eq_of_le hγ with hγp | hγe
  · rcases lt_or_eq_of_le (show (0 : ℝ) ≤ 1 - γ by linarith) with h1γ | h1γ
    · -- `0 < 1 - γ`: write `v` on the segment from `o` to a point of `[u,w]`.
      have hz : (1 - β / (1 - γ)) • u + (β / (1 - γ)) • w ∈
          convexHull ℝ (({o, u, w} : Finset (Euc 2)) : Set (Euc 2)) := by
        apply seg_conv
        · exact Finset.mem_coe.2 (by simp)
        · exact Finset.mem_coe.2 (by simp)
        · positivity
        · rw [div_le_one h1γ]
          linarith [hα]
      have hv : v = (1 - (1 - γ)) • o + (1 - γ) •
          ((1 - β / (1 - γ)) • u + (β / (1 - γ)) • w) := by
        have e1 : (1 - γ) * (1 - β / (1 - γ)) = α := by
          field_simp
          linarith [hsum]
        have e2 : (1 - γ) * (β / (1 - γ)) = β := by
          field_simp
        rw [heq, show (1 - (1 - γ) : ℝ) = γ by ring, smul_add, smul_smul,
          smul_smul, e1, e2, add_assoc]
      rw [hv]
      have hoz : o ∈ convexHull ℝ (({o, u, w} : Finset (Euc 2)) : Set (Euc 2)) :=
        subset_convexHull ℝ _ (Finset.mem_coe.2 (by simp))
      apply (convex_convexHull ℝ _).segment_subset hoz hz
      rw [segment_eq_image_lineMap]
      exact ⟨1 - γ, ⟨by linarith, by linarith [hγ]⟩,
        AffineMap.lineMap_apply_module o _ (1 - γ)⟩
    · -- `1 - γ = 0`, so `v = o`
      have hγ1 : γ = 1 := by linarith
      have hα0 : α = 0 := by linarith [hα, hβ, hsum]
      have hβ0 : β = 0 := by linarith [hα, hβ, hsum]
      rw [heq, hγ1, hα0, hβ0]
      simp only [one_smul, zero_smul, add_zero]
      exact subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
  · -- `γ = 0`: `v` is on the segment `[u,w]`
    have hα' : α = 1 - β := by linarith [hsum]
    have hv : v = (1 - β) • u + β • w := by
      rw [heq, ← hγe, zero_smul, zero_add, hα']
    rw [hv]
    apply seg_conv
    · exact Finset.mem_coe.2 (by simp)
    · exact Finset.mem_coe.2 (by simp)
    · exact hβ
    · linarith [hα]

/-- If the `C`-quantity is nonnegative for `σ_u < σ_v < σ_w`, then `v` lies in
the convex hull of `{o, u, w}` — contradicting convex position. -/
private lemma mem_conv_of_C {f : Euc 2 →ₗ[ℝ] ℝ} {e o u v w : Euc 2}
    (he : e ≠ 0) (hfe : 0 < f e)
    (hu : 0 < f (u - o)) (hv : 0 < f (v - o)) (hw : 0 < f (w - o))
    (hσ1 : cr2 e (u - o) / f (u - o) < cr2 e (v - o) / f (v - o))
    (hσ2 : cr2 e (v - o) / f (v - o) < cr2 e (w - o) / f (w - o))
    (hC : 0 ≤ (cr2 e (w - o) / f (w - o) - cr2 e (u - o) / f (u - o)) / f (v - o)
          - (cr2 e (w - o) / f (w - o) - cr2 e (v - o) / f (v - o)) / f (u - o)
          - (cr2 e (v - o) / f (v - o) - cr2 e (u - o) / f (u - o)) / f (w - o)) :
    v ∈ convexHull ℝ (({o, u, w} : Finset (Euc 2)) : Set (Euc 2)) := by
  -- abbreviations
  set fu := f (u - o) with hfudef
  set fv := f (v - o) with hfvdef
  set fw := f (w - o) with hfwdef
  set su := cr2 e (u - o) / fu with hsudef
  set sv := cr2 e (v - o) / fv with hsvdef
  set sw := cr2 e (w - o) / fw with hswdef
  have hfu : fu ≠ 0 := ne_of_gt hu
  have hfv : fv ≠ 0 := ne_of_gt hv
  have hfw : fw ≠ 0 := ne_of_gt hw
  have hgu : cr2 e (u - o) = su * fu := (div_mul_cancel₀ _ hfu).symm
  have hgv : cr2 e (v - o) = sv * fv := (div_mul_cancel₀ _ hfv).symm
  have hgw : cr2 e (w - o) = sw * fw := (div_mul_cancel₀ _ hfw).symm
  have hd' : 0 < sw - su := sub_pos.mpr (lt_trans hσ1 hσ2)
  have hdne : sw - su ≠ 0 := ne_of_gt hd'
  have hdu : fu * (sw - su) ≠ 0 := mul_ne_zero hfu hdne
  have hdw : fw * (sw - su) ≠ 0 := mul_ne_zero hfw hdne
  -- the three weights
  set A := fv * (sw - sv) / (fu * (sw - su)) with hAdef
  set B := fv * (sv - su) / (fw * (sw - su)) with hBdef
  set G := 1 - A - B with hGdef
  have hApos : 0 < A := by
    rw [hAdef]
    apply div_pos (mul_pos hv (sub_pos.mpr hσ2))
    exact mul_pos hu hd'
  have hBpos : 0 < B := by
    rw [hBdef]
    apply div_pos (mul_pos hv (sub_pos.mpr hσ1))
    exact mul_pos hw hd'
  have hAD : A * (fu * (sw - su)) = fv * (sw - sv) :=
    div_mul_cancel₀ _ hdu
  have hBD : B * (fw * (sw - su)) = fv * (sv - su) :=
    div_mul_cancel₀ _ hdw
  have hGnonneg : 0 ≤ G := by
    have hAD' : A * (fu * fw * (sw - su)) = fv * (sw - sv) * fw := by
      have e : fu * fw * (sw - su) = fu * (sw - su) * fw := by ring
      rw [e, ← mul_assoc, hAD]
    have hBD' : B * (fu * fw * (sw - su)) = fv * (sv - su) * fu := by
      have e : fu * fw * (sw - su) = fw * (sw - su) * fu := by ring
      rw [e, ← mul_assoc, hBD]
    have hCeq : ((sw - su) / fv - (sw - sv) / fu - (sv - su) / fw) *
        (fu * fv * fw) =
        fu * fw * (sw - su) - fv * fw * (sw - sv) - fu * fv * (sv - su) := by
      field_simp
    have key : G * (fu * fw * (sw - su)) =
        ((sw - su) / fv - (sw - sv) / fu - (sv - su) / fw) * (fu * fv * fw) := by
      rw [hGdef, hCeq]
      linear_combination -hAD' - hBD'
    have hnn : 0 ≤ G * (fu * fw * (sw - su)) := by
      rw [key]
      exact mul_nonneg hC (mul_nonneg (mul_nonneg hu.le hv.le) hw.le)
    exact nonneg_of_mul_nonneg_left hnn
      (mul_pos (mul_pos hu hw) hd')
  -- the difference vector `v - (G o + A u + B w)` is zero
  have hDeq : (v - o) - A • (u - o) - B • (w - o) =
      v - (G • o + A • u + B • w) := by
    rw [hGdef, smul_sub, smul_sub, sub_smul, sub_smul, one_smul]
    abel
  have hfD : f ((v - o) - A • (u - o) - B • (w - o)) = 0 := by
    rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      ← hfudef, ← hfvdef, ← hfwdef]
    -- `fv - A·fu - B·fw = 0`; multiply by `sw - su ≠ 0`
    have e1 : A * fu * (sw - su) = fv * (sw - sv) := by
      rw [mul_assoc]
      exact hAD
    have e2 : B * fw * (sw - su) = fv * (sv - su) := by
      rw [mul_assoc]
      exact hBD
    have hD' : (fv - A * fu - B * fw) * (sw - su) = 0 := by
      linear_combination -e1 - e2
    rcases mul_eq_zero.mp hD' with h | h
    · exact h
    · exact absurd h hdne
  have hgD : cr2 e ((v - o) - A • (u - o) - B • (w - o)) = 0 := by
    rw [cr2_sub_right, cr2_sub_right, cr2_smul_right, cr2_smul_right,
      hgu, hgv, hgw]
    -- `sv·fv - A·(su·fu) - B·(sw·fw) = 0`; multiply by `sw - su ≠ 0`
    have e3 : A * (su * fu) * (sw - su) = su * (fv * (sw - sv)) := by
      linear_combination su * hAD
    have e4 : B * (sw * fw) * (sw - su) = sw * (fv * (sv - su)) := by
      linear_combination sw * hBD
    have hD' : (sv * fv - A * (su * fu) - B * (sw * fw)) * (sw - su) = 0 := by
      linear_combination -e3 - e4
    rcases mul_eq_zero.mp hD' with h | h
    · exact h
    · exact absurd h hdne
  have hD0 : (v - o) - A • (u - o) - B • (w - o) = 0 :=
    eq_zero_of_f_cr2_eq_zero he hfe hfD hgD
  rw [hDeq] at hD0
  have hv_eq : v = G • o + A • u + B • w := sub_eq_zero.mp hD0
  exact mem_conv_triple_of_combination hApos.le hBpos.le hGnonneg
    (by rw [hGdef]; ring) hv_eq

/-- The main crossing lemma: if `σ_a < σ_b < σ_c < σ_d` for vertices of a
convex-position set (with `f` the separating functional at `o`), then the
segments `[a,c]` and `[b,d]` cross at an interior point. -/
private lemma chord_cross {V : Finset (Euc 2)} (hV : InConvexPosition V)
    {f : Euc 2 →ₗ[ℝ] ℝ} {e o a b c d : Euc 2}
    (he : e ≠ 0) (hfe : 0 < f e)
    (hf : ∀ p ∈ V, p ≠ o → 0 < f (p - o))
    (ho : o ∈ V) (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V)
    (hoa : o ≠ a) (hob : o ≠ b) (hoc : o ≠ c) (hod : o ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hσ1 : cr2 e (a - o) / f (a - o) < cr2 e (b - o) / f (b - o))
    (hσ2 : cr2 e (b - o) / f (b - o) < cr2 e (c - o) / f (c - o))
    (hσ3 : cr2 e (c - o) / f (c - o) < cr2 e (d - o) / f (d - o)) :
    ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      a + s • (c - a) = b + t • (d - b) := by
  have hf_a := hf a ha (Ne.symm hoa)
  have hf_b := hf b hb (Ne.symm hob)
  have hf_c := hf c hc (Ne.symm hoc)
  have hf_d := hf d hd (Ne.symm hod)
  have hfu : f (a - o) ≠ 0 := ne_of_gt hf_a
  have hfv : f (b - o) ≠ 0 := ne_of_gt hf_b
  have hfw : f (c - o) ≠ 0 := ne_of_gt hf_c
  have hfx : f (d - o) ≠ 0 := ne_of_gt hf_d
  -- `crs a c b < 0`: otherwise `M(a,b,c) ≥ 0` puts `b` in `conv{o,a,c}`
  have hB1 : crs a c b < 0 := by
    by_contra h
    push_neg at h
    have habc : crs a b c ≤ 0 := by
      have hanti := crs_anticomm_mid a b c
      linarith
    have key := crs_C f e o a b c hfu hfv hfw
    have hnn : f (a - o) * f (b - o) * f (c - o) *
        ((cr2 e (b - o) / f (b - o) - cr2 e (a - o) / f (a - o)) / f (c - o) -
         (cr2 e (b - o) / f (b - o) - cr2 e (c - o) / f (c - o)) / f (a - o) -
         (cr2 e (c - o) / f (c - o) - cr2 e (a - o) / f (a - o)) / f (b - o))
        ≤ 0 := by
      have hle : crs a b c * f e ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg habc hfe.le
      rwa [key] at hle
    have hK : (cr2 e (b - o) / f (b - o) - cr2 e (a - o) / f (a - o)) / f (c - o) -
        (cr2 e (b - o) / f (b - o) - cr2 e (c - o) / f (c - o)) / f (a - o) -
        (cr2 e (c - o) / f (c - o) - cr2 e (a - o) / f (a - o)) / f (b - o) ≤ 0 :=
      nonpos_of_mul_nonpos_right hnn (mul_pos (mul_pos hf_a hf_b) hf_c)
    have hC : 0 ≤ (cr2 e (c - o) / f (c - o) - cr2 e (a - o) / f (a - o)) / f (b - o)
        - (cr2 e (c - o) / f (c - o) - cr2 e (b - o) / f (b - o)) / f (a - o)
        - (cr2 e (b - o) / f (b - o) - cr2 e (a - o) / f (a - o)) / f (c - o) := by
      rw [C_neg (f (a - o)) (f (b - o)) (f (c - o)) (cr2 e (a - o) / f (a - o))
        (cr2 e (b - o) / f (b - o)) (cr2 e (c - o) / f (c - o))]
      exact neg_nonneg.mpr hK
    exact not_mem_conv_triple hV hb ho ha hc (Ne.symm hob) (Ne.symm hab) hbc
      (mem_conv_of_C he hfe hf_a hf_b hf_c hσ1 hσ2 hC)
  -- `crs b d c < 0`: otherwise `M(b,c,d) ≥ 0` puts `c` in `conv{o,b,d}`
  have hB2 : crs b d c < 0 := by
    by_contra h
    push_neg at h
    have hbcd : crs b c d ≤ 0 := by
      have hanti := crs_anticomm_mid b c d
      linarith
    have key := crs_C f e o b c d hfv hfw hfx
    have hnn : f (b - o) * f (c - o) * f (d - o) *
        ((cr2 e (c - o) / f (c - o) - cr2 e (b - o) / f (b - o)) / f (d - o) -
         (cr2 e (c - o) / f (c - o) - cr2 e (d - o) / f (d - o)) / f (b - o) -
         (cr2 e (d - o) / f (d - o) - cr2 e (b - o) / f (b - o)) / f (c - o))
        ≤ 0 := by
      have hle : crs b c d * f e ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hbcd hfe.le
      rwa [key] at hle
    have hK : (cr2 e (c - o) / f (c - o) - cr2 e (b - o) / f (b - o)) / f (d - o) -
        (cr2 e (c - o) / f (c - o) - cr2 e (d - o) / f (d - o)) / f (b - o) -
        (cr2 e (d - o) / f (d - o) - cr2 e (b - o) / f (b - o)) / f (c - o) ≤ 0 :=
      nonpos_of_mul_nonpos_right hnn (mul_pos (mul_pos hf_b hf_c) hf_d)
    have hC : 0 ≤ (cr2 e (d - o) / f (d - o) - cr2 e (b - o) / f (b - o)) / f (c - o)
        - (cr2 e (d - o) / f (d - o) - cr2 e (c - o) / f (c - o)) / f (b - o)
        - (cr2 e (c - o) / f (c - o) - cr2 e (b - o) / f (b - o)) / f (d - o) := by
      rw [C_neg (f (b - o)) (f (c - o)) (f (d - o)) (cr2 e (b - o) / f (b - o))
        (cr2 e (c - o) / f (c - o)) (cr2 e (d - o) / f (d - o))]
      exact neg_nonneg.mpr hK
    exact not_mem_conv_triple hV hc ho hb hd (Ne.symm hoc) (Ne.symm hbc) hcd
      (mem_conv_of_C he hfe hf_b hf_c hf_d hσ2 hσ3 hC)
  -- `crs a c d > 0`: otherwise `M(a,c,d) ≥ 0` puts `c` in `conv{o,a,d}`
  have hA1 : crs a c d > 0 := by
    by_contra h
    push_neg at h
    have key := crs_C f e o a c d hfu hfw hfx
    have hnn : f (a - o) * f (c - o) * f (d - o) *
        ((cr2 e (c - o) / f (c - o) - cr2 e (a - o) / f (a - o)) / f (d - o) -
         (cr2 e (c - o) / f (c - o) - cr2 e (d - o) / f (d - o)) / f (a - o) -
         (cr2 e (d - o) / f (d - o) - cr2 e (a - o) / f (a - o)) / f (c - o))
        ≤ 0 := by
      have hle : crs a c d * f e ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h hfe.le
      rwa [key] at hle
    have hK : (cr2 e (c - o) / f (c - o) - cr2 e (a - o) / f (a - o)) / f (d - o) -
        (cr2 e (c - o) / f (c - o) - cr2 e (d - o) / f (d - o)) / f (a - o) -
        (cr2 e (d - o) / f (d - o) - cr2 e (a - o) / f (a - o)) / f (c - o) ≤ 0 :=
      nonpos_of_mul_nonpos_right hnn (mul_pos (mul_pos hf_a hf_c) hf_d)
    have hC : 0 ≤ (cr2 e (d - o) / f (d - o) - cr2 e (a - o) / f (a - o)) / f (c - o)
        - (cr2 e (d - o) / f (d - o) - cr2 e (c - o) / f (c - o)) / f (a - o)
        - (cr2 e (c - o) / f (c - o) - cr2 e (a - o) / f (a - o)) / f (d - o) := by
      rw [C_neg (f (a - o)) (f (c - o)) (f (d - o)) (cr2 e (a - o) / f (a - o))
        (cr2 e (c - o) / f (c - o)) (cr2 e (d - o) / f (d - o))]
      exact neg_nonneg.mpr hK
    have hσ13' : cr2 e (a - o) / f (a - o) < cr2 e (c - o) / f (c - o) :=
      lt_trans hσ1 hσ2
    exact not_mem_conv_triple hV hc ho ha hd (Ne.symm hoc) (Ne.symm hac) hcd
      (mem_conv_of_C he hfe hf_a hf_c hf_d hσ13' hσ3 hC)
  -- `crs b d a > 0`: otherwise `M(a,b,d) ≥ 0` puts `b` in `conv{o,a,d}`
  have hA2 : crs b d a > 0 := by
    by_contra h
    push_neg at h
    have habd : crs a b d ≤ 0 := by
      have h1 := crs_eq_cycle b d a
      have h2 := crs_eq_cycle a b d
      linarith
    have key := crs_C f e o a b d hfu hfv hfx
    have hnn : f (a - o) * f (b - o) * f (d - o) *
        ((cr2 e (b - o) / f (b - o) - cr2 e (a - o) / f (a - o)) / f (d - o) -
         (cr2 e (b - o) / f (b - o) - cr2 e (d - o) / f (d - o)) / f (a - o) -
         (cr2 e (d - o) / f (d - o) - cr2 e (a - o) / f (a - o)) / f (b - o))
        ≤ 0 := by
      have hle : crs a b d * f e ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg habd hfe.le
      rwa [key] at hle
    have hK : (cr2 e (b - o) / f (b - o) - cr2 e (a - o) / f (a - o)) / f (d - o) -
        (cr2 e (b - o) / f (b - o) - cr2 e (d - o) / f (d - o)) / f (a - o) -
        (cr2 e (d - o) / f (d - o) - cr2 e (a - o) / f (a - o)) / f (b - o) ≤ 0 :=
      nonpos_of_mul_nonpos_right hnn (mul_pos (mul_pos hf_a hf_b) hf_d)
    have hC : 0 ≤ (cr2 e (d - o) / f (d - o) - cr2 e (a - o) / f (a - o)) / f (b - o)
        - (cr2 e (d - o) / f (d - o) - cr2 e (b - o) / f (b - o)) / f (a - o)
        - (cr2 e (b - o) / f (b - o) - cr2 e (a - o) / f (a - o)) / f (d - o) := by
      rw [C_neg (f (a - o)) (f (b - o)) (f (d - o)) (cr2 e (a - o) / f (a - o))
        (cr2 e (b - o) / f (b - o)) (cr2 e (d - o) / f (d - o))]
      exact neg_nonneg.mpr hK
    have hσbd : cr2 e (b - o) / f (b - o) < cr2 e (d - o) / f (d - o) :=
      lt_trans hσ2 hσ3
    exact not_mem_conv_triple hV hb ho ha hd (Ne.symm hob) (Ne.symm hab) hbd
      (mem_conv_of_C he hfe hf_a hf_b hf_d hσ1 hσbd hC)
  -- determinant of the two chord directions
  have hD : crs a c d - crs a c b = cr2 (c - a) (d - b) := by
    simp only [crs, cr2, PiLp.sub_apply]
    ring
  have hDpos : 0 < crs a c d - crs a c b := by linarith [hA1, hB1]
  have hDne : cr2 (c - a) (d - b) ≠ 0 := by
    rw [← hD]
    exact ne_of_gt hDpos
  have hDa : crs b d a - (crs a c d - crs a c b) = crs b d c := by
    simp only [crs, cr2, PiLp.sub_apply]
    ring
  refine ⟨crs b d a / (crs a c d - crs a c b),
          -crs a c b / (crs a c d - crs a c b), ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos hA2 hDpos
  · rw [div_lt_one hDpos]
    linarith [hDa, hB2]
  · exact div_pos (neg_pos.mpr hB1) hDpos
  · rw [div_lt_one hDpos]
    linarith [hA1, hB1]
  · -- the crossing equality: `a + s•(c−a) = b + t•(d−b)`
    set s := crs b d a / (crs a c d - crs a c b) with hs
    set t := -crs a c b / (crs a c d - crs a c b) with ht
    have hsD : s * (crs a c d - crs a c b) = crs b d a :=
      div_mul_cancel₀ _ (ne_of_gt hDpos)
    have htD : t * (crs a c d - crs a c b) = -crs a c b :=
      div_mul_cancel₀ _ (ne_of_gt hDpos)
    have hE1 : cr2 (s • (c - a) - t • (d - b) - (b - a)) (c - a) = 0 := by
      rw [cr2_sub_left, cr2_sub_left, cr2_smul_left, cr2_smul_left, cr2_self]
      have h1 : cr2 (d - b) (c - a) = -(crs a c d - crs a c b) := by
        rw [cr2_anticomm, ← hD]
      have h2 : cr2 (b - a) (c - a) = -crs a c b := by
        rw [cr2_anticomm]; rfl
      rw [h1, h2]
      simp only [mul_zero, zero_sub, mul_neg, sub_neg_eq_add, neg_neg]
      linarith [htD]
    have hE2 : cr2 (s • (c - a) - t • (d - b) - (b - a)) (d - b) = 0 := by
      rw [cr2_sub_left, cr2_sub_left, cr2_smul_left, cr2_smul_left, cr2_self]
      have h3 : cr2 (b - a) (d - b) = crs b d a := by
        rw [← neg_sub a b, cr2_neg_left, cr2_anticomm, neg_neg]; rfl
      rw [← hD, h3]
      simp only [mul_zero, sub_zero]
      linarith [hsD]
    have hE0 := eq_zero_of_cr2_eq_zero_pair hDne hE1 hE2
    have key : a + s • (c - a) - (b + t • (d - b)) =
        s • (c - a) - t • (d - b) - (b - a) := by
      abel
    rw [hE0] at key
    exact sub_eq_zero.mp key

/-- `proj2` on coordinates. -/
private lemma proj2_apply (v : Euc 3) (i : Fin 2) : proj2 v i = v i.castSucc := rfl

/-- `Finset.univ` on `Fin 2` mapped by an embedding. -/
private lemma univ_map_two {N : ℕ} (e : Fin 2 ↪ Fin N) :
    Finset.univ.map e = ({e 0, e 1} : Finset (Fin N)) := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- `Finset.univ` on `Fin 4` mapped by an embedding. -/
private lemma univ_map_four {N : ℕ} (e : Fin 4 ↪ Fin N) :
    Finset.univ.map e = ({e 0, e 1, e 2, e 3} : Finset (Fin N)) := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- A two-element index finset equals the pair of its sorted elements. -/
private lemma sorted_two_eq {N : ℕ} (T : Finset (Fin N)) (hT : T.card = 2) :
    ({T.orderEmbOfFin hT 0, T.orderEmbOfFin hT 1} : Finset (Fin N)) = T :=
  ((univ_map_two (T.orderEmbOfFin hT).toEmbedding).symm.trans
    (Finset.map_orderEmbOfFin_univ T hT))

/-- A four-element index finset equals the quadruple of its sorted
elements. -/
private lemma sorted_four_eq {N : ℕ} (T : Finset (Fin N)) (hT : T.card = 4) :
    ({T.orderEmbOfFin hT 0, T.orderEmbOfFin hT 1, T.orderEmbOfFin hT 2,
      T.orderEmbOfFin hT 3} : Finset (Fin N)) = T :=
  ((univ_map_four (T.orderEmbOfFin hT).toEmbedding).symm.trans
    (Finset.map_orderEmbOfFin_univ T hT))

/-- The four-element index finset. -/
private lemma card_four {N : ℕ} {a b c d : Fin N}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ({a, b, c, d} : Finset (Fin N)).card = 4 := by
  have ha : a ∉ ({b, c, d} : Finset (Fin N)) := by
    simp [hab.ne, (lt_trans hab hbc).ne, (lt_trans hab (lt_trans hbc hcd)).ne]
  have hb : b ∉ ({c, d} : Finset (Fin N)) := by
    simp [hbc.ne, (lt_trans hbc hcd).ne]
  have hc : c ∉ ({d} : Finset (Fin N)) := by simp [hcd.ne]
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb,
    Finset.card_insert_of_notMem hc, Finset.card_singleton]

/-- Affine independence of `x` restricted to four strictly increasing
indices, transported from general position. -/
private lemma affine_indep_four {N : ℕ} {x : Fin N → Euc 3}
    (hx : Function.Injective x)
    (hgp : InGeneralPosition ((Finset.image x Finset.univ : Finset (Euc 3)) : Set (Euc 3)))
    {i i' j j' : Fin N} (hii' : i < i') (hi'j : i' < j) (hjj' : j < j') :
    AffineIndependent ℝ
      (fun a : ↥({i, i', j, j'} : Finset (Fin N)) ↦ x (a : Fin N)) := by
  set I : Finset (Fin N) := {i, i', j, j'} with hIdef
  have hIcard : I.card = 4 := card_four hii' hi'j hjj'
  set Y : Finset (Euc 3) := Finset.image x I with hYdef
  have hYsub : (Y : Set (Euc 3)) ⊆ ↑(Finset.image x Finset.univ) := by
    rw [hYdef]
    apply Finset.coe_subset.mpr
    apply Finset.image_mono
    exact Finset.subset_univ _
  have hYcard : Y.card = 4 := by
    rw [hYdef, Finset.card_image_of_injective _ hx, hIcard]
  have hAI := hgp Y hYsub hYcard
  set emb : ↥I ↪ ↥Y :=
    ⟨fun a ↦ ⟨x a, Finset.mem_image.2 ⟨a, a.2, rfl⟩⟩,
     fun a b hab ↦ Subtype.ext (hx (Subtype.ext_iff.mp hab))⟩
  exact hAI.comp_embedding emb

/-- The `z`-coordinates at the crossing cannot agree, by affine
independence of the four endpoints. -/
private lemma z_ne_of_cross {N : ℕ} {x : Fin N → Euc 3}
    {i i' j j' : Fin N} (hii' : i < i') (hi'j : i' < j) (hjj' : j < j')
    (hAI : AffineIndependent ℝ
      (fun a : ↥({i, i', j, j'} : Finset (Fin N)) ↦ x (a : Fin N)))
    {s t : ℝ} (ht1 : t < 1)
    (h : (1 - s) • x i + s • x j = (1 - t) • x i' + t • x j') : False := by
  set I : Finset (Fin N) := {i, i', j, j'} with hIdef
  have hii'ne : i ≠ i' := hii'.ne
  have hijne : i ≠ j := (lt_trans hii' hi'j).ne
  have hij'ne : i ≠ j' := (lt_trans hii' (lt_trans hi'j hjj')).ne
  have hi'jne : i' ≠ j := hi'j.ne
  have hi'j'ne : i' ≠ j' := (lt_trans hi'j hjj').ne
  have hjj'ne : j ≠ j' := hjj'.ne
  have ha : i ∉ ({i', j, j'} : Finset (Fin N)) := by
    simp [hii'ne, hijne, hij'ne]
  have hb : i' ∉ ({j, j'} : Finset (Fin N)) := by
    simp [hi'jne, hi'j'ne]
  have hcc : j ∉ ({j'} : Finset (Fin N)) := by simp [hjj'ne]
  have hsumI : ∀ {M : Type} [AddCommMonoid M] (g : Fin N → M),
      ∑ y ∈ I, g y = g i + (g i' + (g j + g j')) := by
    intro M _ g
    rw [hIdef, Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hcc,
      Finset.sum_singleton]
  have hi'mem : i' ∈ I := by
    rw [hIdef]
    exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert_self _ _))
  -- weight sums
  have hsum1 : ∑ a : ↥I,
      (if (a : Fin N) = i then (1 : ℝ) - s
       else if (a : Fin N) = j then s else 0) = 1 := by
    show ∑ a : ↥I, (fun z : Fin N ↦ if z = i then (1 : ℝ) - s
      else if z = j then s else 0) (a : Fin N) = 1
    rw [Finset.sum_coe_sort (s := I)
      (f := fun z : Fin N ↦ if z = i then (1 : ℝ) - s
        else if z = j then s else 0), hsumI]
    show (if i = i then (1 : ℝ) - s else if i = j then s else 0) +
      ((if i' = i then (1 : ℝ) - s else if i' = j then s else 0) +
      ((if j = i then (1 : ℝ) - s else if j = j then s else 0) +
      (if j' = i then (1 : ℝ) - s else if j' = j then s else 0))) = 1
    rw [if_pos rfl, if_neg hii'ne.symm, if_neg hi'jne, if_neg hijne.symm,
      if_pos rfl, if_neg hij'ne.symm, if_neg hjj'ne.symm]
    ring
  have hsum2 : ∑ a : ↥I,
      (if (a : Fin N) = i' then (1 : ℝ) - t
       else if (a : Fin N) = j' then t else 0) = 1 := by
    show ∑ a : ↥I, (fun z : Fin N ↦ if z = i' then (1 : ℝ) - t
      else if z = j' then t else 0) (a : Fin N) = 1
    rw [Finset.sum_coe_sort (s := I)
      (f := fun z : Fin N ↦ if z = i' then (1 : ℝ) - t
        else if z = j' then t else 0), hsumI]
    show (if i = i' then (1 : ℝ) - t else if i = j' then t else 0) +
      ((if i' = i' then (1 : ℝ) - t else if i' = j' then t else 0) +
      ((if j = i' then (1 : ℝ) - t else if j = j' then t else 0) +
      (if j' = i' then (1 : ℝ) - t else if j' = j' then t else 0))) = 1
    rw [if_neg hii'ne, if_neg hij'ne, if_pos rfl, if_neg hi'jne.symm,
      if_neg hjj'ne, if_neg hi'j'ne.symm, if_pos rfl]
    ring
  -- weighted point sums
  have hsumX1 : ∑ a : ↥I,
      (if (a : Fin N) = i then (1 : ℝ) - s
       else if (a : Fin N) = j then s else 0) • x (a : Fin N) =
      (1 - s) • x i + s • x j := by
    show ∑ a : ↥I, (fun z : Fin N ↦ (if z = i then (1 : ℝ) - s
      else if z = j then s else 0) • x z) (a : Fin N) = _
    rw [Finset.sum_coe_sort (s := I)
      (f := fun z : Fin N ↦ (if z = i then (1 : ℝ) - s
        else if z = j then s else 0) • x z), hsumI]
    show (if i = i then (1 : ℝ) - s else if i = j then s else 0) • x i +
      ((if i' = i then (1 : ℝ) - s else if i' = j then s else 0) • x i' +
      ((if j = i then (1 : ℝ) - s else if j = j then s else 0) • x j +
      (if j' = i then (1 : ℝ) - s else if j' = j then s else 0) • x j')) = _
    rw [if_pos rfl, if_neg hii'ne.symm, if_neg hi'jne, if_neg hijne.symm,
      if_pos rfl, if_neg hij'ne.symm, if_neg hjj'ne.symm]
    simp [zero_smul, add_zero]
  have hsumX2 : ∑ a : ↥I,
      (if (a : Fin N) = i' then (1 : ℝ) - t
       else if (a : Fin N) = j' then t else 0) • x (a : Fin N) =
      (1 - t) • x i' + t • x j' := by
    show ∑ a : ↥I, (fun z : Fin N ↦ (if z = i' then (1 : ℝ) - t
      else if z = j' then t else 0) • x z) (a : Fin N) = _
    rw [Finset.sum_coe_sort (s := I)
      (f := fun z : Fin N ↦ (if z = i' then (1 : ℝ) - t
        else if z = j' then t else 0) • x z), hsumI]
    show (if i = i' then (1 : ℝ) - t else if i = j' then t else 0) • x i +
      ((if i' = i' then (1 : ℝ) - t else if i' = j' then t else 0) • x i' +
      ((if j = i' then (1 : ℝ) - t else if j = j' then t else 0) • x j +
      (if j' = i' then (1 : ℝ) - t else if j' = j' then t else 0) • x j')) = _
    rw [if_neg hii'ne, if_neg hij'ne, if_pos rfl, if_neg hi'jne.symm,
      if_neg hjj'ne, if_neg hi'j'ne.symm, if_pos rfl]
    simp [zero_smul, add_zero]
  have hEq := hAI.eq_of_sum_eq_sum (s := Finset.univ)
    (w₁ := fun a : ↥I ↦
      if (a : Fin N) = i then (1 : ℝ) - s else if (a : Fin N) = j then s else 0)
    (w₂ := fun a : ↥I ↦
      if (a : Fin N) = i' then (1 : ℝ) - t else if (a : Fin N) = j' then t else 0)
    (hsum1.trans hsum2.symm)
    (by rw [hsumX1, hsumX2]; exact h)
  have hval : (if i' = i then (1 : ℝ) - s else if i' = j then s else 0) =
      (if i' = i' then (1 : ℝ) - t else if i' = j' then t else 0) :=
    hEq ⟨i', hi'mem⟩ (Finset.mem_univ _)
  rw [if_neg hii'ne.symm, if_neg hi'jne, if_pos rfl] at hval
  linarith

/-- If the projected convex combinations agree and the third coordinates also
agree, then the two affine combinations of the four affinely independent
points are equal — a contradiction. -/
private lemma z_ne_of_proj_cross {N : ℕ} {x : Fin N → Euc 3}
    {i i' j j' : Fin N} (hii' : i < i') (hi'j : i' < j) (hjj' : j < j')
    (hAI : AffineIndependent ℝ
      (fun a : ↥({i, i', j, j'} : Finset (Fin N)) ↦ x (a : Fin N)))
    {s t : ℝ} (ht1 : t < 1)
    (h : proj2 ((1 - s) • x i + s • x j) =
      proj2 ((1 - t) • x i' + t • x j')) :
    ((1 - s) • x i + s • x j) 2 ≠ ((1 - t) • x i' + t • x j') 2 := by
  intro hz
  apply z_ne_of_cross hii' hi'j hjj' hAI ht1
  apply PiLp.ext
  intro c
  fin_cases c
  · have e := congrArg (fun u : Euc 2 ↦ u ⟨0, by norm_num⟩) h
    simpa [proj2_apply] using e
  · have e := congrArg (fun u : Euc 2 ↦ u ⟨1, by norm_num⟩) h
    simpa [proj2_apply] using e
  · exact hz

/-- The slope `σ v = cr2 e (v−o) / f (v−o)` is injective on `V ∖ {o}`: equal
slopes make `p − o` and `q − o` proportional, so one of `p, q` would lie on
the segment `oq` (resp. `op`) inside `conv (V ∖ {·})`. -/
private lemma sigma_ne {V : Finset (Euc 2)} (hV : InConvexPosition V)
    {f : Euc 2 →ₗ[ℝ] ℝ} {e o p q : Euc 2}
    (he : e ≠ 0) (hfe : 0 < f e)
    (hf : ∀ r ∈ V, r ≠ o → 0 < f (r - o))
    (ho : o ∈ V) (hp : p ∈ V) (hq : q ∈ V)
    (hop : o ≠ p) (hoq : o ≠ q) (hpq : p ≠ q) :
    cr2 e (p - o) / f (p - o) ≠ cr2 e (q - o) / f (q - o) := by
  intro h
  have hfp : 0 < f (p - o) := hf p hp (Ne.symm hop)
  have hfq : 0 < f (q - o) := hf q hq (Ne.symm hoq)
  have key : cr2 e (p - o) * f (q - o) = cr2 e (q - o) * f (p - o) := by
    rwa [div_eq_div_iff hfp.ne' hfq.ne'] at h
  set w : Euc 2 := f (q - o) • (p - o) - f (p - o) • (q - o) with hw
  have hcrw : cr2 e w = 0 := by
    rw [hw, cr2_sub_right, cr2_smul_right, cr2_smul_right]
    linarith [key]
  obtain ⟨c, hc⟩ := exists_smul_of_cr2_eq_zero he hcrw
  have hfw : f w = 0 := by
    rw [hw, map_sub, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  have hc0 : c = 0 := by
    have hz : c * f e = 0 := by
      have hce : f w = c * f e := by rw [hc]; simp [map_smul, smul_eq_mul]
      rw [hfw] at hce
      linarith
    rcases mul_eq_zero.mp hz with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt hfe)
  rw [hc0, zero_smul] at hc
  have hprop : f (q - o) • (p - o) = f (p - o) • (q - o) := sub_eq_zero.mp hc
  -- so `q - o = c' • (p - o)` with `c' = f (q−o) / f (p−o) > 0`
  set c' := f (q - o) / f (p - o) with hc'def
  have hc'pos : 0 < c' := div_pos hfq hfp
  have hqo : q - o = c' • (p - o) := by
    have h2 := congrArg (fun v : Euc 2 ↦ (f (p - o))⁻¹ • v) hprop
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hfp.ne', one_smul] at h2
    rw [hc'def, div_eq_mul_inv, mul_comm]
    exact h2.symm
  have hqeq : q = (1 - c') • o + c' • p := by
    have hqsplit : q = o + (q - o) := by abel
    rw [hqsplit, hqo, smul_sub, sub_smul, one_smul]
    abel
  rcases lt_trichotomy c' 1 with hc'lt | hc'eq | hc'gt
  · have hmem : (1 - c') • o + c' • p ∈
        convexHull ℝ ((V.erase q : Finset (Euc 2)) : Set (Euc 2)) :=
      seg_conv (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hoq, ho⟩))
        (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hpq, hp⟩)) hc'pos.le hc'lt.le
    exact hV q hq (hqeq ▸ hmem)
  · rw [hc'eq] at hqeq
    simp at hqeq
    exact hpq hqeq.symm
  · have hc'ne : c' ≠ 0 := ne_of_gt hc'pos
    have hpo : p - o = c'⁻¹ • (q - o) := by
      have h2 := congrArg (fun v : Euc 2 ↦ c'⁻¹ • v) hqo
      rw [smul_smul, inv_mul_cancel₀ hc'ne, one_smul] at h2
      exact h2.symm
    have hpeq : p = (1 - c'⁻¹) • o + c'⁻¹ • q := by
      have hpsplit : p = o + (p - o) := by abel
      rw [hpsplit, hpo, smul_sub, sub_smul, one_smul]
      abel
    have hc''pos : 0 < c'⁻¹ := by positivity
    have hc''lt : c'⁻¹ < 1 := inv_lt_one_iff₀.2 (Or.inr hc'gt)
    have hmem : (1 - c'⁻¹) • o + c'⁻¹ • q ∈
        convexHull ℝ ((V.erase p : Finset (Euc 2)) : Set (Euc 2)) :=
      seg_conv (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hop, ho⟩))
        (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨Ne.symm hpq, hq⟩))
        hc''pos.le hc''lt.le
    exact hV p hp (hpeq ▸ hmem)

/-- Chord crossing transported to index tuples: if the σ-values of the four
projected points are ordered either as `σ_i < σ_i' < σ_j < σ_j'` or in the
reverse, then the chords `[p_i, p_j]` and `[p_i', p_j']` cross in the
interior. -/
private lemma tuple_cross {N : ℕ} {p : Fin N → Euc 2}
    {V : Finset (Euc 2)} (hV : InConvexPosition V)
    {f : Euc 2 →ₗ[ℝ] ℝ} {e o : Euc 2} (he : e ≠ 0) (hfe : 0 < f e)
    (hf : ∀ q ∈ V, q ≠ o → 0 < f (q - o)) (ho : o ∈ V)
    {i i' j j' : Fin N}
    (hpi : p i ∈ V) (hpi' : p i' ∈ V) (hpj : p j ∈ V) (hpj' : p j' ∈ V)
    (hio : o ≠ p i) (hio' : o ≠ p i') (hjo : o ≠ p j) (hjo' : o ≠ p j')
    (hii'p : p i ≠ p i') (hijp : p i ≠ p j) (hij'p : p i ≠ p j')
    (hi'jp : p i' ≠ p j) (hi'j'p : p i' ≠ p j') (hjj'p : p j ≠ p j')
    (hord : (cr2 e (p i - o) / f (p i - o) < cr2 e (p i' - o) / f (p i' - o) ∧
             cr2 e (p i' - o) / f (p i' - o) < cr2 e (p j - o) / f (p j - o) ∧
             cr2 e (p j - o) / f (p j - o) < cr2 e (p j' - o) / f (p j' - o)) ∨
            (cr2 e (p j' - o) / f (p j' - o) < cr2 e (p j - o) / f (p j - o) ∧
             cr2 e (p j - o) / f (p j - o) < cr2 e (p i' - o) / f (p i' - o) ∧
             cr2 e (p i' - o) / f (p i' - o) < cr2 e (p i - o) / f (p i - o))) :
    ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      (1 - s) • p i + s • p j = (1 - t) • p i' + t • p j' := by
  have e1 : ∀ (u v : Euc 2) (r : ℝ), u + r • (v - u) = (1 - r) • u + r • v := by
    intro u v r
    rw [smul_sub, sub_smul, one_smul]
    abel
  rcases hord with ⟨hσ1, hσ2, hσ3⟩ | ⟨hσ1, hσ2, hσ3⟩
  · obtain ⟨s, t, hs0, hs1, ht0, ht1, hcross⟩ :=
      chord_cross hV he hfe hf ho hpi hpi' hpj hpj'
        hio hio' hjo hjo' hii'p hijp hij'p hi'jp hi'j'p hjj'p hσ1 hσ2 hσ3
    refine ⟨s, t, hs0, hs1, ht0, ht1, ?_⟩
    rw [← e1 (p i) (p j) s, ← e1 (p i') (p j') t]
    exact hcross
  · obtain ⟨s, t, hs0, hs1, ht0, ht1, hcross⟩ :=
      chord_cross hV he hfe hf ho hpj' hpj hpi' hpi
        hjo' hjo hio' hio (Ne.symm hjj'p) (Ne.symm hi'j'p) (Ne.symm hij'p)
        (Ne.symm hi'jp) (Ne.symm hijp) (Ne.symm hii'p) hσ1 hσ2 hσ3
    rw [e1, e1] at hcross
    refine ⟨1 - t, 1 - s, sub_pos.mpr ht1, sub_lt_self _ ht0,
      sub_pos.mpr hs1, sub_lt_self _ hs0, ?_⟩
    have h1 : (1 : ℝ) - (1 - t) = t := sub_sub_self 1 t
    have h2 : (1 : ℝ) - (1 - s) = s := sub_sub_self 1 s
    rw [h1, h2, add_comm (t • p i) ((1 - t) • p j),
      add_comm (s • p i') ((1 - s) • p j')]
    exact hcross.symm

/-- A projected crossing of the chords of `x` lifts to an `AboveSeg` or
`BelowSeg` between the lifted segments. -/
private lemma tuple_above_or_below {N : ℕ} {x : Fin N → Euc 3}
    {i i' j j' : Fin N} (hii' : i < i') (hi'j : i' < j) (hjj' : j < j')
    (hAI : AffineIndependent ℝ
      (fun a : ↥({i, i', j, j'} : Finset (Fin N)) ↦ x (a : Fin N)))
    {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (h : (1 - s) • proj2 (x i) + s • proj2 (x j) =
      (1 - t) • proj2 (x i') + t • proj2 (x j')) :
    AboveSeg (x i) (x j) (x i') (x j') ∨ BelowSeg (x i) (x j) (x i') (x j') := by
  have hproj : proj2 ((1 - s) • x i + s • x j) =
      proj2 ((1 - t) • x i' + t • x j') := by
    rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
    exact h
  have hz := z_ne_of_proj_cross hii' hi'j hjj' hAI ht1 hproj
  rcases lt_or_gt_of_ne hz with hlt | hgt
  · exact Or.inr ⟨s, t, hs0, hs1, ht0, ht1, hproj, hlt⟩
  · exact Or.inl ⟨s, t, hs0, hs1, ht0, ht1, hproj, hgt⟩

/-- Swapping the roles of the two segments turns `BelowSeg` into
`AboveSeg`. -/
private lemma belowSeg_iff {a c b d : Euc 3} :
    BelowSeg a c b d ↔ AboveSeg b d a c := by
  constructor
  · rintro ⟨s, t, hs0, hs1, ht0, ht1, hproj, hz⟩
    exact ⟨t, s, ht0, ht1, hs0, hs1, hproj.symm, hz⟩
  · rintro ⟨s, t, hs0, hs1, ht0, ht1, hproj, hz⟩
    exact ⟨t, s, ht0, ht1, hs0, hs1, hproj.symm, hz⟩

/-- The sorted list of a four-element `Fin N` finset. -/
private lemma sort_four {N : ℕ} {a b c d : Fin N} (hab : a < b) (hbc : b < c)
    (hcd : c < d) :
    ({a, b, c, d} : Finset (Fin N)).sort (· ≤ ·) = [a, b, c, d] := by
  rw [show ({a, b, c, d} : Finset (Fin N)) = insert a {b, c, d} from rfl]
  rw [Finset.sort_insert (· ≤ ·)
    (fun y hy ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hab.le
      · exact (lt_trans hab hbc).le
      · exact (lt_trans hab (lt_trans hbc hcd)).le)
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hab.ne, (lt_trans hab hbc).ne,
        (lt_trans hab (lt_trans hbc hcd)).ne⟩)]
  rw [show ({b, c, d} : Finset (Fin N)) = insert b {c, d} from rfl]
  rw [Finset.sort_insert (· ≤ ·)
    (fun y hy ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hbc.le
      · exact (lt_trans hbc hcd).le)
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hbc.ne, (lt_trans hbc hcd).ne⟩)]
  rw [show ({c, d} : Finset (Fin N)) = insert c {d} from rfl]
  rw [Finset.sort_insert (· ≤ ·)
    (fun y hy ↦ by
      simp only [Finset.mem_singleton] at hy
      rw [hy]
      exact hcd.le)
    (by
      simp only [Finset.mem_singleton]
      exact hcd.ne)]
  rw [Finset.sort_singleton]

/-- A strictly increasing quadruple drawn from `{i, i', j, j'}` must be
`(i, i', j, j')` itself. -/
private lemma quad_eq {N : ℕ} {a b c d i i' j j' : Fin N}
    (h1 : i < i') (h2 : i' < j) (h3 : j < j')
    (ha : a ∈ ({i, i', j, j'} : Finset (Fin N)))
    (hb : b ∈ ({i, i', j, j'} : Finset (Fin N)))
    (hc : c ∈ ({i, i', j, j'} : Finset (Fin N)))
    (hd : d ∈ ({i, i', j, j'} : Finset (Fin N)))
    (g1 : a < b) (g2 : b < c) (g3 : c < d) :
    i = a ∧ i' = b ∧ j = c ∧ j' = d := by
  have hsub : ({a, b, c, d} : Finset (Fin N)) ⊆ {i, i', j, j'} := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> assumption
  have heq : ({a, b, c, d} : Finset (Fin N)) = {i, i', j, j'} :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [card_four h1 h2 h3, card_four g1 g2 g3])
  have hs1 := sort_four g1 g2 g3
  rw [heq, sort_four h1 h2 h3] at hs1
  simp only [List.cons.injEq, and_true] at hs1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs1
  exact ⟨rfl, rfl, rfl, rfl⟩


/-! ### Chord separation for cyclic arcs

When one of the index blocks in `cor_2_4` is empty, `prop_2_3` does not
apply directly.  In that case the two index sets form a contiguous cyclic
arc of the projected polygon together with its complement, and the chord
joining the two arc endpoints separates the corresponding convex hulls.
The essential fact, extracted from the strict crossings produced by
`aboveBelow_ramsey`, is that the sign of `crs (v i) (v j) (v l)` is constant
over increasing index triples `i < j < l`. -/

/-- Cyclic rotation symmetry of `crs`. -/
private lemma crs_rotate (u v w : Euc 2) : crs u v w = crs w u v := by
  rw [crs_eq_cycle, crs_eq_cycle]
  ring

/-- `crs` vanishes when the first and third arguments agree. -/
private lemma crs_self_right (u v : Euc 2) : crs u v u = 0 := by
  simp only [crs, sub_self, cr2_zero_right]

/-- `crs` vanishes when the second and third arguments agree. -/
private lemma crs_self_end (u v : Euc 2) : crs u v v = 0 := cr2_self _

/-- `crs` is affine in its third argument along a segment. -/
private lemma crs_affine_right (u v x y : Euc 2) (t : ℝ) :
    crs u v ((1 - t) • x + t • y) = (1 - t) * crs u v x + t * crs u v y := by
  have heq : (1 - t) • x + t • y - u = (1 - t) • (x - u) + t • (y - u) := by
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  simp only [crs, heq, cr2_add_right, cr2_smul_right]

/-- Multiplicative transitivity of same-sign products. -/
private lemma sign_trans {A B C : ℝ} (h1 : 0 < A * B) (h2 : 0 < B * C) :
    0 < A * C := by
  have h3 : 0 < (A * C) * (B * B) := by
    have e : (A * C) * (B * B) = (A * B) * (B * C) := by ring
    rw [e]
    exact mul_pos h1 h2
  exact pos_of_mul_pos_left h3 (mul_self_nonneg B)

/-- A variant of `sign_trans` with the shared factor on the right. -/
private lemma sign_trans' {A B C : ℝ} (h1 : 0 < A * C) (h2 : 0 < B * C) :
    0 < A * B :=
  sign_trans h1 (by rw [mul_comm]; exact h2)

/-- The linear functional `w ↦ cr2 u w`. -/
private def cr2Lin (u : Euc 2) : Euc 2 →ₗ[ℝ] ℝ where
  toFun w := cr2 u w
  map_add' x y := cr2_add_right u x y
  map_smul' c x := cr2_smul_right c u x

/-- Evaluation of `cr2Lin`. -/
private lemma cr2Lin_apply (u w : Euc 2) : cr2Lin u w = cr2 u w := rfl

/-- Convex position is inherited by subsets. -/
private lemma inConvexPosition_subset {S T : Finset (Euc 2)}
    (hT : InConvexPosition T) (hST : S ⊆ T) : InConvexPosition S := by
  intro x hx hmem
  exact hT x (hST hx) (convexHull_mono
    (Finset.coe_subset.2 (Finset.erase_subset_erase x hST)) hmem)

/-- The sign relations forced by one strict chord crossing: if the chords
`[v_w, v_y]` and `[v_x, v_z]` cross (with `w < x < y < z`), then the products
`crs(w,x,y)·crs(w,y,z)`, `crs(w,x,z)·crs(x,y,z)` and `crs(w,x,y)·crs(x,y,z)`
are all positive. -/
private lemma crs_quad_rels {m : ℕ} {v : Fin m → Euc 2}
    (hv : Function.Injective v)
    (hconv : InConvexPosition (Finset.image v Finset.univ))
    (hcross : ∀ i i' j j' : Fin m, i < i' → i' < j → j < j' →
      ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
        (1 - s) • v i + s • v j = (1 - t) • v i' + t • v j')
    {w x y z : Fin m} (hwx : w < x) (hxy : x < y) (hyz : y < z) :
    0 < crs (v w) (v x) (v y) * crs (v w) (v y) (v z) ∧
    0 < crs (v w) (v x) (v z) * crs (v x) (v y) (v z) ∧
    0 < crs (v w) (v x) (v y) * crs (v x) (v y) (v z) := by
  have hVmem : ∀ i : Fin m, v i ∈ Finset.image v Finset.univ :=
    fun i ↦ Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  have hcrs : ∀ {i j l : Fin m}, i ≠ j → j ≠ l → i ≠ l →
      crs (v i) (v j) (v l) ≠ 0 :=
    fun hij hjl hil ↦ crs_ne_zero_of_convex hconv (hVmem _) (hVmem _) (hVmem _)
      (hv.ne hij) (hv.ne hjl) (hv.ne hil)
  obtain ⟨α, β, hα0, hα1, hβ0, hβ1, hz⟩ := hcross w x y z hwx hxy hyz
  have hα1' : (0 : ℝ) < 1 - α := sub_pos.mpr hα1
  have hβ1' : (0 : ℝ) < 1 - β := sub_pos.mpr hβ1
  -- evaluate the oriented-area functional at the crossing point on each chord
  have hwy : (1 - β) * crs (v w) (v y) (v x) + β * crs (v w) (v y) (v z) = 0 := by
    have e1 := congrArg (fun u ↦ crs (v w) (v y) u) hz
    simp only [crs_affine_right, crs_self_right, crs_self_end, mul_zero,
      add_zero, zero_add] at e1
    exact e1.symm
  have hxz : (1 - α) * crs (v x) (v z) (v w) + α * crs (v x) (v z) (v y) = 0 := by
    have e1 := congrArg (fun u ↦ crs (v x) (v z) u) hz
    simp only [crs_affine_right, crs_self_right, crs_self_end, mul_zero,
      add_zero, zero_add] at e1
    exact e1
  have hxy_eq : (1 - α) * crs (v x) (v y) (v w) = β * crs (v x) (v y) (v z) := by
    have e1 := congrArg (fun u ↦ crs (v x) (v y) u) hz
    simp only [crs_affine_right, crs_self_right, crs_self_end, mul_zero,
      add_zero, zero_add] at e1
    exact e1
  -- the `(w,y)`-line separates `x` from `z`
  have hA : crs (v w) (v y) (v x) ≠ 0 :=
    hcrs (ne_of_lt (hwx.trans hxy)) (ne_of_gt hxy) (ne_of_lt hwx)
  have hB : crs (v w) (v y) (v z) ≠ 0 :=
    hcrs (ne_of_lt (hwx.trans hxy)) (ne_of_lt hyz)
      (ne_of_lt (hwx.trans (hxy.trans hyz)))
  have hAB : crs (v w) (v y) (v x) * crs (v w) (v y) (v z) < 0 := by
    have key : (1 - β) * (crs (v w) (v y) (v x) * crs (v w) (v y) (v z)) =
        -β * (crs (v w) (v y) (v z) * crs (v w) (v y) (v z)) := by
      linear_combination crs (v w) (v y) (v z) * hwy
    have hneg : (1 - β) * (crs (v w) (v y) (v x) * crs (v w) (v y) (v z)) < 0 := by
      rw [key]
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hβ0) (mul_self_pos.mpr hB)
    exact neg_of_mul_neg_right hneg hβ1'.le
  have hR1 : 0 < crs (v w) (v x) (v y) * crs (v w) (v y) (v z) := by
    rw [crs_anticomm_mid (v w) (v x) (v y), neg_mul]
    exact neg_pos.mpr hAB
  -- the `(x,z)`-line separates `w` from `y`
  have hA' : crs (v x) (v z) (v w) ≠ 0 :=
    hcrs (ne_of_lt (hxy.trans hyz)) (ne_of_gt (hwx.trans (hxy.trans hyz)))
      (ne_of_gt hwx)
  have hB' : crs (v x) (v z) (v y) ≠ 0 :=
    hcrs (ne_of_lt (hxy.trans hyz)) (ne_of_gt hyz) (ne_of_lt hxy)
  have hAB' : crs (v x) (v z) (v w) * crs (v x) (v z) (v y) < 0 := by
    have key : α * (crs (v x) (v z) (v w) * crs (v x) (v z) (v y)) =
        -(1 - α) * (crs (v x) (v z) (v w) * crs (v x) (v z) (v w)) := by
      linear_combination crs (v x) (v z) (v w) * hxz
    have hneg : α * (crs (v x) (v z) (v w) * crs (v x) (v z) (v y)) < 0 := by
      rw [key]
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hα1') (mul_self_pos.mpr hA')
    exact neg_of_mul_neg_right hneg hα0.le
  have hR2 : 0 < crs (v w) (v x) (v z) * crs (v x) (v y) (v z) := by
    have e1 : crs (v x) (v z) (v w) = crs (v w) (v x) (v z) := crs_rotate _ _ _
    have e2 : crs (v x) (v z) (v y) = -crs (v x) (v y) (v z) :=
      crs_anticomm_mid _ _ _
    rw [e1, e2, mul_neg] at hAB'
    exact neg_lt_zero.mp hAB'
  -- the `(x,y)`-line has `w` and `z` on the same side
  have hR3 : 0 < crs (v w) (v x) (v y) * crs (v x) (v y) (v z) := by
    have e3 : crs (v x) (v y) (v w) = crs (v w) (v x) (v y) := crs_rotate _ _ _
    rw [e3] at hxy_eq
    have hC1 : crs (v w) (v x) (v y) ≠ 0 :=
      hcrs (ne_of_lt hwx) (ne_of_lt hxy) (ne_of_lt (hwx.trans hxy))
    have key : (1 - α) * (crs (v w) (v x) (v y) * crs (v w) (v x) (v y)) =
        β * (crs (v w) (v x) (v y) * crs (v x) (v y) (v z)) := by
      linear_combination crs (v w) (v x) (v y) * hxy_eq
    have hpos : 0 < β * (crs (v w) (v x) (v y) * crs (v x) (v y) (v z)) := by
      rw [← key]
      exact mul_pos hα1' (mul_self_pos.mpr hC1)
    exact pos_of_mul_pos_right hpos hβ0.le
  exact ⟨hR1, hR2, hR3⟩

/-- The oriented-area functional `crs (v r) (v s) ⬝` along the chord
`[v_r, v_s]` (with `r < s`) has a constant nonzero sign on the vertices `v_i`
with `i < r` or `s < i` (outside the arc) and the opposite nonzero sign on
the arc's interior vertices. -/
private lemma arc_chord_sign {m : ℕ} {v : Fin m → Euc 2}
    (hv : Function.Injective v)
    (hconv : InConvexPosition (Finset.image v Finset.univ))
    (hcross : ∀ i i' j j' : Fin m, i < i' → i' < j → j < j' →
      ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
        (1 - s) • v i + s • v j = (1 - t) • v i' + t • v j')
    {r s : Fin m} (hrs : r < s) :
    ∃ E : ℝ, E ≠ 0 ∧
      (∀ i : Fin m, r < i → i < s → crs (v r) (v s) (v i) * E < 0) ∧
      (∀ i : Fin m, (i < r ∨ s < i) → 0 < crs (v r) (v s) (v i) * E) := by
  have hVmem : ∀ i : Fin m, v i ∈ Finset.image v Finset.univ :=
    fun i ↦ Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  have hcrs : ∀ {i j l : Fin m}, i ≠ j → j ≠ l → i ≠ l →
      crs (v i) (v j) (v l) ≠ 0 :=
    fun hij hjl hil ↦ crs_ne_zero_of_convex hconv (hVmem _) (hVmem _) (hVmem _)
      (hv.ne hij) (hv.ne hjl) (hv.ne hil)
  by_cases htop : ∃ j : Fin m, s < j
  · -- `s` is not the last index: take `j₀ > s` as the reference vertex
    obtain ⟨j₀, hj₀⟩ := htop
    have hE : crs (v r) (v s) (v j₀) ≠ 0 :=
      hcrs hrs.ne (ne_of_lt hj₀) (ne_of_lt (hrs.trans hj₀))
    refine ⟨crs (v r) (v s) (v j₀), hE, ?_, ?_⟩
    · intro i hir his
      have h1 := (crs_quad_rels hv hconv hcross hir his hj₀).1
      rw [crs_anticomm_mid (v r) (v s) (v i), neg_mul, neg_lt_zero]
      exact h1
    · intro i hi
      rcases hi with hir | his
      · have h3 := (crs_quad_rels hv hconv hcross hir hrs hj₀).2.2
        rw [crs_rotate (v r) (v s) (v i)]
        exact h3
      · rcases lt_trichotomy i j₀ with hlt | heq | hgt
        · obtain ⟨-, h2, h3⟩ := crs_quad_rels hv hconv hcross hrs his hlt
          exact sign_trans' h3 h2
        · subst heq
          exact mul_self_pos.mpr hE
        · obtain ⟨-, h2, h3⟩ := crs_quad_rels hv hconv hcross hrs hj₀ hgt
          exact sign_trans' h2 h3
  · by_cases hbot : ∃ j : Fin m, j < r
    · -- `r` is not the first index: take `j₀ < r` as the reference vertex
      obtain ⟨j₀, hj₀⟩ := hbot
      have hE : crs (v r) (v s) (v j₀) ≠ 0 :=
        hcrs hrs.ne (ne_of_gt (hj₀.trans hrs)) (ne_of_gt hj₀)
      refine ⟨crs (v r) (v s) (v j₀), hE, ?_, ?_⟩
      · intro i hir his
        have h2 := (crs_quad_rels hv hconv hcross hj₀ hir his).2.1
        rw [crs_anticomm_mid (v r) (v s) (v i), neg_mul, neg_lt_zero,
          crs_rotate (v r) (v s) (v j₀), mul_comm]
        exact h2
      · intro i hi
        rcases hi with hir | his
        · rcases lt_trichotomy i j₀ with hlt | heq | hgt
          · obtain ⟨h1, -, h3⟩ := crs_quad_rels hv hconv hcross hlt hj₀ hrs
            have hs' : 0 < crs (v i) (v r) (v s) * crs (v j₀) (v r) (v s) :=
              sign_trans' (by rw [mul_comm]; exact h1)
                (by rw [mul_comm]; exact h3)
            rw [crs_rotate (v r) (v s) (v i), crs_rotate (v r) (v s) (v j₀)]
            exact hs'
          · subst heq
            exact mul_self_pos.mpr hE
          · obtain ⟨h1, -, h3⟩ := crs_quad_rels hv hconv hcross hgt hir hrs
            have hs' : 0 < crs (v i) (v r) (v s) * crs (v j₀) (v r) (v s) :=
              sign_trans' (by rw [mul_comm]; exact h3)
                (by rw [mul_comm]; exact h1)
            rw [crs_rotate (v r) (v s) (v i), crs_rotate (v r) (v s) (v j₀)]
            exact hs'
        · exact absurd ⟨i, his⟩ htop
    · -- `r` is first and `s` is last: only interior vertices need to be checked
      by_cases hint : ∃ i : Fin m, r < i ∧ i < s
      · obtain ⟨i₁, hi₁r, hi₁s⟩ := hint
        have hE : crs (v r) (v s) (v i₁) ≠ 0 :=
          hcrs hrs.ne (ne_of_gt hi₁s) (ne_of_lt hi₁r)
        refine ⟨-crs (v r) (v s) (v i₁), neg_ne_zero.mpr hE, ?_, ?_⟩
        · intro i hir his
          rw [mul_neg, neg_lt_zero, crs_anticomm_mid (v r) (v s) (v i),
            crs_anticomm_mid (v r) (v s) (v i₁), neg_mul_neg]
          rcases lt_trichotomy i i₁ with hlt | heq | hgt
          · obtain ⟨h1, h2, h3⟩ := crs_quad_rels hv hconv hcross hir hlt hi₁s
            have h13 : 0 < crs (v r) (v i₁) (v s) * crs (v i) (v i₁) (v s) :=
              sign_trans' (by rw [mul_comm]; exact h1)
                (by rw [mul_comm]; exact h3)
            exact sign_trans' h2 h13
          · subst heq
            exact mul_self_pos.mpr (hcrs (ne_of_lt hi₁r) (ne_of_lt hi₁s) hrs.ne)
          · obtain ⟨h1, h2, h3⟩ := crs_quad_rels hv hconv hcross hi₁r hgt his
            have h13 : 0 < crs (v r) (v i) (v s) * crs (v i₁) (v i) (v s) :=
              sign_trans' (by rw [mul_comm]; exact h1)
                (by rw [mul_comm]; exact h3)
            exact sign_trans' h13 h2
        · intro i hi
          rcases hi with hir | his
          · exact absurd ⟨i, hir⟩ hbot
          · exact absurd ⟨i, his⟩ htop
      · -- the arc is the whole polygon with no interior vertex either
        refine ⟨1, one_ne_zero, ?_, ?_⟩
        · intro i hir his
          exact absurd ⟨i, hir, his⟩ hint
        · intro i hi
          rcases hi with hir | his
          · exact absurd ⟨i, hir⟩ hbot
          · exact absurd ⟨i, his⟩ htop

/-- In a cyclically ordered configuration in convex position, the convex
hull of the vertices of a closed index interval `[r, s]` is disjoint from the
convex hull of the remaining vertices. -/
private lemma hull_arc_disjoint {m : ℕ} {v : Fin m → Euc 2}
    (hv : Function.Injective v)
    (hconv : InConvexPosition (Finset.image v Finset.univ))
    (hcross : ∀ i i' j j' : Fin m, i < i' → i' < j → j < j' →
      ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
        (1 - s) • v i + s • v j = (1 - t) • v i' + t • v j')
    {r s : Fin m} (hrs : r ≤ s) :
    Disjoint
      (convexHull ℝ ((Finset.image v
        (Finset.univ.filter fun i ↦ r ≤ i ∧ i ≤ s)) : Set (Euc 2)))
      (convexHull ℝ ((Finset.image v
        (Finset.univ.filter fun i ↦ i < r ∨ s < i)) : Set (Euc 2))) := by
  classical
  rcases eq_or_lt_of_le hrs with h | hrs
  · -- `r = s`: the arc is the single vertex `v_r`, use convex position
    rw [← h]
    have hA : Finset.univ.filter (fun i : Fin m ↦ r ≤ i ∧ i ≤ r) = {r} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      exact ⟨fun h ↦ le_antisymm h.2 h.1, fun h ↦ ⟨h.ge, h.le⟩⟩
    have hB : Finset.univ.filter (fun i : Fin m ↦ i < r ∨ r < i) =
        Finset.univ.erase r := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        and_true]
      exact ⟨fun h ↦ h.elim ne_of_lt ne_of_gt, fun h ↦ lt_or_gt_of_ne h⟩
    rw [hA, Finset.image_singleton, Finset.coe_singleton, convexHull_singleton,
      hB, Finset.image_erase hv]
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rw [Set.mem_singleton_iff] at hz1
    subst hz1
    exact hconv (v r) (Finset.mem_image.2 ⟨r, Finset.mem_univ r, rfl⟩) hz2
  · obtain ⟨E, hE, hint, hext⟩ := arc_chord_sign hv hconv hcross hrs
    -- separating functional: `G w = E · cr2 (v s - v r) w`
    set G : Euc 2 →ₗ[ℝ] ℝ := E • cr2Lin (v s - v r) with hGdef
    set C := G (v r) with hCdef
    have hGeval : ∀ w : Euc 2, G w = E * cr2 (v s - v r) w := by
      intro w
      simp only [hGdef, LinearMap.smul_apply, smul_eq_mul, cr2Lin_apply]
    have hGrel : ∀ w : Euc 2, G w - G (v r) = E * crs (v r) (v s) w := by
      intro w
      rw [hGeval, hGeval]
      simp only [crs]
      rw [← mul_sub, ← cr2_sub_right]
    have hsubA : convexHull ℝ ((Finset.image v
          (Finset.univ.filter fun i : Fin m ↦ r ≤ i ∧ i ≤ s)) : Set (Euc 2)) ⊆
        G ⁻¹' Set.Iic C := by
      refine convexHull_min ?_ ((convex_Iic C).linear_preimage G)
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
      have hiA := Finset.mem_filter.1 hi
      show G (v i) ≤ C
      rcases eq_or_lt_of_le hiA.2.1 with h | h1
      · rw [← h, hCdef]
      rcases eq_or_lt_of_le hiA.2.2 with h | h2
      · rw [h, hCdef]
        have hz : G (v s) - G (v r) = 0 := by
          rw [hGrel, crs_self_end, mul_zero]
        linarith
      · have hz : G (v i) - G (v r) < 0 := by
          rw [hGrel, mul_comm]
          exact hint i h1 h2
        rw [hCdef]
        linarith
    have hsubB : convexHull ℝ ((Finset.image v
          (Finset.univ.filter fun i : Fin m ↦ i < r ∨ s < i)) : Set (Euc 2)) ⊆
        G ⁻¹' Set.Ioi C := by
      refine convexHull_min ?_ ((convex_Ioi C).linear_preimage G)
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
      have hiB := Finset.mem_filter.1 hi
      show C < G (v i)
      have hz : 0 < G (v i) - G (v r) := by
        rw [hGrel, mul_comm]
        exact hext i hiB.2
      rw [hCdef]
      linarith
    rw [Set.disjoint_left]
    intro z hzA hzB
    have h1 := hsubA hzA
    have h2 := hsubB hzB
    rw [Set.mem_preimage, Set.mem_Iic] at h1
    rw [Set.mem_preimage, Set.mem_Ioi] at h2
    linarith

/-- Disjointness of the projected (`Euc 2`) convex hulls implies disjointness
of the original (`Euc 3`) hulls, via the linear map `proj2`. -/
private lemma disjoint_hull_proj2 {A B : Finset (Euc 3)}
    (h : Disjoint (convexHull ℝ ((A.image proj2 : Finset (Euc 2)) : Set (Euc 2)))
      (convexHull ℝ ((B.image proj2 : Finset (Euc 2)) : Set (Euc 2)))) :
    Disjoint (convexHull ℝ (A : Set (Euc 3)))
      (convexHull ℝ (B : Set (Euc 3))) := by
  rw [Set.disjoint_left] at h ⊢
  intro z hzA hzB
  have hmem : ∀ {F : Finset (Euc 3)}, z ∈ convexHull ℝ (F : Set (Euc 3)) →
      proj2 z ∈ convexHull ℝ
        ((F.image proj2 : Finset (Euc 2)) : Set (Euc 2)) := by
    intro F hzF
    have e : ((F.image proj2 : Finset (Euc 2)) : Set (Euc 2)) =
        proj2 '' (F : Set (Euc 3)) := Finset.coe_image
    rw [e, ← LinearMap.image_convexHull]
    exact ⟨z, hzF, rfl⟩
  exact h (hmem hzA) (hmem hzB)


/-- **Proposition 2.2.**  For `k ≥ 4` there is `AB(k)` such that any `N ≥ AB(k)`
points `x₁,…,x_N` of `ℝ³` in general position, whose projections are the
vertices of a convex polygon, contain a `k`-element index set `S` on which
every crossing pair `i < i' < j < j'` has `xᵢxⱼ` above `xᵢ'xⱼ'`, or below.

A 2-colouring of index pairs by agreement with the polygon's cyclic order
(mediated by the slope `σ`) makes the index order uniform with respect to
`σ` on a large subset; a second Ramsey application on 4-subsets coloured by
`AboveSeg`/`BelowSeg` then yields the monochromatic set. -/
theorem aboveBelow_ramsey {k : ℕ} (hk : 4 ≤ k) :
    ∃ AB : ℕ, ∀ N : ℕ, AB ≤ N → ∀ x : Fin N → Euc 3,
      Function.Injective x →
      InGeneralPosition ((Finset.image x Finset.univ : Finset (Euc 3)) : Set (Euc 3)) →
      Function.Injective (proj2 ∘ x) →
      InConvexPosition (Finset.image (proj2 ∘ x) Finset.univ) →
      ∃ S : Finset (Fin N), S.card = k ∧
        ((∀ i i' j j' : Fin N, i ∈ S → i' ∈ S → j ∈ S → j' ∈ S →
            i < i' → i' < j → j < j' → AboveSeg (x i) (x j) (x i') (x j')) ∨
         (∀ i i' j j' : Fin N, i ∈ S → i' ∈ S → j ∈ S → j' ∈ S →
            i < i' → i' < j → j < j' → BelowSeg (x i) (x j) (x i') (x j'))) := by
  classical
  obtain ⟨M₁, hM₁⟩ := ramsey_mono 4 2 (by norm_num) k
  obtain ⟨N₂, hN₂⟩ := ramsey_mono 2 2 (by norm_num) M₁
  refine ⟨N₂ + 1, ?_⟩
  intro N hN x hx hgp hπ hconv
  -- `M₁` and `N₂` are genuine Ramsey bounds, hence at least the target sizes.
  have hM₁k : k ≤ M₁ := by
    have hcard : (Finset.univ : Finset (Fin M₁)).card = M₁ := by simp
    obtain ⟨S, -, hS1, -⟩ := hM₁ (Finset.univ : Finset (Fin M₁))
      (le_of_eq hcard.symm) (fun _ : Finset (Fin M₁) ↦ (0 : Fin 2))
    calc k = S.card := hS1.symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ S)
      _ = M₁ := hcard
  have hN₂M₁ : M₁ ≤ N₂ := by
    have hcard : (Finset.univ : Finset (Fin N₂)).card = N₂ := by simp
    obtain ⟨S, -, hS1, -⟩ := hN₂ (Finset.univ : Finset (Fin N₂))
      (le_of_eq hcard.symm) (fun _ : Finset (Fin N₂) ↦ (0 : Fin 2))
    calc M₁ = S.card := hS1.symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ S)
      _ = N₂ := hcard
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  -- geometry setup: vertex set, separating functional, slope `σ`
  set V : Finset (Euc 2) := Finset.image (proj2 ∘ x) Finset.univ with hVdef
  have hVmem : ∀ i : Fin N, (proj2 ∘ x) i ∈ V := fun i ↦
    Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  set i₀ : Fin N := ⟨0, hN0⟩ with hi₀def
  set i₁ : Fin N := ⟨1, hN1⟩ with hi₁def
  set o : Euc 2 := (proj2 ∘ x) i₀ with hodef
  have ho : o ∈ V := hVmem i₀
  obtain ⟨f, hf⟩ := exists_sep hconv ho
  have hi₁ne : i₁ ≠ i₀ := by
    rw [hi₁def, hi₀def]
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  have hpo₁ : (proj2 ∘ x) i₁ ≠ o := hπ.ne hi₁ne
  set e : Euc 2 := (proj2 ∘ x) i₁ - o with hedef
  have he : e ≠ 0 := sub_ne_zero.mpr hpo₁
  have hfe : 0 < f e := hf _ (hVmem i₁) hpo₁
  set σ : Fin N → ℝ :=
    fun i ↦ cr2 e ((proj2 ∘ x) i - o) / f ((proj2 ∘ x) i - o) with hσdef
  -- pair colouring: does the index order agree with the σ-order?
  set χ₂ : Finset (Fin N) → Fin 2 :=
    fun P ↦ if (∀ a ∈ P, ∀ b ∈ P, a < b → σ a < σ b) then (0 : Fin 2) else 1
    with hχ₂def
  have hcard₁ : N₂ ≤ (Finset.univ.erase i₀).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨S₁, hS₁sub, hS₁card, col₂, hcol₂⟩ :=
    hN₂ (Finset.univ.erase i₀) hcard₁ χ₂
  have hS₁o : ∀ a ∈ S₁, (proj2 ∘ x) a ≠ o := fun a ha ↦
    hπ.ne (Finset.mem_erase.1 (hS₁sub ha)).1
  have hS₁p : ∀ a b : Fin N, a ∈ S₁ → b ∈ S₁ → a ≠ b →
      (proj2 ∘ x) a ≠ (proj2 ∘ x) b := fun a b _ _ hab ↦ hπ.ne hab
  have hσinj : ∀ {a b : Fin N}, a ∈ S₁ → b ∈ S₁ → a ≠ b → σ a ≠ σ b := by
    intro a b ha hb hab
    exact sigma_ne hconv he hfe hf ho (hVmem a) (hVmem b)
      (hS₁o a ha).symm (hS₁o b hb).symm (hS₁p a b ha hb hab)
  have hcol₂cases : col₂ = 0 ∨ col₂ = 1 := by
    have hv : col₂.val < 2 := col₂.isLt
    rcases (by omega : col₂.val = 0 ∨ col₂.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hσmono : (∀ a b : Fin N, a ∈ S₁ → b ∈ S₁ → a < b → σ a < σ b) ∨
      (∀ a b : Fin N, a ∈ S₁ → b ∈ S₁ → a < b → σ b < σ a) := by
    rcases hcol₂cases with h0 | h0
    · refine Or.inl fun a b ha hb hab ↦ ?_
      have hTsub : ({a, b} : Finset (Fin N)) ⊆ S₁ := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption
      have hχ := hcol₂ {a, b} hTsub (Finset.card_pair hab.ne)
      rw [h0] at hχ
      simp only [hχ₂def] at hχ
      split_ifs at hχ with hcond
      · exact hcond a (by simp) b (by simp) hab
      · exact absurd hχ (by decide)
    · refine Or.inr fun a b ha hb hab ↦ ?_
      have hTsub : ({a, b} : Finset (Fin N)) ⊆ S₁ := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption
      have hχ := hcol₂ {a, b} hTsub (Finset.card_pair hab.ne)
      rw [h0] at hχ
      simp only [hχ₂def] at hχ
      split_ifs at hχ with hcond
      · exact absurd hχ (by decide)
      · push_neg at hcond
        obtain ⟨u, hu, v, hv, huv, huvσ⟩ := hcond
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact absurd huv (lt_irrefl _)
        · exact lt_of_le_of_ne huvσ (hσinj hb ha (Ne.symm hab.ne))
        · exact absurd huv (lt_asymm hab)
        · exact absurd huv (lt_irrefl _)
  -- every ordered quadruple of `S₁` gives a crossing
  have hcross : ∀ i i' j j' : Fin N, i ∈ S₁ → i' ∈ S₁ → j ∈ S₁ → j' ∈ S₁ →
      i < i' → i' < j → j < j' →
      ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
        (1 - s) • (proj2 ∘ x) i + s • (proj2 ∘ x) j =
          (1 - t) • (proj2 ∘ x) i' + t • (proj2 ∘ x) j' := by
    intro i i' j j' hi hi' hj hj' hii' hi'j hjj'
    have hord : (σ i < σ i' ∧ σ i' < σ j ∧ σ j < σ j') ∨
        (σ j' < σ j ∧ σ j < σ i' ∧ σ i' < σ i) := by
      rcases hσmono with hm | hm
      · exact Or.inl ⟨hm i i' hi hi' hii', hm i' j hi' hj hi'j,
          hm j j' hj hj' hjj'⟩
      · exact Or.inr ⟨hm j j' hj hj' hjj', hm i' j hi' hj hi'j,
          hm i i' hi hi' hii'⟩
    exact tuple_cross hconv he hfe hf ho (hVmem i) (hVmem i') (hVmem j)
      (hVmem j') (hS₁o i hi).symm (hS₁o i' hi').symm (hS₁o j hj).symm
      (hS₁o j' hj').symm
      (hS₁p i i' hi hi' hii'.ne) (hS₁p i j hi hj (lt_trans hii' hi'j).ne)
      (hS₁p i j' hi hj' (lt_trans hii' (lt_trans hi'j hjj')).ne)
      (hS₁p i' j hi' hj hi'j.ne)
      (hS₁p i' j' hi' hj' (lt_trans hi'j hjj').ne)
      (hS₁p j j' hj hj' hjj'.ne) hord
  -- the 4-subset colouring, homogeneous on a `k`-set `S₂ ⊆ S₁`
  set χ₄ : Finset (Fin N) → Fin 2 :=
    fun T ↦ if (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
        a < b → b < c → c < d → AboveSeg (x a) (x c) (x b) (x d))
      then (0 : Fin 2) else 1 with hχ₄def
  obtain ⟨S₂, hS₂sub, hS₂card, col₄, hcol₄⟩ := hM₁ S₁
    (le_of_eq hS₁card.symm) χ₄
  have hab_cd : ∀ i i' j j' : Fin N, i ∈ S₂ → i' ∈ S₂ → j ∈ S₂ → j' ∈ S₂ →
      i < i' → i' < j → j < j' →
      AboveSeg (x i) (x j) (x i') (x j') ∨
      BelowSeg (x i) (x j) (x i') (x j') := by
    intro i i' j j' hi hi' hj hj' hii' hi'j hjj'
    obtain ⟨s, t, hs0, hs1, ht0, ht1, hc⟩ :=
      hcross i i' j j' (hS₂sub hi) (hS₂sub hi') (hS₂sub hj) (hS₂sub hj')
        hii' hi'j hjj'
    exact tuple_above_or_below hii' hi'j hjj'
      (affine_indep_four hx hgp hii' hi'j hjj') hs0 hs1 ht0 ht1 hc
  have hcol₄cases : col₄ = 0 ∨ col₄ = 1 := by
    have hv : col₄.val < 2 := col₄.isLt
    rcases (by omega : col₄.val = 0 ∨ col₄.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  refine ⟨S₂, hS₂card, ?_⟩
  rcases hcol₄cases with h0 | h0
  · left
    intro i i' j j' hi hi' hj hj' hii' hi'j hjj'
    have hTsub : ({i, i', j, j'} : Finset (Fin N)) ⊆ S₂ := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> assumption
    have hχ := hcol₄ _ hTsub (card_four hii' hi'j hjj')
    rw [h0] at hχ
    simp only [hχ₄def] at hχ
    split_ifs at hχ with hcond
    · exact hcond i (by simp) i' (by simp) j (by simp) j' (by simp)
        hii' hi'j hjj'
    · exact absurd hχ (by decide)
  · right
    intro i i' j j' hi hi' hj hj' hii' hi'j hjj'
    have hTsub : ({i, i', j, j'} : Finset (Fin N)) ⊆ S₂ := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> assumption
    have hχ := hcol₄ _ hTsub (card_four hii' hi'j hjj')
    rw [h0] at hχ
    simp only [hχ₄def] at hχ
    split_ifs at hχ with hcond
    · exact absurd hχ (by decide)
    · push_neg at hcond
      obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hbc, hcd, hnot⟩ := hcond
      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        quad_eq hii' hi'j hjj' ha hb hc hd hab hbc hcd
      rcases hab_cd i i' j j' hi hi' hj hj' hii' hi'j hjj' with hA | hB
      · exact absurd hA hnot
      · exact hB

/-- **Corollary 2.4.**  In the situation of Proposition 2.2 there is a
`k`-element subsequence `x∘σ` whose interval splits
`{σ i : i < a ∨ b ≤ i < c}` and `{σ i : a ≤ i < b ∨ c ≤ i}` have disjoint
convex hulls for every `a ≤ b ≤ c` in `Fin k`. -/
theorem cor_2_4 {N : ℕ} {x : Fin N → Euc 3}
    (hx : Function.Injective x)
    (hgp : InGeneralPosition ((Finset.image x Finset.univ : Finset (Euc 3)) : Set (Euc 3)))
    (hπ : Function.Injective (proj2 ∘ x))
    (hconv : InConvexPosition (Finset.image (proj2 ∘ x) Finset.univ))
    {k : ℕ} (hk : 4 ≤ k) (hN : Classical.choose (aboveBelow_ramsey hk) ≤ N) :
    ∃ σ : Fin k ↪o Fin N, ∀ a b c : Fin k, a ≤ b → b ≤ c →
      Disjoint
        (convexHull ℝ ((Finset.image (x ∘ σ)
          ((Finset.univ.filter (fun i ↦ i < a ∨ (b ≤ i ∧ i < c))) : Finset (Fin k))) : Set (Euc 3)))
        (convexHull ℝ ((Finset.image (x ∘ σ)
          ((Finset.univ.filter (fun i ↦ (a ≤ i ∧ i < b) ∨ c ≤ i)) : Finset (Fin k))) : Set (Euc 3))) := by
  classical
  obtain ⟨S, hScard, hmono⟩ :=
    Classical.choose_spec (aboveBelow_ramsey hk) N hN x hx hgp hπ hconv
  refine ⟨S.orderEmbOfFin hScard, ?_⟩
  intro a b c hab hbc
  set σ : Fin k ↪o Fin N := S.orderEmbOfFin hScard with hσdef
  have hσmem : ∀ i : Fin k, σ i ∈ S := fun i ↦ Finset.orderEmbOfFin_mem S hScard i
  -- the four interval index sets
  set J₁ : Finset (Fin k) := Finset.univ.filter (fun i ↦ i < a) with hJ₁
  set J₂ : Finset (Fin k) := Finset.univ.filter (fun i ↦ a ≤ i ∧ i < b) with hJ₂
  set J₃ : Finset (Fin k) := Finset.univ.filter (fun i ↦ b ≤ i ∧ i < c) with hJ₃
  set J₄ : Finset (Fin k) := Finset.univ.filter (fun i ↦ c ≤ i) with hJ₄
  set X₁ : Finset (Euc 3) := Finset.image (x ∘ σ) J₁ with hX₁
  set X₂ : Finset (Euc 3) := Finset.image (x ∘ σ) J₂ with hX₂
  set X₃ : Finset (Euc 3) := Finset.image (x ∘ σ) J₃ with hX₃
  set X₄ : Finset (Euc 3) := Finset.image (x ∘ σ) J₄ with hX₄
  have hdisj : ∀ P Q : Finset (Fin k), Disjoint P Q →
      Disjoint (Finset.image (x ∘ σ) P) (Finset.image (x ∘ σ) Q) := by
    intro P Q hPQ
    rw [Finset.disjoint_left]
    rintro y hy hq
    rw [Finset.mem_image] at hy hq
    obtain ⟨i, hi, hiy⟩ := hy
    obtain ⟨j, hj, hjy⟩ := hq
    have hij : i = j := σ.injective (hx (hiy.trans hjy.symm))
    exact (Finset.disjoint_left.1 hPQ hi) (hij ▸ hj)
  have hd12 : Disjoint X₁ X₂ := hdisj J₁ J₂ (by
    rw [hJ₁, hJ₂, Finset.disjoint_filter]
    intro i _ hi₁ hi₂
    exact absurd (lt_of_lt_of_le hi₁ hi₂.1) (lt_irrefl i))
  have hd13 : Disjoint X₁ X₃ := hdisj J₁ J₃ (by
    rw [hJ₁, hJ₃, Finset.disjoint_filter]
    intro i _ hi₁ hi₂
    exact absurd (lt_of_lt_of_le (lt_of_lt_of_le hi₁ hab) hi₂.1) (lt_irrefl i))
  have hd14 : Disjoint X₁ X₄ := hdisj J₁ J₄ (by
    rw [hJ₁, hJ₄, Finset.disjoint_filter]
    intro i _ hi₁ hi₂
    exact absurd (lt_of_lt_of_le hi₁ (le_trans (le_trans hab hbc) hi₂))
      (lt_irrefl i))
  have hd23 : Disjoint X₂ X₃ := hdisj J₂ J₃ (by
    rw [hJ₂, hJ₃, Finset.disjoint_filter]
    intro i _ hi₁ hi₂
    exact absurd (lt_of_lt_of_le hi₁.2 hi₂.1) (lt_irrefl i))
  have hd24 : Disjoint X₂ X₄ := hdisj J₂ J₄ (by
    rw [hJ₂, hJ₄, Finset.disjoint_filter]
    intro i _ hi₁ hi₂
    exact absurd (lt_of_lt_of_le hi₁.2 (le_trans hbc hi₂)) (lt_irrefl i))
  have hd34 : Disjoint X₃ X₄ := hdisj J₃ J₄ (by
    rw [hJ₃, hJ₄, Finset.disjoint_filter]
    intro i _ hi₁ hi₂
    exact absurd (lt_of_lt_of_le hi₁.2 hi₂) (lt_irrefl i))
  have hU₁₃ : X₁ ∪ X₃ = Finset.image (x ∘ σ)
      (Finset.univ.filter (fun i ↦ i < a ∨ (b ≤ i ∧ i < c))) := by
    rw [hX₁, hX₃, hJ₁, hJ₃, ← Finset.image_union, ← Finset.filter_or]
  have hU₂₄ : X₂ ∪ X₄ = Finset.image (x ∘ σ)
      (Finset.univ.filter (fun i ↦ (a ≤ i ∧ i < b) ∨ c ≤ i)) := by
    rw [hX₂, hX₄, hJ₂, hJ₄, ← Finset.image_union, ← Finset.filter_or]
  have hsub : ∀ J : Finset (Fin k),
      Finset.image (x ∘ σ) J ⊆ Finset.image x Finset.univ := by
    intro J y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact Finset.mem_image.2 ⟨σ i, Finset.mem_univ _, rfl⟩
  have memJ₁ : ∀ i : Fin k, i ∈ J₁ → i < a := fun i hi ↦ by
    have hm : i ∈ J₁ := hi
    rw [hJ₁, Finset.mem_filter] at hm
    exact hm.2
  have memJ₂ : ∀ i : Fin k, i ∈ J₂ → a ≤ i ∧ i < b := fun i hi ↦ by
    have hm : i ∈ J₂ := hi
    rw [hJ₂, Finset.mem_filter] at hm
    exact hm.2
  have memJ₃ : ∀ i : Fin k, i ∈ J₃ → b ≤ i ∧ i < c := fun i hi ↦ by
    have hm : i ∈ J₃ := hi
    rw [hJ₃, Finset.mem_filter] at hm
    exact hm.2
  have memJ₄ : ∀ i : Fin k, i ∈ J₄ → c ≤ i := fun i hi ↦ by
    have hm : i ∈ J₄ := hi
    rw [hJ₄, Finset.mem_filter] at hm
    exact hm.2
  -- Projected crossings of the `k`-tuple `i ↦ proj2 (x (σ i))`, and a helper
  -- lifting hull disjointness from `Euc 2` to `Euc 3`.
  have hvinj : Function.Injective (proj2 ∘ x ∘ σ) := hπ.comp σ.injective
  have hVk : InConvexPosition (Finset.image (proj2 ∘ x ∘ σ) Finset.univ) := by
    apply inConvexPosition_subset hconv
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image.2 ⟨σ i, Finset.mem_univ _, rfl⟩
  have hcrossK : ∀ i i' j j' : Fin k, i < i' → i' < j → j < j' →
      ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
        (1 - s) • (proj2 ∘ x ∘ σ) i + s • (proj2 ∘ x ∘ σ) j =
          (1 - t) • (proj2 ∘ x ∘ σ) i' + t • (proj2 ∘ x ∘ σ) j' := by
    intro i i' j j' h1 h2 h3
    rcases hmono with hall | hall
    · obtain ⟨s, t, hs0, hs1, ht0, ht1, hproj, _⟩ := hall (σ i) (σ i') (σ j)
        (σ j') (hσmem i) (hσmem i') (hσmem j) (hσmem j')
        (σ.lt_iff_lt.mpr h1) (σ.lt_iff_lt.mpr h2) (σ.lt_iff_lt.mpr h3)
      refine ⟨s, t, hs0, hs1, ht0, ht1, ?_⟩
      have hproj' := hproj
      simp only [map_add, map_smul] at hproj'
      simpa only [Function.comp_apply] using hproj'
    · obtain ⟨s, t, hs0, hs1, ht0, ht1, hproj, _⟩ := hall (σ i) (σ i') (σ j)
        (σ j') (hσmem i) (hσmem i') (hσmem j) (hσmem j')
        (σ.lt_iff_lt.mpr h1) (σ.lt_iff_lt.mpr h2) (σ.lt_iff_lt.mpr h3)
      refine ⟨s, t, hs0, hs1, ht0, ht1, ?_⟩
      have hproj' := hproj
      simp only [map_add, map_smul] at hproj'
      simpa only [Function.comp_apply] using hproj'
  have lift : ∀ JL JR : Finset (Fin k),
      Disjoint
        (convexHull ℝ ((JL.image (proj2 ∘ x ∘ σ) : Finset (Euc 2)) :
          Set (Euc 2)))
        (convexHull ℝ ((JR.image (proj2 ∘ x ∘ σ) : Finset (Euc 2)) :
          Set (Euc 2))) →
      Disjoint
        (convexHull ℝ ((JL.image (x ∘ σ) : Finset (Euc 3)) : Set (Euc 3)))
        (convexHull ℝ ((JR.image (x ∘ σ) : Finset (Euc 3)) : Set (Euc 3))) := by
    intro JL JR h
    apply disjoint_hull_proj2
    rwa [Finset.image_image, Finset.image_image]
  have hJ4 : J₄.Nonempty :=
    ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ c, le_refl c⟩⟩
  -- split on which of the interval blocks `J₁`, `J₂`, `J₃` are empty
  by_cases hJ1 : J₁.Nonempty
  · by_cases hJ2 : J₂.Nonempty
    · by_cases hJ3 : J₃.Nonempty
      · -- all blocks nonempty: `prop_2_3` applies directly
        rcases hmono with hall | hall
        · have hgpU : InGeneralPosition
              ((X₁ ∪ X₂ ∪ X₃ ∪ X₄ : Finset (Euc 3)) : Set (Euc 3)) := by
            intro s hs hcard
            apply hgp s _ hcard
            exact hs.trans (Finset.coe_subset.2
              (Finset.union_subset
                (Finset.union_subset
                  (Finset.union_subset (hsub J₁) (hsub J₂)) (hsub J₃))
                (hsub J₄)))
          have habove : ∀ x1 ∈ X₁, ∀ x2 ∈ X₂, ∀ x3 ∈ X₃, ∀ x4 ∈ X₄,
              AboveSeg x1 x3 x2 x4 := by
            rintro x1 hx1 x2 hx2 x3 hx3 x4 hx4
            obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 (hX₁ ▸ hx1)
            obtain ⟨i₂, hi₂, rfl⟩ := Finset.mem_image.1 (hX₂ ▸ hx2)
            obtain ⟨i₃, hi₃, rfl⟩ := Finset.mem_image.1 (hX₃ ▸ hx3)
            obtain ⟨i₄, hi₄, rfl⟩ := Finset.mem_image.1 (hX₄ ▸ hx4)
            have hi₁a : i₁ < a := memJ₁ i₁ hi₁
            have hi₂ab : a ≤ i₂ ∧ i₂ < b := memJ₂ i₂ hi₂
            have hi₃bc : b ≤ i₃ ∧ i₃ < c := memJ₃ i₃ hi₃
            have hi₄c : c ≤ i₄ := memJ₄ i₄ hi₄
            have h12 : σ i₁ < σ i₂ :=
              σ.lt_iff_lt.mpr (lt_of_lt_of_le hi₁a hi₂ab.1)
            have h23 : σ i₂ < σ i₃ :=
              σ.lt_iff_lt.mpr (lt_of_lt_of_le hi₂ab.2 hi₃bc.1)
            have h34 : σ i₃ < σ i₄ :=
              σ.lt_iff_lt.mpr (lt_of_lt_of_le hi₃bc.2 hi₄c)
            exact hall (σ i₁) (σ i₂) (σ i₃) (σ i₄)
              (hσmem i₁) (hσmem i₂) (hσmem i₃) (hσmem i₄) h12 h23 h34
          have hd := prop_2_3 (hJ1.image (x ∘ σ)) (hJ2.image (x ∘ σ))
            (hJ3.image (x ∘ σ)) (hJ4.image (x ∘ σ))
            hd12 hd13 hd14 hd23 hd24 hd34 hgpU habove
          rw [hU₁₃, hU₂₄] at hd
          exact hd
        · have hgpU' : InGeneralPosition
              ((X₂ ∪ X₁ ∪ X₄ ∪ X₃ : Finset (Euc 3)) : Set (Euc 3)) := by
            intro s hs hcard
            apply hgp s _ hcard
            exact hs.trans (Finset.coe_subset.2
              (Finset.union_subset
                (Finset.union_subset
                  (Finset.union_subset (hsub J₂) (hsub J₁)) (hsub J₄))
                (hsub J₃)))
          have habove : ∀ x1 ∈ X₂, ∀ x2 ∈ X₁, ∀ x3 ∈ X₄, ∀ x4 ∈ X₃,
              AboveSeg x1 x3 x2 x4 := by
            rintro x1 hx1 x2 hx2 x3 hx3 x4 hx4
            obtain ⟨i₂, hi₂, rfl⟩ := Finset.mem_image.1 (hX₂ ▸ hx1)
            obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 (hX₁ ▸ hx2)
            obtain ⟨i₄, hi₄, rfl⟩ := Finset.mem_image.1 (hX₄ ▸ hx3)
            obtain ⟨i₃, hi₃, rfl⟩ := Finset.mem_image.1 (hX₃ ▸ hx4)
            have hi₁a : i₁ < a := memJ₁ i₁ hi₁
            have hi₂ab : a ≤ i₂ ∧ i₂ < b := memJ₂ i₂ hi₂
            have hi₃bc : b ≤ i₃ ∧ i₃ < c := memJ₃ i₃ hi₃
            have hi₄c : c ≤ i₄ := memJ₄ i₄ hi₄
            have h12 : σ i₁ < σ i₂ :=
              σ.lt_iff_lt.mpr (lt_of_lt_of_le hi₁a hi₂ab.1)
            have h23 : σ i₂ < σ i₃ :=
              σ.lt_iff_lt.mpr (lt_of_lt_of_le hi₂ab.2 hi₃bc.1)
            have h34 : σ i₃ < σ i₄ :=
              σ.lt_iff_lt.mpr (lt_of_lt_of_le hi₃bc.2 hi₄c)
            have hb := hall (σ i₁) (σ i₂) (σ i₃) (σ i₄)
              (hσmem i₁) (hσmem i₂) (hσmem i₃) (hσmem i₄) h12 h23 h34
            exact belowSeg_iff.1 hb
          have hd := prop_2_3 (hJ2.image (x ∘ σ)) (hJ1.image (x ∘ σ))
            (hJ4.image (x ∘ σ)) (hJ3.image (x ∘ σ))
            hd12.symm hd24 hd23 hd14 hd13 hd34.symm hgpU' habove
          have hd' := hd.symm
          rw [hU₁₃, hU₂₄] at hd'
          exact hd'
      · -- `J₃` empty (so `b = c`): the right side is the arc `[a, k)`
        -- and the left side is `J₁ = [0, a)`, its complement.
        have hbc' : b = c := by
          have h : J₃ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ3
          have hb : b ∉ J₃ := Finset.eq_empty_iff_forall_notMem.mp h b
          rw [hJ₃, Finset.mem_filter] at hb
          exact le_antisymm hbc
            (not_lt.mp fun hlt ↦ hb ⟨Finset.mem_univ b, le_refl b, hlt⟩)
        set M : Fin k := ⟨k - 1, by have := a.isLt; omega⟩ with hMdef
        have hMv : M.val = k - 1 := rfl
        have hle_M : ∀ i : Fin k, i ≤ M := fun i ↦ by
          rw [Fin.le_iff_val_le_val, hMv]
          have := i.isLt
          omega
        have hlt_M : ∀ i : Fin k, ¬ M < i := fun i ↦ not_lt_of_ge (hle_M i)
        have hL : Finset.univ.filter (fun i : Fin k ↦ i < a ∨ (b ≤ i ∧ i < c)) =
            Finset.univ.filter (fun i : Fin k ↦ i < a ∨ M < i) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact absurd (lt_of_le_of_lt h1 (hbc'.symm ▸ h2)) (lt_irrefl b)
          · rintro (h | h)
            · exact Or.inl h
            · exact absurd h (hlt_M i)
        have hR : Finset.univ.filter (fun i : Fin k ↦ (a ≤ i ∧ i < b) ∨ c ≤ i) =
            Finset.univ.filter (fun i : Fin k ↦ a ≤ i ∧ i ≤ M) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro (⟨h1, h2⟩ | h3)
            · exact ⟨h1, hle_M i⟩
            · exact ⟨le_trans (le_trans hab hbc'.le) h3, hle_M i⟩
          · rintro ⟨h1, -⟩
            rcases lt_or_ge i b with hi | hi
            · exact Or.inl ⟨h1, hi⟩
            · exact Or.inr (hbc' ▸ hi)
        apply lift
        rw [hL, hR]
        exact (hull_arc_disjoint hvinj hVk hcrossK (hle_M a)).symm
    · -- `J₂` empty (so `a = b`): the right side is the arc `[c, k)`
      -- and the left side is `J₁ ∪ J₃ = [0, c)`, its complement.
      have hab' : a = b := by
        have h : J₂ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ2
        have ha' : a ∉ J₂ := Finset.eq_empty_iff_forall_notMem.mp h a
        rw [hJ₂, Finset.mem_filter] at ha'
        exact le_antisymm hab
          (not_lt.mp fun hlt ↦ ha' ⟨Finset.mem_univ a, le_refl a, hlt⟩)
      set M : Fin k := ⟨k - 1, by have := a.isLt; omega⟩ with hMdef
      have hMv : M.val = k - 1 := rfl
      have hle_M : ∀ i : Fin k, i ≤ M := fun i ↦ by
        rw [Fin.le_iff_val_le_val, hMv]
        have := i.isLt
        omega
      have hlt_M : ∀ i : Fin k, ¬ M < i := fun i ↦ not_lt_of_ge (hle_M i)
      have hL : Finset.univ.filter (fun i : Fin k ↦ i < a ∨ (b ≤ i ∧ i < c)) =
          Finset.univ.filter (fun i : Fin k ↦ i < c ∨ M < i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (h | ⟨-, h2⟩)
          · exact Or.inl (lt_of_lt_of_le h (le_trans hab hbc))
          · exact Or.inl h2
        · rintro (h | h)
          · rcases lt_or_ge i a with hi | hi
            · exact Or.inl hi
            · exact Or.inr ⟨hab' ▸ hi, h⟩
          · exact absurd h (hlt_M i)
      have hR : Finset.univ.filter (fun i : Fin k ↦ (a ≤ i ∧ i < b) ∨ c ≤ i) =
          Finset.univ.filter (fun i : Fin k ↦ c ≤ i ∧ i ≤ M) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (⟨h1, h2⟩ | h3)
          · exact absurd (lt_of_lt_of_le h2 (hab' ▸ h1)) (lt_irrefl i)
          · exact ⟨h3, hle_M i⟩
        · rintro ⟨h1, -⟩
          exact Or.inr h1
      apply lift
      rw [hL, hR]
      exact (hull_arc_disjoint hvinj hVk hcrossK (hle_M c)).symm
  · by_cases hJ3 : J₃.Nonempty
    · -- `J₁` empty (so `a = 0`) with `J₃` nonempty: the left side is the arc
      -- `[b, c)` and the right side is its complement.
      obtain ⟨i₀, hi₀⟩ := hJ3
      have hbc'' : b < c := lt_of_le_of_lt (memJ₃ i₀ hi₀).1 (memJ₃ i₀ hi₀).2
      have ha : ∀ i : Fin k, a ≤ i := fun i ↦
        not_lt.mp fun hi ↦
          hJ1 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
      set s' : Fin k := ⟨c.val - 1, by
        have hbv := Fin.lt_def.mp hbc''
        have := c.isLt
        omega⟩ with hs'def
      have hs'v : s'.val = c.val - 1 := rfl
      have hle_s' : ∀ i : Fin k, i ≤ s' ↔ i < c := fun i ↦ by
        rw [Fin.le_iff_val_le_val, Fin.lt_def, hs'v]
        have hbv := Fin.lt_def.mp hbc''
        omega
      have hlt_s' : ∀ i : Fin k, s' < i ↔ c ≤ i := fun i ↦ by
        rw [Fin.lt_def, Fin.le_iff_val_le_val, hs'v]
        have hbv := Fin.lt_def.mp hbc''
        omega
      have hrs' : b ≤ s' := by
        rw [Fin.le_iff_val_le_val, hs'v]
        have hbv := Fin.lt_def.mp hbc''
        omega
      have hL : Finset.univ.filter (fun i : Fin k ↦ i < a ∨ (b ≤ i ∧ i < c)) =
          Finset.univ.filter (fun i : Fin k ↦ b ≤ i ∧ i ≤ s') := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · exact absurd h (not_lt_of_ge (ha i))
          · exact ⟨h1, (hle_s' i).mpr h2⟩
        · rintro ⟨h1, h2⟩
          exact Or.inr ⟨h1, (hle_s' i).mp h2⟩
      have hR : Finset.univ.filter (fun i : Fin k ↦ (a ≤ i ∧ i < b) ∨ c ≤ i) =
          Finset.univ.filter (fun i : Fin k ↦ i < b ∨ s' < i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (⟨-, h2⟩ | h3)
          · exact Or.inl h2
          · exact Or.inr ((hlt_s' i).mpr h3)
        · rintro (h | h)
          · exact Or.inl ⟨ha i, h⟩
          · exact Or.inr ((hlt_s' i).mp h)
      apply lift
      rw [hL, hR]
      exact hull_arc_disjoint hvinj hVk hcrossK hrs'
    · -- `J₁` and `J₃` are both empty: the left side is empty.
      have hL : Finset.univ.filter (fun i : Fin k ↦ i < a ∨ (b ≤ i ∧ i < c)) =
          ∅ :=
        Finset.filter_false_of_mem fun i _ ↦ by
          rintro (h | ⟨h1, h2⟩)
          · exact hJ1 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩⟩
          · exact hJ3 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, h1, h2⟩⟩
      rw [hL, Finset.image_empty, Finset.coe_empty, convexHull_empty]
      exact disjoint_bot_left

end
