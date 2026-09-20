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

## Proof outline

We work with an order-free description: for a set `P` of points with
pairwise distinct `x`-coordinates, `IsCup P` is equivalent to the condition
(`CupShape`) that for every triple `u v w ∈ P` with `u 0 < v 0 < w 0` the
signed area `cross u v w` is positive, i.e. the consecutive slopes strictly
increase.  The factorization
`cross u v w = (v 0 - u 0)(w 0 - v 0)(sl v w - sl u v)` and its two variants
turn every slope comparison into a sign check on `cross`, so no sorting is
ever needed.

The combinatorial heart (`cupsCaps_aux`) is Erdős–Szekeres' induction on
`a + b`: split `X` into `E`, the set of points that are the right endpoint
of some `(a-1)`-cup, and its complement.  Either `X ∖ E` is large (then it
contains a `b`-cap or a contradiction with the definition of `E`) or `E` is
large (then a `(b-1)`-cap in `E` is extended by the second-to-last point of
the `(a-1)`-cup ending at its leftmost point, or symmetrically).
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

/-- The slope of the segment `uv` (only meaningful when `u 0 ≠ v 0`). -/
private def sl (u v : Euc 2) : ℝ := (v 1 - u 1) / (v 0 - u 0)

/-- Twice the signed area of the triangle `u v w`.  For `u 0 < v 0 < w 0`
its sign detects whether `v` lies strictly below (`cross > 0`, cup-like) or
strictly above (`cross < 0`, cap-like) the chord `uw`. -/
private def cross (u v w : Euc 2) : ℝ :=
  (v 0 - u 0) * (w 1 - u 1) - (v 1 - u 1) * (w 0 - u 0)

/-- Order-free cup shape: every increasing-`x` triple has positive signed
area.  Equivalent to `IsCup` under `DistinctX` (`isCup_of_cupShape`). -/
private def CupShape (P : Finset (Euc 2)) : Prop :=
  ∀ u ∈ P, ∀ v ∈ P, ∀ w ∈ P, u 0 < v 0 → v 0 < w 0 → 0 < cross u v w

/-- Order-free cap shape: every increasing-`x` triple has negative signed
area. -/
private def CapShape (P : Finset (Euc 2)) : Prop :=
  ∀ u ∈ P, ∀ v ∈ P, ∀ w ∈ P, u 0 < v 0 → v 0 < w 0 → cross u v w < 0

private theorem distinctX_mono {S X : Finset (Euc 2)} (h : S ⊆ X)
    (hdx : DistinctX X) : DistinctX S :=
  fun p hp q hq ↦ hdx p (h hp) q (h hq)

/-! ### Factorizations of `cross` into slope differences -/

private theorem cross_eq_right {u v w : Euc 2} (huv : u 0 < v 0) (hvw : v 0 < w 0) :
    cross u v w = (v 0 - u 0) * (w 0 - v 0) * (sl v w - sl u v) := by
  have h1 : v 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have h2 : w 0 - v 0 ≠ 0 := ne_of_gt (sub_pos.mpr hvw)
  unfold cross sl
  field_simp <;> ring

private theorem cross_eq_mid {u v w : Euc 2} (huv : u 0 < v 0) (hvw : v 0 < w 0) :
    cross u v w = (v 0 - u 0) * (w 0 - u 0) * (sl u w - sl u v) := by
  have h1 : v 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have h3 : w 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr (huv.trans hvw))
  unfold cross sl
  field_simp <;> ring

private theorem cross_eq_left {u v w : Euc 2} (huv : u 0 < v 0) (hvw : v 0 < w 0) :
    cross u v w = (w 0 - v 0) * (w 0 - u 0) * (sl v w - sl u w) := by
  have h2 : w 0 - v 0 ≠ 0 := ne_of_gt (sub_pos.mpr hvw)
  have h3 : w 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr (huv.trans hvw))
  unfold cross sl
  field_simp <;> ring

/-! ### Sign of `cross` versus slope comparisons -/

private theorem cross_pos_iff_sl {u v w : Euc 2} (huv : u 0 < v 0) (hvw : v 0 < w 0) :
    0 < cross u v w ↔ sl u v < sl v w := by
  rw [cross_eq_right huv hvw,
    mul_pos_iff_of_pos_left (mul_pos (sub_pos.mpr huv) (sub_pos.mpr hvw)), sub_pos]

private theorem cross_pos_iff_sl_mid {u v w : Euc 2} (huv : u 0 < v 0) (hvw : v 0 < w 0) :
    0 < cross u v w ↔ sl u v < sl u w := by
  rw [cross_eq_mid huv hvw,
    mul_pos_iff_of_pos_left (mul_pos (sub_pos.mpr huv) (sub_pos.mpr (huv.trans hvw))),
    sub_pos]

private theorem cross_pos_iff_sl_left {u v w : Euc 2} (huv : u 0 < v 0) (hvw : v 0 < w 0) :
    0 < cross u v w ↔ sl u w < sl v w := by
  rw [cross_eq_left huv hvw,
    mul_pos_iff_of_pos_left (mul_pos (sub_pos.mpr hvw) (sub_pos.mpr (huv.trans hvw))),
    sub_pos]

private theorem cross_neg_iff_sl {u v w : Euc 2} (huv : u 0 < v 0) (hvw : v 0 < w 0) :
    cross u v w < 0 ↔ sl v w < sl u v := by
  rw [cross_eq_right huv hvw]
  have hp : (0:ℝ) < (v 0 - u 0) * (w 0 - v 0) := mul_pos (sub_pos.mpr huv) (sub_pos.mpr hvw)
  exact ⟨fun h ↦ sub_neg.mp (neg_of_mul_neg_right h hp.le),
    fun h ↦ mul_neg_of_pos_of_neg hp (sub_neg.mpr h)⟩

private theorem cross_neg_iff_sl_mid {u v w : Euc 2} (huv : u 0 < v 0) (hvw : v 0 < w 0) :
    cross u v w < 0 ↔ sl u w < sl u v := by
  rw [cross_eq_mid huv hvw]
  have hp : (0:ℝ) < (v 0 - u 0) * (w 0 - u 0) :=
    mul_pos (sub_pos.mpr huv) (sub_pos.mpr (huv.trans hvw))
  exact ⟨fun h ↦ sub_neg.mp (neg_of_mul_neg_right h hp.le),
    fun h ↦ mul_neg_of_pos_of_neg hp (sub_neg.mpr h)⟩

private theorem cross_neg_iff_sl_left {u v w : Euc 2} (huv : u 0 < v 0) (hvw : v 0 < w 0) :
    cross u v w < 0 ↔ sl v w < sl u w := by
  rw [cross_eq_left huv hvw]
  have hp : (0:ℝ) < (w 0 - v 0) * (w 0 - u 0) :=
    mul_pos (sub_pos.mpr hvw) (sub_pos.mpr (huv.trans hvw))
  exact ⟨fun h ↦ sub_neg.mp (neg_of_mul_neg_right h hp.le),
    fun h ↦ mul_neg_of_pos_of_neg hp (sub_neg.mpr h)⟩

private theorem cross_eq_zero_iff_sl {u v w : Euc 2} (huv : u 0 < v 0) (hvw : v 0 < w 0) :
    cross u v w = 0 ↔ sl u v = sl v w := by
  rw [cross_eq_right huv hvw]
  have hp : (0:ℝ) < (v 0 - u 0) * (w 0 - v 0) := mul_pos (sub_pos.mpr huv) (sub_pos.mpr hvw)
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 (ne_of_gt hp)
    · exact (sub_eq_zero.mp h0).symm
  · intro h
    rw [sub_eq_zero.mpr h.symm, mul_zero]

/-! ### From `CupShape`/`CapShape` to `IsCup`/`IsCap` -/

/-- If the slopes grow, each point admits a supporting line from below whose
slope separates the slopes to the left points from the slopes to the right
points. -/
private theorem isCup_of_cupShape {P : Finset (Euc 2)} (hdx : DistinctX P)
    (hP : CupShape P) : IsCup P := by
  intro p hp
  classical
  have hLR : ∀ u ∈ P, u 0 < p 0 → ∀ w ∈ P, p 0 < w 0 → sl u p < sl p w :=
    fun u hu hux w hw hwx ↦
      (cross_pos_iff_sl hux hwx).mp (hP u hu p hp w hw hux hwx)
  obtain ⟨m, hml, hmr⟩ : ∃ m : ℝ,
      (∀ u ∈ P, u 0 < p 0 → sl u p < m) ∧ (∀ w ∈ P, p 0 < w 0 → m < sl p w) := by
    by_cases hL : ∃ u ∈ P, u 0 < p 0
    · by_cases hR : ∃ w ∈ P, p 0 < w 0
      · obtain ⟨u₀, hu₀, hmax⟩ := Finset.exists_max_image
          (P.filter (fun u ↦ u 0 < p 0)) (fun u ↦ sl u p)
          (hL.elim fun u hu ↦ ⟨u, Finset.mem_filter.mpr hu⟩)
        rw [Finset.mem_filter] at hu₀
        obtain ⟨w₀, hw₀, hmin⟩ := Finset.exists_min_image
          (P.filter (fun w ↦ p 0 < w 0)) (fun w ↦ sl p w)
          (hR.elim fun w hw ↦ ⟨w, Finset.mem_filter.mpr hw⟩)
        rw [Finset.mem_filter] at hw₀
        have hlt : sl u₀ p < sl p w₀ := hLR u₀ hu₀.1 hu₀.2 w₀ hw₀.1 hw₀.2
        refine ⟨(sl u₀ p + sl p w₀) / 2,
          fun u hu hux ↦ ?_, fun w hw hwx ↦ ?_⟩
        · have h := hmax u (Finset.mem_filter.mpr ⟨hu, hux⟩); linarith
        · have h := hmin w (Finset.mem_filter.mpr ⟨hw, hwx⟩); linarith
      · obtain ⟨u₀, hu₀, hmax⟩ := Finset.exists_max_image
          (P.filter (fun u ↦ u 0 < p 0)) (fun u ↦ sl u p)
          (hL.elim fun u hu ↦ ⟨u, Finset.mem_filter.mpr hu⟩)
        rw [Finset.mem_filter] at hu₀
        refine ⟨sl u₀ p + 1, fun u hu hux ↦ ?_, fun w hw hwx ↦ (hR ⟨w, hw, hwx⟩).elim⟩
        have h := hmax u (Finset.mem_filter.mpr ⟨hu, hux⟩); linarith
    · by_cases hR : ∃ w ∈ P, p 0 < w 0
      · obtain ⟨w₀, hw₀, hmin⟩ := Finset.exists_min_image
          (P.filter (fun w ↦ p 0 < w 0)) (fun w ↦ sl p w)
          (hR.elim fun w hw ↦ ⟨w, Finset.mem_filter.mpr hw⟩)
        rw [Finset.mem_filter] at hw₀
        refine ⟨sl p w₀ - 1, fun u hu hux ↦ (hL ⟨u, hu, hux⟩).elim,
          fun w hw hwx ↦ ?_⟩
        have h := hmin w (Finset.mem_filter.mpr ⟨hw, hwx⟩); linarith
      · exact ⟨0, fun u hu hux ↦ (hL ⟨u, hu, hux⟩).elim,
          fun w hw hwx ↦ (hR ⟨w, hw, hwx⟩).elim⟩
  refine ⟨m, p 1 - m * p 0, by ring, ?_⟩
  intro q hq hqp
  have hqx : q 0 ≠ p 0 := fun e ↦ hqp (hdx q hq p hp e)
  rcases lt_or_gt_of_ne hqx with hlt | hgt
  · have hsl : sl q p < m := hml q hq hlt
    rw [sl, div_lt_iff₀ (sub_pos.mpr hlt)] at hsl
    linarith
  · have hsl : m < sl p q := hmr q hq hgt
    rw [sl, lt_div_iff₀ (sub_pos.mpr hgt)] at hsl
    linarith

/-- Mirror image: every point of a cap admits a supporting line from above. -/
private theorem isCap_of_capShape {P : Finset (Euc 2)} (hdx : DistinctX P)
    (hP : CapShape P) : IsCap P := by
  intro p hp
  classical
  have hLR : ∀ u ∈ P, u 0 < p 0 → ∀ w ∈ P, p 0 < w 0 → sl p w < sl u p :=
    fun u hu hux w hw hwx ↦
      (cross_neg_iff_sl hux hwx).mp (hP u hu p hp w hw hux hwx)
  obtain ⟨m, hml, hmr⟩ : ∃ m : ℝ,
      (∀ u ∈ P, u 0 < p 0 → m < sl u p) ∧ (∀ w ∈ P, p 0 < w 0 → sl p w < m) := by
    by_cases hL : ∃ u ∈ P, u 0 < p 0
    · by_cases hR : ∃ w ∈ P, p 0 < w 0
      · obtain ⟨u₀, hu₀, hmin⟩ := Finset.exists_min_image
          (P.filter (fun u ↦ u 0 < p 0)) (fun u ↦ sl u p)
          (hL.elim fun u hu ↦ ⟨u, Finset.mem_filter.mpr hu⟩)
        rw [Finset.mem_filter] at hu₀
        obtain ⟨w₀, hw₀, hmax⟩ := Finset.exists_max_image
          (P.filter (fun w ↦ p 0 < w 0)) (fun w ↦ sl p w)
          (hR.elim fun w hw ↦ ⟨w, Finset.mem_filter.mpr hw⟩)
        rw [Finset.mem_filter] at hw₀
        have hlt : sl p w₀ < sl u₀ p := hLR u₀ hu₀.1 hu₀.2 w₀ hw₀.1 hw₀.2
        refine ⟨(sl p w₀ + sl u₀ p) / 2,
          fun u hu hux ↦ ?_, fun w hw hwx ↦ ?_⟩
        · have h := hmin u (Finset.mem_filter.mpr ⟨hu, hux⟩); linarith
        · have h := hmax w (Finset.mem_filter.mpr ⟨hw, hwx⟩); linarith
      · obtain ⟨u₀, hu₀, hmin⟩ := Finset.exists_min_image
          (P.filter (fun u ↦ u 0 < p 0)) (fun u ↦ sl u p)
          (hL.elim fun u hu ↦ ⟨u, Finset.mem_filter.mpr hu⟩)
        rw [Finset.mem_filter] at hu₀
        refine ⟨sl u₀ p - 1, fun u hu hux ↦ ?_, fun w hw hwx ↦ (hR ⟨w, hw, hwx⟩).elim⟩
        have h := hmin u (Finset.mem_filter.mpr ⟨hu, hux⟩); linarith
    · by_cases hR : ∃ w ∈ P, p 0 < w 0
      · obtain ⟨w₀, hw₀, hmax⟩ := Finset.exists_max_image
          (P.filter (fun w ↦ p 0 < w 0)) (fun w ↦ sl p w)
          (hR.elim fun w hw ↦ ⟨w, Finset.mem_filter.mpr hw⟩)
        rw [Finset.mem_filter] at hw₀
        refine ⟨sl p w₀ + 1, fun u hu hux ↦ (hL ⟨u, hu, hux⟩).elim,
          fun w hw hwx ↦ ?_⟩
        have h := hmax w (Finset.mem_filter.mpr ⟨hw, hwx⟩); linarith
      · exact ⟨0, fun u hu hux ↦ (hL ⟨u, hu, hux⟩).elim,
          fun w hw hwx ↦ (hR ⟨w, hw, hwx⟩).elim⟩
  refine ⟨m, p 1 - m * p 0, by ring, ?_⟩
  intro q hq hqp
  have hqx : q 0 ≠ p 0 := fun e ↦ hqp (hdx q hq p hp e)
  rcases lt_or_gt_of_ne hqx with hlt | hgt
  · have hsl : m < sl q p := hml q hq hlt
    rw [sl, lt_div_iff₀ (sub_pos.mpr hlt)] at hsl
    linarith
  · have hsl : sl p q < m := hmr q hq hgt
    rw [sl, div_lt_iff₀ (sub_pos.mpr hgt)] at hsl
    linarith

/-! ### Extension lemmas -/

/-- Appending a steeper edge to a cup keeps it a cup. -/
private theorem cupShape_insert {K : Finset (Euc 2)} {p r : Euc 2}
    (hdx : DistinctX K) (hK : CupShape K) (hp : p ∈ K)
    (hmax : ∀ u ∈ K, u 0 ≤ p 0) (hr : p 0 < r 0)
    (hcond : ∀ u ∈ K, u ≠ p → sl u p < sl p r) :
    CupShape (insert r K) := by
  intro u hu v hv w hw hu0 hv0
  rw [Finset.mem_insert] at hu hv hw
  rcases hw with hwr | hwK
  · -- `w = r`; then `u, v ∈ K`
    subst w
    rcases hv with rfl | hvK
    · exact absurd hv0 (lt_irrefl _)
    rcases hu with rfl | huK
    · exact absurd hu0 (not_lt.mpr (le_of_lt ((hmax v hvK).trans_lt hr)))
    by_cases hvp : v = p
    · subst v
      have hup : u ≠ p := by rintro rfl; exact lt_irrefl _ hu0
      exact (cross_pos_iff_sl hu0 hr).mpr (hcond u huK hup)
    · have hvp0 : v 0 < p 0 := lt_of_le_of_ne (hmax v hvK) (fun e ↦ hvp (hdx v hvK p hp e))
      have h1 : sl u v < sl v p := (cross_pos_iff_sl hu0 hvp0).mp (hK u huK v hvK p hp hu0 hvp0)
      have h2 : sl v p < sl p r := hcond v hvK hvp
      have h3 : sl v p < sl v r := (cross_pos_iff_sl_mid hvp0 hr).mp ((cross_pos_iff_sl hvp0 hr).mpr h2)
      exact (cross_pos_iff_sl hu0 hv0).mpr (h1.trans h3)
  · -- `w ∈ K`; then also `u, v ∈ K`
    have hvK : v ∈ K := by
      rcases hv with rfl | hvK
      · exact absurd hv0 (not_lt.mpr (le_of_lt ((hmax w hwK).trans_lt hr)))
      · exact hvK
    have huK : u ∈ K := by
      rcases hu with rfl | huK
      · exact absurd hu0 (not_lt.mpr (le_of_lt ((hmax v hvK).trans_lt hr)))
      · exact huK
    exact hK u huK v hvK w hwK hu0 hv0

/-- Prepending a steeper edge to a cap keeps it a cap. -/
private theorem capShape_insert {C : Finset (Euc 2)} {p q : Euc 2}
    (hdx : DistinctX C) (hC : CapShape C) (hp : p ∈ C)
    (hmin : ∀ u ∈ C, p 0 ≤ u 0) (hq : q 0 < p 0)
    (hcond : ∀ u ∈ C, u ≠ p → sl p u < sl q p) :
    CapShape (insert q C) := by
  intro u hu v hv w hw hu0 hv0
  rw [Finset.mem_insert] at hu hv hw
  rcases hu with huq | huC
  · -- `u = q`; then `v, w ∈ C`
    subst u
    rcases hv with rfl | hvC
    · exact absurd hu0 (lt_irrefl _)
    rcases hw with rfl | hwC
    · exact absurd hv0 (not_lt.mpr (le_trans (le_of_lt hq) (hmin v hvC)))
    by_cases hvp : v = p
    · subst v
      have hwp : w ≠ p := by rintro rfl; exact lt_irrefl _ hv0
      exact (cross_neg_iff_sl hq hv0).mpr (hcond w hwC hwp)
    · have hvp0 : p 0 < v 0 := lt_of_le_of_ne (hmin v hvC) (fun e ↦ hvp (hdx p hp v hvC e).symm)
      have h1 : sl v w < sl p v := (cross_neg_iff_sl hvp0 hv0).mp (hC p hp v hvC w hwC hvp0 hv0)
      have h2 : sl p v < sl q p := hcond v hvC hvp
      have h3 : cross q p v < 0 := (cross_neg_iff_sl hq hvp0).mpr h2
      have h4 : sl p v < sl q v := (cross_neg_iff_sl_left hq hvp0).mp h3
      exact (cross_neg_iff_sl hu0 hv0).mpr (h1.trans h4)
  · -- `u ∈ C`; then also `v, w ∈ C`
    have hvC : v ∈ C := by
      rcases hv with rfl | hvC
      · exact absurd hu0 (not_lt.mpr (le_trans (le_of_lt hq) (hmin u huC)))
      · exact hvC
    have hwC : w ∈ C := by
      rcases hw with rfl | hwC
      · exact absurd hv0 (not_lt.mpr (le_trans (le_of_lt hq) (hmin v hvC)))
      · exact hwC
    exact hC u huC v hvC w hwC hu0 hv0

/-- In a cup with rightmost point `p`, if the last edge slope `sl q p` is
below `sl p r` then *every* edge ending at `p` has slope below `sl p r`. -/
private theorem cup_right_slopes {K : Finset (Euc 2)} {p q r : Euc 2}
    (hdx : DistinctX K) (hK : CupShape K)
    (hp : p ∈ K) (hmax : ∀ u ∈ K, u 0 ≤ p 0)
    (hq : q ∈ K) (hqp : q ≠ p) (hqmax : ∀ u ∈ K, u ≠ p → u 0 ≤ q 0)
    (hqr : sl q p < sl p r) :
    ∀ u ∈ K, u ≠ p → sl u p < sl p r := by
  intro u hu hup
  have hqp0 : q 0 < p 0 := lt_of_le_of_ne (hmax q hq) (fun e ↦ hqp (hdx q hq p hp e))
  by_cases huq : u = q
  · subst huq; exact hqr
  · have huq0 : u 0 < q 0 := lt_of_le_of_ne (hqmax u hu hup) (fun e ↦ huq (hdx u hu q hq e))
    have hc : 0 < cross u q p := hK u hu q hq p hp huq0 hqp0
    have h1 : sl u p < sl q p := (cross_pos_iff_sl_left huq0 hqp0).mp hc
    exact h1.trans hqr

/-- In a cap with leftmost point `p`, if the first edge slope `sl p r`
is below `sl q p` then every edge starting at `p` has slope below `sl q p`. -/
private theorem cap_left_slopes {C : Finset (Euc 2)} {p q r : Euc 2}
    (hdx : DistinctX C) (hC : CapShape C)
    (hp : p ∈ C) (hmin : ∀ u ∈ C, p 0 ≤ u 0)
    (hr : r ∈ C) (hrp : r ≠ p) (hrmin : ∀ u ∈ C, u ≠ p → r 0 ≤ u 0)
    (hqr : sl p r < sl q p) :
    ∀ u ∈ C, u ≠ p → sl p u < sl q p := by
  intro u hu hup
  have hrp0 : p 0 < r 0 := lt_of_le_of_ne (hmin r hr) (fun e ↦ hrp (hdx p hp r hr e).symm)
  by_cases hur : u = r
  · subst hur; exact hqr
  · have hur0 : r 0 < u 0 := lt_of_le_of_ne (hrmin u hu hup) (fun e ↦ hur (hdx r hr u hu e).symm)
    have hc : cross p r u < 0 := hC p hp r hr u hu hrp0 hur0
    have h1 : sl p u < sl p r := (cross_neg_iff_sl_mid hrp0 hur0).mp hc
    exact h1.trans hqr

/-! ### General position ⇒ nonzero signed area -/

/-- Three points of a general-position set in `ℝ²` with increasing `x` are
not collinear, expressed as `cross ≠ 0`. -/
private theorem cross_ne_zero_of_gp {X : Finset (Euc 2)}
    (hX : InGeneralPosition (X : Set (Euc 2)))
    {u v w : Euc 2} (hu : u ∈ X) (hv : v ∈ X) (hw : w ∈ X)
    (huv : u 0 < v 0) (hvw : v 0 < w 0) : cross u v w ≠ 0 := by
  intro hc
  have huv' : u ≠ v := by rintro rfl; exact lt_irrefl _ huv
  have hvw' : v ≠ w := by rintro rfl; exact lt_irrefl _ hvw
  have huw' : u ≠ w := by rintro rfl; exact lt_irrefl _ (huv.trans hvw)
  have hsc : ({u, v, w} : Finset (Euc 2)).card = 2 + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [huv', huw']),
      Finset.card_insert_of_notMem (by simp [hvw']), Finset.card_singleton]
  have hsub : (({u, v, w} : Finset (Euc 2)) : Set (Euc 2)) ⊆ X := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hw
  have hAI := hX _ hsub hsc
  -- `w` is not in the affine span of `{u, v}`.
  have hnot : w ∉ affineSpan ℝ ({u, v} : Set (Euc 2)) := by
    have hws : w ∈ ({u, v, w} : Finset (Euc 2)) := by simp
    have h := hAI.notMem_affineSpan_sdiff ⟨w, hws⟩ Set.univ
    have himg : (fun x : ({u, v, w} : Finset (Euc 2)) ↦ (x : Euc 2)) ''
        (Set.univ \ {⟨w, hws⟩}) = {u, v} := by
      ext z
      constructor
      · rintro ⟨⟨y, hy⟩, hmem, hyz⟩
        change y = z at hyz
        subst hyz
        have hyw : y ≠ w := fun e ↦
          hmem.2 (Set.mem_singleton_iff.mpr (Subtype.ext e))
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact Set.mem_insert_iff.mpr (Or.inl rfl)
        · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
        · exact absurd rfl hyw
      · intro hz
        rcases hz with hz | hz
        · rw [hz]
          exact ⟨⟨u, by simp⟩,
            ⟨Set.mem_univ _, fun e ↦ huw' (congrArg Subtype.val (Set.mem_singleton_iff.mp e))⟩,
            rfl⟩
        · rw [hz]
          exact ⟨⟨v, by simp⟩,
            ⟨Set.mem_univ _, fun e ↦ hvw' (congrArg Subtype.val (Set.mem_singleton_iff.mp e))⟩,
            rfl⟩
    rw [himg] at h
    exact h
  -- But `cross u v w = 0` forces `w` onto the line through `u` and `v`.
  have hmem : w ∈ affineSpan ℝ ({u, v} : Set (Euc 2)) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨(w 0 - u 0) / (v 0 - u 0), ?_⟩
    rw [AffineMap.lineMap_apply_module]
    refine PiLp.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have hne : v 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huv)
      field_simp
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have hne : v 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huv)
      have hkey : (v 1 - u 1) * (w 0 - u 0) = (v 0 - u 0) * (w 1 - u 1) := by
        unfold cross at hc; linarith [hc]
      field_simp
      linear_combination hkey
  exact hnot hmem

/-! ### Small sets -/

private theorem card_three_of_triple {S : Finset (Euc 2)} {u v w : Euc 2}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S)
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) : 3 ≤ S.card := by
  have hsub : ({u, v, w} : Finset (Euc 2)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hw
  have hcard : ({u, v, w} : Finset (Euc 2)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [huv, huw]),
      Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact hle

private theorem cupShape_of_card_le_two {S : Finset (Euc 2)} (h : S.card ≤ 2) :
    CupShape S := by
  intro u hu v hv w hw hu0 hv0
  exfalso
  have huv : u ≠ v := by rintro rfl; exact lt_irrefl _ hu0
  have hvw : v ≠ w := by rintro rfl; exact lt_irrefl _ hv0
  have huw : u ≠ w := by rintro rfl; exact lt_irrefl _ (hu0.trans hv0)
  have h3 := card_three_of_triple hu hv hw huv hvw huw
  omega

private theorem capShape_of_card_le_two {S : Finset (Euc 2)} (h : S.card ≤ 2) :
    CapShape S := by
  intro u hu v hv w hw hu0 hv0
  exfalso
  have huv : u ≠ v := by rintro rfl; exact lt_irrefl _ hu0
  have hvw : v ≠ w := by rintro rfl; exact lt_irrefl _ hv0
  have huw : u ≠ w := by rintro rfl; exact lt_irrefl _ (hu0.trans hv0)
  have h3 := card_three_of_triple hu hv hw huv hvw huw
  omega

/-! ### The combinatorial induction -/

/-- Combinatorial form of cups-vs-caps: a set of `C(a+b-4, a-2)+1` points
with distinct `x`-coordinates, in general position, contains a `CupShape`
set of size `a` or a `CapShape` set of size `b`.  Proved by induction on
`a + b`. -/
private theorem cupsCaps_aux : ∀ n : ℕ, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → a + b ≤ n →
    ∀ X : Finset (Euc 2), DistinctX X → InGeneralPosition (X : Set (Euc 2)) →
    (a + b - 4).choose (a - 2) + 1 ≤ X.card →
    ∃ S ⊆ X, (S.card = a ∧ CupShape S) ∨ (S.card = b ∧ CapShape S) := by
  intro n
  induction n with
  | zero => rintro a b ha hb hn X hdx hX hcard; omega
  | succ n IH =>
    rintro a b ha hb hn X hdx hX hcard
    rcases eq_or_lt_of_le ha with rfl | ha3
    · -- `a = 2`: any two points form a cup
      have h2' : (2 + b - 4).choose (2 - 2) = 1 := by
        rw [show 2 + b - 4 = b - 2 by omega, show 2 - 2 = 0 by omega,
          Nat.choose_zero_right]
      have h2 : 2 ≤ X.card := by omega
      obtain ⟨S, hSX, hScard⟩ := Finset.exists_subset_card_eq h2
      exact ⟨S, hSX, Or.inl ⟨hScard, cupShape_of_card_le_two hScard.le⟩⟩
    · rcases eq_or_lt_of_le hb with rfl | hb3
      · -- `b = 2`: any two points form a cap
        have h2' : (a + 2 - 4).choose (a - 2) = 1 := by
          rw [show a + 2 - 4 = a - 2 by omega, Nat.choose_self]
        have h2 : 2 ≤ X.card := by omega
        obtain ⟨S, hSX, hScard⟩ := Finset.exists_subset_card_eq h2
        exact ⟨S, hSX, Or.inr ⟨hScard, capShape_of_card_le_two hScard.le⟩⟩
      · -- `a, b ≥ 3`: the Erdős–Szekeres endpoint argument
        classical
        set E := X.filter (fun p ↦ ∃ K : Finset (Euc 2), K ⊆ X ∧ K.card = a - 1 ∧
          CupShape K ∧ p ∈ K ∧ ∀ u ∈ K, u 0 ≤ p 0) with hEdef
        by_cases hbig : (a + b - 5).choose (a - 3) + 1 ≤ (X \ E).card
        · -- `X ∖ E` is large: apply the `(a-1, b)` hypothesis
          obtain ⟨S, hSX, hS⟩ := IH (a - 1) b (by omega) hb (by omega) (X \ E)
            (distinctX_mono Finset.sdiff_subset hdx)
            (inGeneralPosition_mono hX (Finset.coe_subset.mpr Finset.sdiff_subset))
            (by rw [show a - 1 + b - 4 = a + b - 5 by omega,
                    show a - 1 - 2 = a - 3 by omega]; exact hbig)
          rcases hS with ⟨hScard, hcup⟩ | ⟨hScard, hcap⟩
          · -- an `(a-1)`-cup in `X ∖ E` ends in `E`: contradiction
            obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image S (· 0)
              (Finset.card_pos.mp (by omega : 0 < S.card))
            have hpX : p ∈ X := (Finset.mem_sdiff.mp (hSX hpS)).1
            have hpE : p ∈ E := by
              rw [hEdef, Finset.mem_filter]
              exact ⟨hpX, S, hSX.trans Finset.sdiff_subset, hScard, hcup, hpS, hpmax⟩
            exact absurd hpE (Finset.mem_sdiff.mp (hSX hpS)).2
          · exact ⟨S, hSX.trans Finset.sdiff_subset, Or.inr ⟨hScard, hcap⟩⟩
        · -- `E` is large: apply the `(a, b-1)` hypothesis
          push Not at hbig
          have hsd : (X \ E).card = X.card - E.card :=
            Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
          have hch : (a + b - 4).choose (a - 2) =
              (a + b - 5).choose (a - 3) + (a + b - 5).choose (a - 2) := by
            rw [show a + b - 4 = a + b - 5 + 1 by omega,
              show a - 2 = a - 3 + 1 by omega, Nat.choose_succ_succ']
          have hEcard : (a + b - 5).choose (a - 2) + 1 ≤ E.card := by omega
          obtain ⟨S, hSE, hS⟩ := IH a (b - 1) ha (by omega) (by omega) E
            (distinctX_mono (Finset.filter_subset _ _) hdx)
            (inGeneralPosition_mono hX (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
            (by rw [show a + (b - 1) - 4 = a + b - 5 by omega]; exact hEcard)
          rcases hS with ⟨hScard, hcup⟩ | ⟨hScard, hcap⟩
          · exact ⟨S, hSE.trans (Finset.filter_subset _ _), Or.inl ⟨hScard, hcup⟩⟩
          · -- a `(b-1)`-cap `S ⊆ E`: extend with the cup ending at its leftmost point
            obtain ⟨p, hpS, hpmin⟩ := Finset.exists_min_image S (· 0)
              (Finset.card_pos.mp (by omega : 0 < S.card))
            obtain ⟨r, hrS, hrmin⟩ := Finset.exists_min_image (S.erase p) (· 0)
              (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hpS]; omega :
                0 < (S.erase p).card))
            have hpE : p ∈ E := hSE hpS
            rw [hEdef, Finset.mem_filter] at hpE
            obtain ⟨hpX, K, hKX, hKcard, hKcup, hpK, hKmax⟩ := hpE
            obtain ⟨q, hqK, hqmax⟩ := Finset.exists_max_image (K.erase p) (· 0)
              (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hpK]; omega :
                0 < (K.erase p).card))
            have hrS' : r ∈ S := (Finset.mem_erase.mp hrS).2
            have hrp : r ≠ p := (Finset.mem_erase.mp hrS).1
            have hqK' : q ∈ K := (Finset.mem_erase.mp hqK).2
            have hqp : q ≠ p := (Finset.mem_erase.mp hqK).1
            have hdxS : DistinctX S :=
              distinctX_mono (hSE.trans (Finset.filter_subset _ _)) hdx
            have hdxK : DistinctX K := distinctX_mono hKX hdx
            have hpr0 : p 0 < r 0 :=
              lt_of_le_of_ne (hpmin r hrS') (fun e ↦ hrp (hdxS p hpS r hrS' e).symm)
            have hqp0 : q 0 < p 0 :=
              lt_of_le_of_ne (hKmax q hqK') (fun e ↦ hqp (hdxK q hqK' p hpK e))
            have hqX : q ∈ X := hKX hqK'
            have hrX : r ∈ X := (Finset.filter_subset _ _) (hSE hrS')
            have hne : sl q p ≠ sl p r := fun e ↦
              cross_ne_zero_of_gp hX hqX hpX hrX hqp0 hpr0
                ((cross_eq_zero_iff_sl hqp0 hpr0).mpr e)
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · -- `sl q p < sl p r`: `insert r K` is an `a`-cup
              have hcond : ∀ u ∈ K, u ≠ p → sl u p < sl p r :=
                cup_right_slopes hdxK hKcup hpK hKmax hqK' hqp
                  (fun u hu hup ↦ hqmax u (Finset.mem_erase.mpr ⟨hup, hu⟩)) hlt
              have hrK : r ∉ K := fun hrK ↦ absurd hpr0 (not_lt.mpr (hKmax r hrK))
              refine ⟨insert r K, ?_, Or.inl ⟨?_, ?_⟩⟩
              · rw [Finset.insert_subset_iff]; exact ⟨hrX, hKX⟩
              · rw [Finset.card_insert_of_notMem hrK, hKcard]; omega
              · exact cupShape_insert hdxK hKcup hpK hKmax hpr0 hcond
            · -- `sl p r < sl q p`: `insert q S` is a `b`-cap
              have hcond : ∀ u ∈ S, u ≠ p → sl p u < sl q p :=
                cap_left_slopes hdxS hcap hpS hpmin hrS' hrp
                  (fun u hu hup ↦ hrmin u (Finset.mem_erase.mpr ⟨hup, hu⟩)) hgt
              have hqS : q ∉ S := fun hqS ↦ absurd hqp0 (not_lt.mpr (hpmin q hqS))
              refine ⟨insert q S, ?_, Or.inr ⟨?_, ?_⟩⟩
              · rw [Finset.insert_subset_iff]
                exact ⟨hqX, hSE.trans (Finset.filter_subset _ _)⟩
              · rw [Finset.card_insert_of_notMem hqS, hScard]; omega
              · exact capShape_insert hdxS hcap hpS hpmin hqp0 hcond

/-- **Theorem 2.1 (cups vs caps).**  Any set of `(a+b-4 choose a-2)+1` points in
`ℝ²` in general position with distinct `x`-coordinates contains an `a`-cup or a
`b`-cap.  Paper item: Theorem 2.1 (Erdős–Szekeres 1935). -/
theorem cupsCaps {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    {X : Finset (Euc 2)} (hX : InGeneralPosition (X : Set (Euc 2))) (hdx : DistinctX X)
    (hcard : (a + b - 4).choose (a - 2) + 1 ≤ X.card) :
    ∃ S ⊆ X, (S.card = a ∧ IsCup S) ∨ (S.card = b ∧ IsCap S) := by
  obtain ⟨S, hSX, hS⟩ := cupsCaps_aux (a + b) a b ha hb le_rfl X hdx hX hcard
  have hdxS : DistinctX S := distinctX_mono hSX hdx
  rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨S, hSX, Or.inl ⟨h1, isCup_of_cupShape hdxS h2⟩⟩
  · exact ⟨S, hSX, Or.inr ⟨h1, isCap_of_capShape hdxS h2⟩⟩

end
