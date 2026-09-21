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

## Formalization note — `SupportRegion` orientation (fixed)

In the paper (and in Suk's statement of [PV02, Theorem 4], which is quoted
verbatim in [PZ22, Theorem 2.2]), `T_i` is the *triangular* region adjacent to
the segment `x_i x_{i+1}`: for a cap it is
`LeftOf xᵢxᵢ₊₁ ∩ RightOf xᵢ₋₁xᵢ ∩ RightOf xᵢ₊₁xᵢ₊₂` — i.e. **below** the line
through the *next* edge.  An earlier version of this file used
`LeftOf xᵢ₊₁xᵢ₊₂` (cap case) for the third factor — the *opposite* (open)
half-plane, producing the unbounded wedge on the far side of the apex
`line xᵢ₋₁xᵢ ∩ line xᵢ₊₁xᵢ₊₂`, disjoint from the segment `xᵢxᵢ₊₁`; the
transversal-convexity clause of Theorem 2.2 fails for that region (witnessed
numerically below for the cap `(0,0),(1,3),(2,4),(3,3),(4,0)`).

`SupportRegion` now uses the corrected third conjunct
`if σ then RightOf xᵢ₁ r else LeftOf xᵢ₁ r` (same orientation pattern as the
second conjunct).  The examples below check that the formalized region is the
paper's triangular region: it contains the interior point `(1.7,3.9)` and
excludes the wedge points `(20,80), (17,20), (15,6), (20,-20)` that formed a
non-convex transversal under the wrong orientation.
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
  (if σ then RightOf xᵢ₁ r else LeftOf xᵢ₁ r)

/-- The support region `T i` of the `i`-th edge `x_i x_{i+1}` of a left-to-right
`(k+1)`-cap/cup `x : Fin (k+1) → Euc 2`, with wraparound indices `i±1` taken
modulo `k+1` (so `x_k x_0`, the chord closing `conv (range x)`, plays the role
of the missing neighbouring edge at both ends). -/
private abbrev supportOf {k : ℕ} (x : Fin (k + 1) → Euc 2) (σ : Bool) (i : Fin k) :
    Set (Euc 2) :=
  SupportRegion
    (x ⟨(i.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩)
    (x ⟨i.val, by omega⟩)
    (x ⟨i.val + 1, by omega⟩)
    (x ⟨(i.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩) σ

/-! ### Machine-checked sanity checks on `SupportRegion`

For the explicit cap `x = (0,0),(1,3),(2,4),(3,3),(4,0)` (a downward convex
`∩`-chain, `IsCap`), the checks below verify that the formalized
`SupportRegion` is the paper's triangular region: it contains an interior
point of that triangle and excludes the wedge points that, under the wrong
orientation of the third factor, admitted a non-convex transversal. -/

private def pvPt (a b : ℝ) : Euc 2 := WithLp.toLp 2 ![a, b]

@[simp] private lemma pvPt0 (a b : ℝ) : pvPt a b 0 = a := rfl
@[simp] private lemma pvPt1 (a b : ℝ) : pvPt a b 1 = b := rfl

/-- `(1.7, 3.9)` lies inside the triangular region of the paper's support for
the edge `(1,3)-(2,4)` (above the edge, to the right of the extension of
`(0,0)-(1,3)`, and to the left of the extension `y = -x + 6` of `(2,4)-(3,3)`),
and it *is* in the formalized `SupportRegion`. -/
example :
    pvPt 1.7 3.9 ∈ SupportRegion (pvPt 0 0) (pvPt 1 3) (pvPt 2 4) (pvPt 3 3) true := by
  simp only [SupportRegion, LeftOf, RightOf, Set.mem_inter_iff, pvPt0, pvPt1]
  norm_num

/-- The corrected region excludes exterior wedge points such as `(17, 20)`. -/
example :
    pvPt 17 20 ∉ SupportRegion (pvPt 0 0) (pvPt 1 3) (pvPt 2 4) (pvPt 3 3) true := by
  simp only [SupportRegion, LeftOf, RightOf, Set.mem_inter_iff, pvPt0, pvPt1]
  norm_num

/-- The next four non-memberships exclude region points
`y₀=(20,80), y₁=(17,20), y₂=(15,6), y₃=(20,-20)` which belonged to `T₀,…,T₃`
under the wrong orientation and formed a transversal *not* in convex position
(`y₁` lies strictly inside `conv {y₀, y₂, y₃}`). -/
example :
    pvPt 20 80 ∉ SupportRegion (pvPt 4 0) (pvPt 0 0) (pvPt 1 3) (pvPt 2 4) true := by
  simp only [SupportRegion, LeftOf, RightOf, Set.mem_inter_iff, pvPt0, pvPt1]
  norm_num

example :
    pvPt 15 6 ∉ SupportRegion (pvPt 1 3) (pvPt 2 4) (pvPt 3 3) (pvPt 4 0) true := by
  simp only [SupportRegion, LeftOf, RightOf, Set.mem_inter_iff, pvPt0, pvPt1]
  norm_num

example :
    pvPt 20 (-20) ∉ SupportRegion (pvPt 2 4) (pvPt 3 3) (pvPt 4 0) (pvPt 0 0) true := by
  simp only [SupportRegion, LeftOf, RightOf, Set.mem_inter_iff, pvPt0, pvPt1]
  norm_num

/-! ### Oriented-area API for the transversal-convexity clause

The last clause of `porValtr_dense_support` — every transversal of the
support regions is in convex position — is a self-contained geometric fact:
each support region `Tⱼ` lies strictly on the interior side of every *other*
edge line `xᵢxᵢ₊₁`, so that line strictly separates `Y i` from the remaining
`Y j`.  We develop this here via the signed area `pvCross`, a slope `pvSl`
and the height function `pvHgt` of an edge line.

Uniformity between caps and cups is achieved by the sign
`pvSgn σ = if σ then 1 else -1`: the cup/cap condition becomes
`pvSgn σ · pvCross (x a) (x b) (x c) < 0` for `a < b < c`, and the three
support-region inequalities become `0 < pvSgn σ · pvCross xⱼ xⱼ₊₁ p`,
`pvSgn σ · pvCross x_{j-1} xⱼ p < 0`, `pvSgn σ · pvCross xⱼ₊₁ x_{j+2} p < 0`. -/

/-- Twice the signed area of the oriented triangle `u v w` (the same quantity
as `CupsCaps.cross`, which is private there). -/
private def pvCross (u v w : Euc 2) : ℝ :=
  (v 0 - u 0) * (w 1 - u 1) - (v 1 - u 1) * (w 0 - u 0)

/-- The slope of the directed segment `u v`. -/
private noncomputable def pvSl (u v : Euc 2) : ℝ := (v 1 - u 1) / (v 0 - u 0)

/-- The height at abscissa `t` of the line through `u` and `v`. -/
private noncomputable def pvHgt (u v : Euc 2) (t : ℝ) : ℝ :=
  u 1 + pvSl u v * (t - u 0)

/-- The sign distinguishing cap (`σ = true`, `ε = 1`) from cup
(`σ = false`, `ε = -1`) in the uniform statements. -/
private def pvSgn (σ : Bool) : ℝ := if σ then 1 else -1

private lemma pvCross_self (u v : Euc 2) : pvCross u u v = 0 := by
  unfold pvCross; ring

private lemma pvCross_left (u v : Euc 2) : pvCross u v u = 0 := by
  unfold pvCross; ring

private lemma pvCross_right (u v : Euc 2) : pvCross u v v = 0 := by
  unfold pvCross; ring

private lemma pvCross_swap (u v w : Euc 2) : pvCross v u w = -pvCross u v w := by
  unfold pvCross; ring

private lemma pvCross_cyc (u v w : Euc 2) : pvCross u v w = pvCross v w u := by
  unfold pvCross; ring

private lemma mem_LeftOf_iff (u v p : Euc 2) : p ∈ LeftOf u v ↔ 0 < pvCross u v p :=
  Iff.rfl

private lemma mem_RightOf_iff (u v p : Euc 2) : p ∈ RightOf u v ↔ pvCross u v p < 0 := by
  show 0 < pvCross v u p ↔ pvCross u v p < 0
  rw [pvCross_swap]; constructor <;> intro h <;> linarith

/-- Membership in a support region, expressed uniformly in `σ` as sign
conditions on `pvCross`. -/
private lemma mem_supportOf_iff {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
    {j : Fin k} {p : Euc 2} :
    p ∈ supportOf x σ j ↔
      0 < pvSgn σ * pvCross (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) p ∧
      pvSgn σ * pvCross (x ⟨(j.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩)
        (x ⟨j.val, by omega⟩) p < 0 ∧
      pvSgn σ * pvCross (x ⟨j.val + 1, by omega⟩)
        (x ⟨(j.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩) p < 0 := by
  cases σ
  · -- `σ = false` (cup): region = `RightOf e ∩ LeftOf l ∩ LeftOf r`
    have e : supportOf x false j =
        (RightOf (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) ∩
          LeftOf (x ⟨(j.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩)
            (x ⟨j.val, by omega⟩)) ∩
        LeftOf (x ⟨j.val + 1, by omega⟩)
          (x ⟨(j.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩) := rfl
    rw [e, Set.mem_inter_iff, Set.mem_inter_iff, mem_RightOf_iff,
      mem_LeftOf_iff, mem_LeftOf_iff, show pvSgn false = (-1 : ℝ) from rfl]
    exact ⟨fun h ↦ ⟨by linarith [h.1.1], by linarith [h.1.2], by linarith [h.2]⟩,
      fun h ↦ ⟨⟨by linarith [h.1], by linarith [h.2.1]⟩, by linarith [h.2.2]⟩⟩
  · -- `σ = true` (cap): region = `LeftOf e ∩ RightOf l ∩ RightOf r`
    have e : supportOf x true j =
        (LeftOf (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) ∩
          RightOf (x ⟨(j.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩)
            (x ⟨j.val, by omega⟩)) ∩
        RightOf (x ⟨j.val + 1, by omega⟩)
          (x ⟨(j.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩) := rfl
    rw [e, Set.mem_inter_iff, Set.mem_inter_iff, mem_LeftOf_iff,
      mem_RightOf_iff, mem_RightOf_iff, show pvSgn true = (1 : ℝ) from rfl]
    exact ⟨fun h ↦ ⟨by linarith [h.1.1], by linarith [h.1.2], by linarith [h.2]⟩,
      fun h ↦ ⟨⟨by linarith [h.1], by linarith [h.2.1]⟩, by linarith [h.2.2]⟩⟩

/-- The signed area expressed through the height function of the edge line. -/
private lemma pvCross_eq_hgt {u v : Euc 2} (h : v 0 ≠ u 0) (p : Euc 2) :
    pvCross u v p = (v 0 - u 0) * (p 1 - pvHgt u v (p 0)) := by
  unfold pvCross pvHgt pvSl
  field_simp
  ring

/-- The height function recomputed at the right endpoint. -/
private lemma pvHgt_at_right {u v : Euc 2} (h : v 0 ≠ u 0) (t : ℝ) :
    pvHgt u v t = v 1 + pvSl u v * (t - v 0) := by
  unfold pvHgt pvSl
  field_simp
  ring

/-- The height function is affine in `t` with slope `pvSl u v`. -/
private lemma pvHgt_affine (u v : Euc 2) (t t₀ : ℝ) :
    pvHgt u v t = pvHgt u v t₀ + pvSl u v * (t - t₀) := by
  unfold pvHgt; ring

/-- From the cup/cap condition: in a cap every increasing-`x` triple has
negative signed area (and the mirror statement for cups). -/
private lemma pvCross_neg_of_isCap {P : Finset (Euc 2)} (hP : IsCap P)
    {u v w : Euc 2} (hu : u ∈ P) (hv : v ∈ P) (hw : w ∈ P)
    (huv : u 0 < v 0) (hvw : v 0 < w 0) : pvCross u v w < 0 := by
  obtain ⟨a, b, hvb, hbelow⟩ := hP v hv
  have hu' : u 1 < a * u 0 + b := hbelow u hu (fun e ↦ (by rw [e] at huv; exact lt_irrefl _ huv))
  have hw' : w 1 < a * w 0 + b := hbelow w hw (fun e ↦ (by rw [e] at hvw; exact lt_irrefl _ hvw))
  have h1 : w 1 - v 1 < a * (w 0 - v 0) := by linarith
  have h2 : v 1 - u 1 > a * (v 0 - u 0) := by linarith
  have e : pvCross u v w = (v 0 - u 0) * (w 1 - v 1) - (v 1 - u 1) * (w 0 - v 0) := by
    unfold pvCross; ring
  have hstep : pvCross u v w <
      (v 0 - u 0) * (a * (w 0 - v 0)) - (a * (v 0 - u 0)) * (w 0 - v 0) := by
    rw [e]
    apply sub_lt_sub
    · exact mul_lt_mul_of_pos_left h1 (sub_pos.mpr huv)
    · exact mul_lt_mul_of_pos_right h2 (sub_pos.mpr hvw)
  have heq : (v 0 - u 0) * (a * (w 0 - v 0)) - (a * (v 0 - u 0)) * (w 0 - v 0) = 0 := by ring
  linarith

/-- The mirror statement for cups: increasing-`x` triples have positive
signed area. -/
private lemma pvCross_pos_of_isCup {P : Finset (Euc 2)} (hP : IsCup P)
    {u v w : Euc 2} (hu : u ∈ P) (hv : v ∈ P) (hw : w ∈ P)
    (huv : u 0 < v 0) (hvw : v 0 < w 0) : 0 < pvCross u v w := by
  obtain ⟨a, b, hvb, habove⟩ := hP v hv
  have hu' : u 1 > a * u 0 + b := habove u hu (fun e ↦ (by rw [e] at huv; exact lt_irrefl _ huv))
  have hw' : w 1 > a * w 0 + b := habove w hw (fun e ↦ (by rw [e] at hvw; exact lt_irrefl _ hvw))
  have h1 : w 1 - v 1 > a * (w 0 - v 0) := by linarith
  have h2 : v 1 - u 1 < a * (v 0 - u 0) := by linarith
  have e : pvCross u v w = (v 0 - u 0) * (w 1 - v 1) - (v 1 - u 1) * (w 0 - v 0) := by
    unfold pvCross; ring
  have hstep : pvCross u v w >
      (v 0 - u 0) * (a * (w 0 - v 0)) - (a * (v 0 - u 0)) * (w 0 - v 0) := by
    rw [e]
    apply sub_lt_sub
    · exact mul_lt_mul_of_pos_left h1 (sub_pos.mpr huv)
    · exact mul_lt_mul_of_pos_right h2 (sub_pos.mpr hvw)
  have heq : (v 0 - u 0) * (a * (w 0 - v 0)) - (a * (v 0 - u 0)) * (w 0 - v 0) = 0 := by ring
  linarith

/-- The signed area factors through a slope difference (chord vs. first
edge). -/
private lemma pvCross_eq_mid {u v w : Euc 2} (huv : u 0 < v 0) (huw : u 0 < w 0) :
    pvCross u v w = (v 0 - u 0) * (w 0 - u 0) * (pvSl u w - pvSl u v) := by
  unfold pvCross pvSl
  have h1 : v 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have h2 : w 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huw)
  field_simp

/-- The signed area factors through a slope difference (second edge vs.
chord). -/
private lemma pvCross_eq_left {u v w : Euc 2} (hvw : v 0 < w 0) (huw : u 0 < w 0) :
    pvCross u v w = (w 0 - v 0) * (w 0 - u 0) * (pvSl v w - pvSl u w) := by
  unfold pvCross pvSl
  have h1 : w 0 - v 0 ≠ 0 := ne_of_gt (sub_pos.mpr hvw)
  have h2 : w 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huw)
  field_simp
  ring

/-- Cancelling a positive middle factor inside a `pvSgn`-scaled product. -/
private lemma pv_mul_neg_of_pos_factor {ε P c : ℝ} (hP : 0 < P) (h : ε * (P * c) < 0) :
    ε * c < 0 := by
  rw [mul_left_comm] at h
  exact Right.neg_of_mul_neg_right h hP.le

/-- Cancelling a positive middle factor inside a `pvSgn`-scaled product,
`0 <` version. -/
private lemma pv_mul_pos_of_pos_factor {ε P c : ℝ} (hP : 0 < P) (h : 0 < ε * (P * c)) :
    0 < ε * c := by
  rw [mul_left_comm] at h
  exact pos_of_mul_pos_right h hP.le

/-- The cup/cap shape condition on a left-to-right chain, in uniform
`pvSgn`-scaled form: every increasing triple has interior-side signed
area. -/
private def pvShaped {k : ℕ} (x : Fin (k + 1) → Euc 2) (σ : Bool) : Prop :=
  ∀ a b c : Fin (k + 1), a < b → b < c → pvSgn σ * pvCross (x a) (x b) (x c) < 0

private lemma pvShaped_of_capOrCup {k : ℕ} {x : Fin (k + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (x i) 0) {σ : Bool}
    (h : if σ then IsCap (Finset.image x Finset.univ)
         else IsCup (Finset.image x Finset.univ)) : pvShaped x σ := by
  intro a b c hab hbc
  have mem : ∀ t : Fin (k + 1), x t ∈ Finset.image x Finset.univ :=
    fun t ↦ Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
  cases σ
  · -- `σ = false` (cup)
    have h' : IsCup (Finset.image x Finset.univ) := h
    have hc := pvCross_pos_of_isCup h' (mem a) (mem b) (mem c) (hmono hab)
      (hmono hbc)
    rw [show pvSgn false = (-1 : ℝ) from rfl]
    linarith
  · -- `σ = true` (cap)
    have h' : IsCap (Finset.image x Finset.univ) := h
    have hc := pvCross_neg_of_isCap h' (mem a) (mem b) (mem c) (hmono hab)
      (hmono hbc)
    rw [show pvSgn true = (1 : ℝ) from rfl]
    linarith

/-- In a `pvShaped` chain the `pvSgn`-scaled edge slopes strictly decrease
with the edge index (concavity of cap / convexity of cup slopes). -/
private lemma pvSl_edge {k : ℕ} {x : Fin (k + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (x i) 0) {σ : Bool} (hshape : pvShaped x σ)
    {a b : ℕ} (hab : a < b) (hb : b + 1 ≤ k) :
    pvSgn σ * pvSl (x ⟨b, by omega⟩) (x ⟨b + 1, by omega⟩) <
      pvSgn σ * pvSl (x ⟨a, by omega⟩) (x ⟨a + 1, by omega⟩) := by
  set u := x ⟨a, by omega⟩ with hu
  set u' := x ⟨a + 1, by omega⟩ with hu'
  set z := x ⟨b, by omega⟩ with hz
  set w := x ⟨b + 1, by omega⟩ with hw
  have muu' : (u : Euc 2) 0 < (u' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have muw : (u : Euc 2) 0 < (w : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have mzw : (z : Euc 2) 0 < (w : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have h1 : pvSgn σ * pvCross u u' w < 0 :=
    hshape ⟨a, by omega⟩ ⟨a + 1, by omega⟩ ⟨b + 1, by omega⟩
      (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
  have key1 : pvSgn σ * (pvSl u w - pvSl u u') < 0 := by
    rw [pvCross_eq_mid muu' muw] at h1
    exact pv_mul_neg_of_pos_factor (mul_pos (sub_pos.mpr muu') (sub_pos.mpr muw)) h1
  have h2 : pvSgn σ * pvCross u z w < 0 :=
    hshape ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨b + 1, by omega⟩
      (Fin.mk_lt_mk.mpr hab) (Fin.mk_lt_mk.mpr (by omega))
  have key2 : pvSgn σ * (pvSl z w - pvSl u w) < 0 := by
    rw [pvCross_eq_left mzw muw] at h2
    exact pv_mul_neg_of_pos_factor (mul_pos (sub_pos.mpr mzw) (sub_pos.mpr muw)) h2
  linarith

/-- The first defining half-plane of a support region: `p` is strictly on
the interior side of its own edge line. -/
private lemma mem_supportOf_inner {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
    {j : Fin k} {p : Euc 2} (hp : p ∈ supportOf x σ j) :
    0 < pvSgn σ * pvCross (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) p :=
  (mem_supportOf_iff.mp hp).1

/-- The second defining half-plane, specialized to `j ≥ 1`: `p` is on the
interior side of the previous edge line `x_{j-1} xⱼ`. -/
private lemma mem_supportOf_left {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
    {j : Fin k} {p : Euc 2} (hp : p ∈ supportOf x σ j) (hj : 1 ≤ j.val) :
    pvSgn σ * pvCross (x ⟨j.val - 1, by omega⟩) (x ⟨j.val, by omega⟩) p < 0 := by
  have h := (mem_supportOf_iff.mp hp).2.1
  have e : (⟨(j.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
      ⟨j.val - 1, by omega⟩ :=
    Fin.ext_iff.mpr (show (j.val + k) % (k + 1) = j.val - 1 by
      rw [show j.val + k = j.val - 1 + (k + 1) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)])
  rw [e] at h
  exact h

/-- The third defining half-plane, specialized to `j + 2 ≤ k`: `p` is on the
interior side of the next edge line `x_{j+1} x_{j+2}`. -/
private lemma mem_supportOf_right {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
    {j : Fin k} {p : Euc 2} (hp : p ∈ supportOf x σ j) (hj : j.val + 2 ≤ k) :
    pvSgn σ * pvCross (x ⟨j.val + 1, by omega⟩) (x ⟨j.val + 2, by omega⟩) p < 0 := by
  have h := (mem_supportOf_iff.mp hp).2.2
  have e : (⟨(j.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
      ⟨j.val + 2, by omega⟩ := Fin.ext_iff.mpr (Nat.mod_eq_of_lt (by omega))
  rw [e] at h
  exact h

/-- **Key geometric lemma**: in a shaped left-to-right chain, the support
region `Tⱼ` lies strictly on the interior side of every *other* edge line
`xᵢxᵢ₊₁`.

For `i < j` the argument is: `p ∈ Tⱼ` lies below (in `ε`-sense) the previous
edge line `x_{j-1}xⱼ` and above the own edge line `xⱼxⱼ₊₁`; since
`ε·(s_{j-1} - sⱼ) > 0` the two lines meet strictly left of `p`, i.e.
`xⱼ₀ < p₀`.  The line `xᵢxᵢ₊₁` passes above `xⱼ` and has larger scaled slope
than `x_{j-1}xⱼ`, so it dominates `x_{j-1}xⱼ`'s height on all of
`[xⱼ₀, p₀]` — in particular it is above `p`.  The case `i > j` is the mirror
image. -/
private theorem pv_region_inner_side {k : ℕ} {x : Fin (k + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (x i) 0) {σ : Bool} (hshape : pvShaped x σ)
    {i j : Fin k} (hij : i ≠ j) {p : Euc 2} (hp : p ∈ supportOf x σ j) :
    pvSgn σ * pvCross (x ⟨i.val, by omega⟩) (x ⟨i.val + 1, by omega⟩) p < 0 := by
  have hA : 0 < pvSgn σ * pvCross (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) p :=
    (mem_supportOf_iff.mp hp).1
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · -- `i < j`: the previous edge `x_{j-1} xⱼ` bounds `Tⱼ` from below
    have hB : pvSgn σ * pvCross (x ⟨j.val - 1, by omega⟩) (x ⟨j.val, by omega⟩) p < 0 :=
      mem_supportOf_left hp (by omega)
    by_cases hjj : i.val + 1 = j.val
    · -- the previous edge IS the `i`-th edge
      have e1 : (⟨i.val, by omega⟩ : Fin (k + 1)) = ⟨j.val - 1, by omega⟩ :=
        Fin.ext_iff.mpr (show i.val = j.val - 1 by omega)
      have e2 : (⟨i.val + 1, by omega⟩ : Fin (k + 1)) = ⟨j.val, by omega⟩ :=
        Fin.ext_iff.mpr (show i.val + 1 = j.val by omega)
      rw [e1, e2]
      exact hB
    · -- `i + 1 < j`: apex bound then height domination
      set u := x ⟨i.val, by omega⟩ with hu
      set u' := x ⟨i.val + 1, by omega⟩ with hu'
      set z := x ⟨j.val - 1, by omega⟩ with hz
      set w := x ⟨j.val, by omega⟩ with hw
      set w' := x ⟨j.val + 1, by omega⟩ with hw'
      have hzw : (z : Euc 2) 0 < (w : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have hww' : (w : Euc 2) 0 < (w' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have huu' : (u : Euc 2) 0 < (u' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have hB1 : pvSgn σ * (p 1 - pvHgt z w (p 0)) < 0 := by
        rw [pvCross_eq_hgt (ne_of_gt hzw)] at hB
        exact pv_mul_neg_of_pos_factor (sub_pos.mpr hzw) hB
      have hA1 : 0 < pvSgn σ * (p 1 - pvHgt w w' (p 0)) := by
        rw [pvCross_eq_hgt (ne_of_gt hww')] at hA
        exact pv_mul_pos_of_pos_factor (sub_pos.mpr hww') hA
      -- wedge bound: `p` is strictly to the right of the apex `w`
      have hpx : (w : Euc 2) 0 < p 0 := by
        have hB1w : pvSgn σ * (p 1 - (w 1 + pvSl z w * (p 0 - w 0))) < 0 := by
          have h := hB1
          rw [pvHgt_at_right (ne_of_gt hzw)] at h
          exact h
        have hA1w : 0 < pvSgn σ * (p 1 - (w 1 + pvSl w w' * (p 0 - w 0))) := hA1
        have hsl : 0 < pvSgn σ * (pvSl z w - pvSl w w') := by
          have h' := pvSl_edge hmono hshape (show j.val - 1 < j.val by omega)
            (show j.val + 1 ≤ k by omega)
          have e : (⟨j.val - 1 + 1, by omega⟩ : Fin (k + 1)) = ⟨j.val, by omega⟩ :=
            Fin.ext_iff.mpr (show j.val - 1 + 1 = j.val by omega)
          rw [e] at h'
          have h : pvSgn σ * pvSl w w' < pvSgn σ * pvSl z w := h'
          linarith
        have hd : 0 < pvSgn σ * (pvSl z w - pvSl w w') * (p 0 - w 0) := by
          have e : pvSgn σ * (pvSl z w - pvSl w w') * (p 0 - w 0) =
              pvSgn σ * (p 1 - (w 1 + pvSl w w' * (p 0 - w 0))) -
              pvSgn σ * (p 1 - (w 1 + pvSl z w * (p 0 - w 0))) := by ring
          rw [e]
          linarith
        exact sub_pos.mp (pos_of_mul_pos_right hd hsl.le)
      -- domination: the line `u u'` stays strictly above `z w`'s height on
      -- `[w₀, p₀]`
      have hdom : 0 < pvSgn σ * (pvHgt u u' (p 0) - pvHgt z w (p 0)) := by
        rw [pvHgt_affine u u' (p 0) (w 0), pvHgt_at_right (ne_of_gt hzw)]
        have hbase : 0 < pvSgn σ * (pvHgt u u' (w 0) - w 1) := by
          have hc : pvSgn σ * pvCross u u' w < 0 :=
            hshape ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ ⟨j.val, by omega⟩
              (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
          rw [pvCross_eq_hgt (ne_of_gt huu')] at hc
          have hlt' := pv_mul_neg_of_pos_factor (sub_pos.mpr huu') hc
          linarith
        have hslope : 0 < pvSgn σ * (pvSl u u' - pvSl z w) := by
          have h' := pvSl_edge hmono hshape (show i.val < j.val - 1 by omega)
            (show j.val - 1 + 1 ≤ k by omega)
          have e : (⟨j.val - 1 + 1, by omega⟩ : Fin (k + 1)) = ⟨j.val, by omega⟩ :=
            Fin.ext_iff.mpr (show j.val - 1 + 1 = j.val by omega)
          rw [e] at h'
          have h : pvSgn σ * pvSl z w < pvSgn σ * pvSl u u' := h'
          linarith
        have hprod : 0 ≤ pvSgn σ * (pvSl u u' - pvSl z w) * (p 0 - w 0) :=
          mul_nonneg hslope.le (sub_nonneg.mpr hpx.le)
        have e : pvSgn σ * (pvHgt u u' (w 0) + pvSl u u' * (p 0 - w 0) -
            (w 1 + pvSl z w * (p 0 - w 0))) =
            pvSgn σ * (pvHgt u u' (w 0) - w 1) +
              pvSgn σ * (pvSl u u' - pvSl z w) * (p 0 - w 0) := by ring
        rw [e]
        linarith
      -- assemble: `ε·(p₁ - hᵢ(p₀)) < 0`, then unscale
      have key : pvSgn σ * (p 1 - pvHgt u u' (p 0)) < 0 := by
        have e : pvSgn σ * (p 1 - pvHgt u u' (p 0)) =
            pvSgn σ * (p 1 - pvHgt z w (p 0)) -
              pvSgn σ * (pvHgt u u' (p 0) - pvHgt z w (p 0)) := by ring
        rw [e]
        linarith
      rw [pvCross_eq_hgt (ne_of_gt huu')]
      have e : pvSgn σ * ((u' 0 - u 0) * (p 1 - pvHgt u u' (p 0))) =
          (u' 0 - u 0) * (pvSgn σ * (p 1 - pvHgt u u' (p 0))) := by ring
      rw [e]
      exact mul_neg_of_pos_of_neg (sub_pos.mpr huu') key
  · -- `i = j` is excluded
    exact absurd (Fin.ext_iff.mpr heq) hij
  · -- `i > j`: the next edge `x_{j+1} x_{j+2}` bounds `Tⱼ` from below
    have hC : pvSgn σ * pvCross (x ⟨j.val + 1, by omega⟩) (x ⟨j.val + 2, by omega⟩) p < 0 :=
      mem_supportOf_right hp (by omega)
    by_cases hjj : i.val = j.val + 1
    · -- the next edge IS the `i`-th edge
      have e1 : (⟨i.val, by omega⟩ : Fin (k + 1)) = ⟨j.val + 1, by omega⟩ :=
        Fin.ext_iff.mpr (show i.val = j.val + 1 by omega)
      have e2 : (⟨i.val + 1, by omega⟩ : Fin (k + 1)) = ⟨j.val + 2, by omega⟩ :=
        Fin.ext_iff.mpr (show i.val + 1 = j.val + 2 by omega)
      rw [e1, e2]
      exact hC
    · -- `i ≥ j + 2`: apex bound then height domination
      set u := x ⟨i.val, by omega⟩ with hu
      set u' := x ⟨i.val + 1, by omega⟩ with hu'
      set w := x ⟨j.val, by omega⟩ with hw
      set w' := x ⟨j.val + 1, by omega⟩ with hw'
      set w'' := x ⟨j.val + 2, by omega⟩ with hw''
      have huu' : (u : Euc 2) 0 < (u' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have hww' : (w : Euc 2) 0 < (w' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have hw'w'' : (w' : Euc 2) 0 < (w'' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have hA1 : 0 < pvSgn σ * (p 1 - pvHgt w w' (p 0)) := by
        rw [pvCross_eq_hgt (ne_of_gt hww')] at hA
        exact pv_mul_pos_of_pos_factor (sub_pos.mpr hww') hA
      have hC1 : pvSgn σ * (p 1 - pvHgt w' w'' (p 0)) < 0 := by
        rw [pvCross_eq_hgt (ne_of_gt hw'w'')] at hC
        exact pv_mul_neg_of_pos_factor (sub_pos.mpr hw'w'') hC
      -- wedge bound: `p` is strictly to the left of the apex `w'`
      have hpx : p 0 < (w' : Euc 2) 0 := by
        have hA1w : 0 < pvSgn σ * (p 1 - (w' 1 + pvSl w w' * (p 0 - w' 0))) := by
          have h := hA1
          rw [pvHgt_at_right (ne_of_gt hww')] at h
          exact h
        have hC1w : pvSgn σ * (p 1 - (w' 1 + pvSl w' w'' * (p 0 - w' 0))) < 0 := hC1
        have hsl : 0 < pvSgn σ * (pvSl w w' - pvSl w' w'') := by
          have h : pvSgn σ * pvSl w' w'' < pvSgn σ * pvSl w w' :=
            pvSl_edge hmono hshape (show j.val < j.val + 1 by omega)
              (show j.val + 1 + 1 ≤ k by omega)
          linarith
        have hd : pvSgn σ * (pvSl w w' - pvSl w' w'') * (p 0 - w' 0) < 0 := by
          have e : pvSgn σ * (pvSl w w' - pvSl w' w'') * (p 0 - w' 0) =
              pvSgn σ * (p 1 - (w' 1 + pvSl w' w'' * (p 0 - w' 0))) -
              pvSgn σ * (p 1 - (w' 1 + pvSl w w' * (p 0 - w' 0))) := by ring
          rw [e]
          linarith
        exact sub_neg.mp (Right.neg_of_mul_neg_right hd hsl.le)
      -- domination: the line `u u'` stays strictly above `w' w''`'s height on
      -- `[p₀, w'₀]`
      have hdom : 0 < pvSgn σ * (pvHgt u u' (p 0) - pvHgt w' w'' (p 0)) := by
        rw [pvHgt_affine u u' (p 0) (w' 0),
          show pvHgt w' w'' (p 0) = w' 1 + pvSl w' w'' * (p 0 - w' 0) from rfl]
        have hbase : 0 < pvSgn σ * (pvHgt u u' (w' 0) - w' 1) := by
          have hc : pvSgn σ * pvCross u u' w' < 0 := by
            have h := hshape ⟨j.val + 1, by omega⟩ ⟨i.val, by omega⟩
              ⟨i.val + 1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
              (Fin.mk_lt_mk.mpr (by omega))
            rwa [pvCross_cyc] at h
          rw [pvCross_eq_hgt (ne_of_gt huu')] at hc
          have hlt' := pv_mul_neg_of_pos_factor (sub_pos.mpr huu') hc
          linarith
        have hslope : pvSgn σ * (pvSl u u' - pvSl w' w'') < 0 := by
          have h : pvSgn σ * pvSl u u' < pvSgn σ * pvSl w' w'' :=
            pvSl_edge hmono hshape (show j.val + 1 < i.val by omega)
              (show i.val + 1 ≤ k by omega)
          linarith
        have hprod : 0 ≤ pvSgn σ * (pvSl u u' - pvSl w' w'') * (p 0 - w' 0) :=
          mul_nonneg_of_nonpos_of_nonpos hslope.le (sub_nonpos.mpr hpx.le)
        have e : pvSgn σ * (pvHgt u u' (w' 0) + pvSl u u' * (p 0 - w' 0) -
            (w' 1 + pvSl w' w'' * (p 0 - w' 0))) =
            pvSgn σ * (pvHgt u u' (w' 0) - w' 1) +
              pvSgn σ * (pvSl u u' - pvSl w' w'') * (p 0 - w' 0) := by ring
        rw [e]
        linarith
      have key : pvSgn σ * (p 1 - pvHgt u u' (p 0)) < 0 := by
        have e : pvSgn σ * (p 1 - pvHgt u u' (p 0)) =
            pvSgn σ * (p 1 - pvHgt w' w'' (p 0)) -
              pvSgn σ * (pvHgt u u' (p 0) - pvHgt w' w'' (p 0)) := by ring
        rw [e]
        linarith
      rw [pvCross_eq_hgt (ne_of_gt huu')]
      have e : pvSgn σ * ((u' 0 - u 0) * (p 1 - pvHgt u u' (p 0))) =
          (u' 0 - u 0) * (pvSgn σ * (p 1 - pvHgt u u' (p 0))) := by ring
      rw [e]
      exact mul_neg_of_pos_of_neg (sub_pos.mpr huu') key

/-- Coordinate evaluation of a weighted sum of points. -/
private lemma pv_sum_eval {S : Finset (Euc 2)} (w : Euc 2 → ℝ) (μ : Fin 2) :
    (∑ y ∈ S, w y • y) μ = ∑ y ∈ S, w y * (y μ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply,
        PiLp.smul_apply, ih, smul_eq_mul]

/-- **Transversal convexity** — the self-contained geometric clause of the
Pór–Valtr theorem: choosing one point `Y i` from each support region of a
shaped `(k+1)`-chain produces a set in convex position, since the `i`-th
edge line strictly separates `Y i` from every other `Y j`. -/
private theorem pv_transversal_convex {k : ℕ} {x : Fin (k + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (x i) 0) {σ : Bool} (hshape : pvShaped x σ)
    {Y : Fin k → Euc 2} (hY : ∀ i, Y i ∈ supportOf x σ i) :
    InConvexPosition (Finset.image Y Finset.univ) := by
  intro z hz hconv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  set ε := pvSgn σ with hε
  set u : Euc 2 := x ⟨i.val, by omega⟩ with hu
  set v : Euc 2 := x ⟨i.val + 1, by omega⟩ with hv
  have hpos : 0 < ε * pvCross u v (Y i) := mem_supportOf_inner (hY i)
  have hneg : ∀ j : Fin k, j ≠ i → ε * pvCross u v (Y j) < 0 :=
    fun j hji ↦ pv_region_inner_side hmono hshape hji.symm (hY j)
  have hS' : ∀ y ∈ Finset.image Y (Finset.univ.erase i), ε * pvCross u v y < 0 := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hneg j (Finset.ne_of_mem_erase hj)
  have hsub : (Finset.image Y Finset.univ).erase (Y i) ⊆
      Finset.image Y (Finset.univ.erase i) := by
    intro y hy
    rw [Finset.mem_erase] at hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy.2
    have hji : j ≠ i := fun e ↦ hy.1 (congrArg Y e)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, rfl⟩
  have hconv' : Y i ∈ convexHull ℝ
      (↑(Finset.image Y (Finset.univ.erase i)) : Set (Euc 2)) :=
    convexHull_mono (Finset.coe_subset.mpr hsub) hconv
  rw [Finset.mem_convexHull] at hconv'
  obtain ⟨w, hw0, hw1, hwcm⟩ := hconv'
  have Laff : ∀ q : Euc 2, ε * pvCross u v q =
      (-ε * (v 1 - u 1)) * q 0 + (ε * (v 0 - u 0)) * q 1 +
        ε * ((v 1 - u 1) * u 0 - (v 0 - u 0) * u 1) := fun q ↦ by
    unfold pvCross; ring
  have key : ε * pvCross u v (Y i) =
      ∑ y ∈ Finset.image Y (Finset.univ.erase i), w y * (ε * pvCross u v y) := by
    rw [← hwcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]
    simp only [id_eq]
    rw [Laff, pv_sum_eval w 0, pv_sum_eval w 1]
    have hC : ε * ((v 1 - u 1) * u 0 - (v 0 - u 0) * u 1) =
        ∑ y ∈ Finset.image Y (Finset.univ.erase i),
          w y * (ε * ((v 1 - u 1) * u 0 - (v 0 - u 0) * u 1)) := by
      rw [← Finset.sum_mul, hw1, one_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, hC,
      ← Finset.sum_add_distrib]
    trans ∑ y ∈ Finset.image Y (Finset.univ.erase i),
        w y * ((-ε * (v 1 - u 1)) * y 0 + (ε * (v 0 - u 0)) * y 1 +
          ε * ((v 1 - u 1) * u 0 - (v 0 - u 0) * u 1))
    · exact Finset.sum_congr rfl fun y _ ↦ by ring
    · exact Finset.sum_congr rfl fun y _ ↦ by rw [Laff]
  have hterm : ∀ y ∈ Finset.image Y (Finset.univ.erase i),
      w y * (ε * pvCross u v y) ≤ 0 :=
    fun y hy ↦ mul_nonpos_of_nonneg_of_nonpos (hw0 y hy) (hS' y hy).le
  obtain ⟨y₀, hy₀, hwy₀⟩ : ∃ y ∈ Finset.image Y (Finset.univ.erase i), 0 < w y := by
    by_contra hcon
    have hcon' : ∀ y ∈ Finset.image Y (Finset.univ.erase i), w y ≤ 0 :=
      fun y hy ↦ le_of_not_gt fun hlt ↦ hcon ⟨y, hy, hlt⟩
    have hzero : ∑ y ∈ Finset.image Y (Finset.univ.erase i), w y = 0 :=
      Finset.sum_eq_zero fun y hy ↦ le_antisymm (hcon' y hy) (hw0 y hy)
    linarith
  have hstrict : ∑ y ∈ Finset.image Y (Finset.univ.erase i), w y * (ε * pvCross u v y) <
      ∑ y ∈ Finset.image Y (Finset.univ.erase i), (0 : ℝ) :=
    Finset.sum_lt_sum hterm ⟨y₀, hy₀, mul_neg_of_pos_of_neg hwy₀ (hS' y₀ hy₀)⟩
  rw [Finset.sum_const_zero, ← key] at hstrict
  linarith

/-- **Pór–Valtr existence core** — the full mathematical content of
Theorem 2.2 of Pohoata–Zakharov (which is [PV02, Theorem 4] as restated by
Suk): a left-to-right `(k+1)`-cap or `(k+1)`-cup `x₀,…,x_k ⊆ X` whose `k`
support regions each contain a `≥ 2^{-40k}`-fraction of `X`, such that every
transversal (one point of `X` per region) is in convex position.

Mathematical gap: this is the research-level positive-fraction
Erdős–Szekeres theorem.  The published proof runs through a fractional
cups–caps/projective argument; a plausible Lean route starts from
`cupsCaps` (Theorem 2.1) applied iteratively to extract a long cap/cup whose
support regions must be dense (a sparse region would allow lengthening the
polygon), but making the density quantitative at `2^{-40k}` and the
transversal-convexity clause rigorous is the content of [PV02].

(The formalized `SupportRegion` has been corrected to the paper's triangular
region — third conjunct `if σ then RightOf xᵢ₁ r else LeftOf xᵢ₁ r` — so this
lemma is the honest remaining gap of Theorem 2.2.) -/
theorem porValtr_dense_support {k : ℕ} (hk : 3 ≤ k)
    {X : Finset (Euc 2)} (hX : InGeneralPosition (X : Set (Euc 2))) (hdx : DistinctX X)
    (hcard : 2 ^ (40 * k) ≤ X.card) :
    ∃ x : Fin (k + 1) → Euc 2, ∃ σ : Bool,
      (∀ i, x i ∈ X) ∧
      StrictMono (fun i ↦ (x i) 0) ∧
      (if σ then IsCap (Finset.image x Finset.univ)
             else IsCup (Finset.image x Finset.univ)) ∧
      (∀ i : Fin k, 2 ^ (40 * k) * (supportOf x σ i ∩ (X : Set (Euc 2))).ncard ≥ X.card) ∧
      (∀ Y : Fin k → Euc 2, (∀ i, Y i ∈ supportOf x σ i ∩ (X : Set (Euc 2))) →
        InConvexPosition (Finset.image Y Finset.univ)) := by
  -- The remaining gap is purely the *existence* of a dense-supported
  -- cap/cup: the research-level content of [PV02, Theorem 4] (fractional /
  -- iterated cups–caps argument with the quantitative `2^{-40k}` density).
  obtain ⟨x, σ, hxX, hmono, hcapcup, hdense⟩ :
      ∃ x : Fin (k + 1) → Euc 2, ∃ σ : Bool,
        (∀ i, x i ∈ X) ∧ StrictMono (fun i ↦ (x i) 0) ∧
        (if σ then IsCap (Finset.image x Finset.univ)
               else IsCup (Finset.image x Finset.univ)) ∧
        (∀ i : Fin k,
          2 ^ (40 * k) * (supportOf x σ i ∩ (X : Set (Euc 2))).ncard ≥ X.card) := by
    sorry
  -- The transversal-convexity clause is fully proved: `pv_transversal_convex`.
  exact ⟨x, σ, hxX, hmono, hcapcup, hdense, fun Y hY ↦
    pv_transversal_convex hmono (pvShaped_of_capOrCup hmono hcapcup)
      fun i ↦ (hY i).1⟩

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
  obtain ⟨x, σ, hxX, hmono, hshape, hdense, hconv⟩ :=
    porValtr_dense_support hk hX hdx hcard
  exact ⟨x, σ, fun i ↦ supportOf x σ i, hxX, hmono, hshape, fun _ ↦ rfl,
    hdense, fun Y hY ↦ hconv Y hY⟩

end
