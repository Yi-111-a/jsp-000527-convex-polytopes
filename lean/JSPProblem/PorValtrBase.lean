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
abbrev supportOf {k : ℕ} (x : Fin (k + 1) → Euc 2) (σ : Bool) (i : Fin k) :
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

def pvPt (a b : ℝ) : Euc 2 := WithLp.toLp 2 ![a, b]

@[simp] lemma pvPt0 (a b : ℝ) : pvPt a b 0 = a := rfl
@[simp] lemma pvPt1 (a b : ℝ) : pvPt a b 1 = b := rfl

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
def pvCross (u v w : Euc 2) : ℝ :=
  (v 0 - u 0) * (w 1 - u 1) - (v 1 - u 1) * (w 0 - u 0)

/-- The slope of the directed segment `u v`. -/
noncomputable def pvSl (u v : Euc 2) : ℝ := (v 1 - u 1) / (v 0 - u 0)

/-- The height at abscissa `t` of the line through `u` and `v`. -/
noncomputable def pvHgt (u v : Euc 2) (t : ℝ) : ℝ :=
  u 1 + pvSl u v * (t - u 0)

/-- The sign distinguishing cap (`σ = true`, `ε = 1`) from cup
(`σ = false`, `ε = -1`) in the uniform statements. -/
def pvSgn (σ : Bool) : ℝ := if σ then 1 else -1

lemma pvCross_self (u v : Euc 2) : pvCross u u v = 0 := by
  unfold pvCross; ring

lemma pvCross_left (u v : Euc 2) : pvCross u v u = 0 := by
  unfold pvCross; ring

lemma pvCross_right (u v : Euc 2) : pvCross u v v = 0 := by
  unfold pvCross; ring

lemma pvCross_swap (u v w : Euc 2) : pvCross v u w = -pvCross u v w := by
  unfold pvCross; ring

lemma pvCross_cyc (u v w : Euc 2) : pvCross u v w = pvCross v w u := by
  unfold pvCross; ring

lemma mem_LeftOf_iff (u v p : Euc 2) : p ∈ LeftOf u v ↔ 0 < pvCross u v p :=
  Iff.rfl

lemma mem_RightOf_iff (u v p : Euc 2) : p ∈ RightOf u v ↔ pvCross u v p < 0 := by
  show 0 < pvCross v u p ↔ pvCross u v p < 0
  rw [pvCross_swap]; constructor <;> intro h <;> linarith

/-- Membership in a support region, expressed uniformly in `σ` as sign
conditions on `pvCross`. -/
lemma mem_supportOf_iff {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
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
lemma pvCross_eq_hgt {u v : Euc 2} (h : v 0 ≠ u 0) (p : Euc 2) :
    pvCross u v p = (v 0 - u 0) * (p 1 - pvHgt u v (p 0)) := by
  unfold pvCross pvHgt pvSl
  field_simp
  ring

/-- The height function recomputed at the right endpoint. -/
lemma pvHgt_at_right {u v : Euc 2} (h : v 0 ≠ u 0) (t : ℝ) :
    pvHgt u v t = v 1 + pvSl u v * (t - v 0) := by
  unfold pvHgt pvSl
  field_simp
  ring

/-- The height function is affine in `t` with slope `pvSl u v`. -/
lemma pvHgt_affine (u v : Euc 2) (t t₀ : ℝ) :
    pvHgt u v t = pvHgt u v t₀ + pvSl u v * (t - t₀) := by
  unfold pvHgt; ring

/-- From the cup/cap condition: in a cap every increasing-`x` triple has
negative signed area (and the mirror statement for cups). -/
lemma pvCross_neg_of_isCap {P : Finset (Euc 2)} (hP : IsCap P)
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
lemma pvCross_pos_of_isCup {P : Finset (Euc 2)} (hP : IsCup P)
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
lemma pvCross_eq_mid {u v w : Euc 2} (huv : u 0 < v 0) (huw : u 0 < w 0) :
    pvCross u v w = (v 0 - u 0) * (w 0 - u 0) * (pvSl u w - pvSl u v) := by
  unfold pvCross pvSl
  have h1 : v 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have h2 : w 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huw)
  field_simp

/-- The signed area factors through a slope difference (second edge vs.
chord). -/
lemma pvCross_eq_left {u v w : Euc 2} (hvw : v 0 < w 0) (huw : u 0 < w 0) :
    pvCross u v w = (w 0 - v 0) * (w 0 - u 0) * (pvSl v w - pvSl u w) := by
  unfold pvCross pvSl
  have h1 : w 0 - v 0 ≠ 0 := ne_of_gt (sub_pos.mpr hvw)
  have h2 : w 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huw)
  field_simp
  ring

/-- Cancelling a positive middle factor inside a `pvSgn`-scaled product. -/
lemma pv_mul_neg_of_pos_factor {ε P c : ℝ} (hP : 0 < P) (h : ε * (P * c) < 0) :
    ε * c < 0 := by
  rw [mul_left_comm] at h
  exact Right.neg_of_mul_neg_right h hP.le

/-- Cancelling a positive middle factor inside a `pvSgn`-scaled product,
`0 <` version. -/
lemma pv_mul_pos_of_pos_factor {ε P c : ℝ} (hP : 0 < P) (h : 0 < ε * (P * c)) :
    0 < ε * c := by
  rw [mul_left_comm] at h
  exact pos_of_mul_pos_right h hP.le

/-- The cup/cap shape condition on a left-to-right chain, in uniform
`pvSgn`-scaled form: every increasing triple has interior-side signed
area. -/
def pvShaped {k : ℕ} (x : Fin (k + 1) → Euc 2) (σ : Bool) : Prop :=
  ∀ a b c : Fin (k + 1), a < b → b < c → pvSgn σ * pvCross (x a) (x b) (x c) < 0

lemma pvShaped_of_capOrCup {k : ℕ} {x : Fin (k + 1) → Euc 2}
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
lemma pvSl_edge {k : ℕ} {x : Fin (k + 1) → Euc 2}
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
lemma mem_supportOf_inner {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
    {j : Fin k} {p : Euc 2} (hp : p ∈ supportOf x σ j) :
    0 < pvSgn σ * pvCross (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) p :=
  (mem_supportOf_iff.mp hp).1

/-- The second defining half-plane, specialized to `j ≥ 1`: `p` is on the
interior side of the previous edge line `x_{j-1} xⱼ`. -/
lemma mem_supportOf_left {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
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
lemma mem_supportOf_right {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
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
theorem pv_region_inner_side {k : ℕ} {x : Fin (k + 1) → Euc 2}
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
lemma pv_sum_eval {S : Finset (Euc 2)} (w : Euc 2 → ℝ) (μ : Fin 2) :
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
theorem pv_transversal_convex {k : ℕ} {x : Fin (k + 1) → Euc 2}
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

/-! ### Slope and height comparisons in a shaped chain

The remaining gap of `porValtr_dense_support` is the *existence* of a
`(k+1)`-cap/cup whose support regions each contain a `2^{-40k}`-fraction of
`X`.  We follow the proof of [PV02, Theorem 4] (as used by Suk for the
cap/cup formulation): a long cap/cup `y : Fin (2k+1) → X` has `2k` support
regions, at least `k` of which are dense by a double-counting argument, and
the sub-chain `x` picking the left endpoints of the dense regions (plus the
last point `y_{2k}`) has its support regions containing the dense ones.

This section collects the uniform (`pvSgn`-scaled) line comparisons. -/

lemma pvSgn_ne_zero (σ : Bool) : pvSgn σ ≠ 0 := by
  cases σ <;> simp [pvSgn]

lemma pvSgn_sq (σ : Bool) : pvSgn σ * pvSgn σ = 1 := by
  cases σ <;> simp [pvSgn]

lemma pvSgn_eq_or (σ : Bool) : pvSgn σ = 1 ∨ pvSgn σ = -1 := by
  cases σ <;> simp [pvSgn]

/-- Swapping the last two arguments of `pvCross` flips the sign. -/
lemma pvCross_swap23 (u v w : Euc 2) : pvCross u w v = -pvCross u v w := by
  unfold pvCross; ring

/-- In a shaped chain, for `a < b < c` the chord slope `y_a y_c` is
`ε`-smaller than the first edge slope `y_a y_b`. -/
lemma pvSl_chord_left {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a b c : Fin (m + 1)} (hab : a < b) (hbc : b < c) :
    pvSgn σ * pvSl (y a) (y c) < pvSgn σ * pvSl (y a) (y b) := by
  have hab0 : (y a) 0 < (y b) 0 := hmono hab
  have hac0 : (y a) 0 < (y c) 0 := hmono (hab.trans hbc)
  have hc : pvSgn σ * pvCross (y a) (y b) (y c) < 0 := hshape a b c hab hbc
  rw [pvCross_eq_mid hab0 hac0] at hc
  have hpos : (0:ℝ) < ((y b) 0 - (y a) 0) * ((y c) 0 - (y a) 0) :=
    mul_pos (sub_pos.mpr hab0) (sub_pos.mpr hac0)
  have h := pv_mul_neg_of_pos_factor hpos hc
  linarith

/-- In a shaped chain, for `a < b < c` the slope into `c` from the later
point `b` is `ε`-smaller than the slope from `a`. -/
lemma pvSl_chord_right {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a b c : Fin (m + 1)} (hab : a < b) (hbc : b < c) :
    pvSgn σ * pvSl (y b) (y c) < pvSgn σ * pvSl (y a) (y c) := by
  have hab0 : (y a) 0 < (y b) 0 := hmono hab
  have hbc0 : (y b) 0 < (y c) 0 := hmono hbc
  have hac0 : (y a) 0 < (y c) 0 := hmono (hab.trans hbc)
  have hc : pvSgn σ * pvCross (y a) (y b) (y c) < 0 := hshape a b c hab hbc
  rw [pvCross_eq_left hbc0 hac0] at hc
  have hpos : (0:ℝ) < ((y c) 0 - (y b) 0) * ((y c) 0 - (y a) 0) :=
    mul_pos (sub_pos.mpr hbc0) (sub_pos.mpr hac0)
  have h := pv_mul_neg_of_pos_factor hpos hc
  linarith

/-- `pvCross` sign is the sign of the height difference (for `u 0 < v 0`). -/
lemma pv_cross_hgt_sign {u v p : Euc 2} (huv : u 0 < v 0) :
    pvSgn σ * pvCross u v p = (v 0 - u 0) * (pvSgn σ * (p 1 - pvHgt u v (p 0))) := by
  rw [pvCross_eq_hgt (ne_of_gt huv)]; ring

/-- Variant of `pv_mul_neg_of_pos_factor` with the positive factor outside
the `ε`-scaled term. -/
lemma pv_mul_neg_of_pos_out {ε P c : ℝ} (hP : 0 < P)
    (h : P * (ε * c) < 0) : ε * c < 0 :=
  pv_mul_neg_of_pos_factor hP (by rwa [mul_left_comm])

/-- Variant of `pv_mul_pos_of_pos_factor` with the positive factor outside
the `ε`-scaled term. -/
lemma pv_mul_pos_of_pos_out {ε P c : ℝ} (hP : 0 < P)
    (h : 0 < P * (ε * c)) : 0 < ε * c :=
  pv_mul_pos_of_pos_factor hP (by rwa [mul_left_comm])

/-- A vertex `y_c` lying outside the index interval `[a,b]` is `ε`-below the
line through `y_a y_b` (the line is `ε`-above the vertex). -/
lemma pv_hgt_above_vertex {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a b c : Fin (m + 1)} (hab : a < b) (hc : c < a ∨ b < c) :
    pvSgn σ * ((y c) 1) < pvSgn σ * pvHgt (y a) (y b) ((y c) 0) := by
  have hab0 : (y a) 0 < (y b) 0 := hmono hab
  have hc' : pvSgn σ * pvCross (y a) (y b) (y c) < 0 := by
    rcases hc with hca | hbc
    · have h := hshape c a b hca hab
      rwa [pvCross_cyc] at h
    · exact hshape a b c hab hbc
  rw [pv_cross_hgt_sign hab0] at hc'
  have h := pv_mul_neg_of_pos_out (sub_pos.mpr hab0) hc'
  linarith

/-- A vertex `y_c` strictly between `a` and `b` lies `ε`-above the chord
`y_a y_b`. -/
lemma pv_hgt_below_vertex {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a b c : Fin (m + 1)} (hac : a < c) (hcb : c < b) :
    pvSgn σ * pvHgt (y a) (y b) ((y c) 0) < pvSgn σ * ((y c) 1) := by
  have hab : a < b := hac.trans hcb
  have hab0 : (y a) 0 < (y b) 0 := hmono hab
  have hc : pvSgn σ * pvCross (y a) (y c) (y b) < 0 := hshape a c b hac hcb
  have hc' : 0 < pvSgn σ * pvCross (y a) (y b) (y c) := by
    have e := pvCross_swap23 (y a) (y c) (y b)
    have e2 : pvSgn σ * pvCross (y a) (y b) (y c) =
        -(pvSgn σ * pvCross (y a) (y c) (y b)) := by rw [e]; ring
    linarith
  rw [pv_cross_hgt_sign hab0] at hc'
  have h := pv_mul_pos_of_pos_out (sub_pos.mpr hab0) hc'
  linarith

/-- Sharing the left endpoint `y a`: for `b < c`, the line `y_a y_c` is
`ε`-below the line `y_a y_b` to the right of `a`. -/
lemma pv_hgt_le_of_lt_right {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a b c : Fin (m + 1)} (hab : a < b) (hbc : b < c) {t : ℝ}
    (ht : (y a) 0 ≤ t) :
    pvSgn σ * pvHgt (y a) (y c) t ≤ pvSgn σ * pvHgt (y a) (y b) t := by
  have hs := pvSl_chord_left hmono hshape hab hbc
  have hd : pvHgt (y a) (y b) t - pvHgt (y a) (y c) t =
      (pvSl (y a) (y b) - pvSl (y a) (y c)) * (t - (y a) 0) := by
    unfold pvHgt; ring
  have hprod : (0:ℝ) ≤ pvSgn σ * (pvSl (y a) (y b) - pvSl (y a) (y c)) * (t - (y a) 0) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr ht)
  have e : pvSgn σ * (pvHgt (y a) (y b) t - pvHgt (y a) (y c) t) =
      pvSgn σ * (pvSl (y a) (y b) - pvSl (y a) (y c)) * (t - (y a) 0) := by
    rw [hd]; ring
  linarith

/-- Sharing the left endpoint `y a` with equality of right endpoints
allowed: weak version where the second line may coincide. -/
lemma pv_hgt_le_of_le_right {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a b c : Fin (m + 1)} (hab : a < b) (hbc : b ≤ c) {t : ℝ}
    (ht : (y a) 0 ≤ t) :
    pvSgn σ * pvHgt (y a) (y c) t ≤ pvSgn σ * pvHgt (y a) (y b) t := by
  rcases eq_or_lt_of_le hbc with rfl | hbc
  · simp
  · exact pv_hgt_le_of_lt_right hmono hshape hab hbc ht

/-- Sharing the right endpoint `y c`: for `a < b`, the line `y_a y_c` is
`ε`-above the line `y_b y_c` to the right of `c`... i.e. to the left the
earlier-start line is `ε`-below. -/
lemma pv_hgt_le_of_lt_left {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a b c : Fin (m + 1)} (hab : a < b) (hbc : b < c) {t : ℝ}
    (ht : t ≤ (y c) 0) :
    pvSgn σ * pvHgt (y a) (y c) t ≤ pvSgn σ * pvHgt (y b) (y c) t := by
  have hbc0 : (y b) 0 < (y c) 0 := hmono hbc
  have hs := pvSl_chord_right hmono hshape hab hbc
  have hd : pvHgt (y b) (y c) t - pvHgt (y a) (y c) t =
      (pvSl (y b) (y c) - pvSl (y a) (y c)) * (t - (y c) 0) := by
    rw [pvHgt_at_right (ne_of_gt hbc0), pvHgt_at_right (ne_of_gt ((hmono hab).trans hbc0))]; ring
  have hprod : (0:ℝ) ≤ pvSgn σ * (pvSl (y b) (y c) - pvSl (y a) (y c)) * (t - (y c) 0) := by
    have h1 : pvSgn σ * (pvSl (y b) (y c) - pvSl (y a) (y c)) < 0 := by linarith
    have h2 : t - (y c) 0 ≤ 0 := sub_nonpos.mpr ht
    exact mul_nonneg_of_nonpos_of_nonpos h1.le h2
  have e : pvSgn σ * (pvHgt (y b) (y c) t - pvHgt (y a) (y c) t) =
      pvSgn σ * (pvSl (y b) (y c) - pvSl (y a) (y c)) * (t - (y c) 0) := by
    rw [hd]; ring
  linarith

/-- Same shared-right-endpoint comparison to the *right* of `y_c`. -/
lemma pv_hgt_le_of_lt_left' {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a b c : Fin (m + 1)} (hab : a < b) (hbc : b < c) {t : ℝ}
    (ht : (y c) 0 ≤ t) :
    pvSgn σ * pvHgt (y b) (y c) t ≤ pvSgn σ * pvHgt (y a) (y c) t := by
  have hbc0 : (y b) 0 < (y c) 0 := hmono hbc
  have hac0 : (y a) 0 < (y c) 0 := hmono (hab.trans hbc)
  have hs := pvSl_chord_right hmono hshape hab hbc
  have hd : pvHgt (y a) (y c) t - pvHgt (y b) (y c) t =
      (pvSl (y a) (y c) - pvSl (y b) (y c)) * (t - (y c) 0) := by
    rw [pvHgt_at_right (ne_of_gt hac0), pvHgt_at_right (ne_of_gt hbc0)]; ring
  have hprod : (0:ℝ) ≤ pvSgn σ * (pvSl (y a) (y c) - pvSl (y b) (y c)) * (t - (y c) 0) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr ht)
  have e : pvSgn σ * (pvHgt (y a) (y c) t - pvHgt (y b) (y c) t) =
      pvSgn σ * (pvSl (y a) (y c) - pvSl (y b) (y c)) * (t - (y c) 0) := by
    rw [hd]; ring
  linarith

/-- Weak version of `pv_hgt_le_of_lt_left'` allowing `a = b`. -/
lemma pv_hgt_le_of_le_left' {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a b c : Fin (m + 1)} (hab : a ≤ b) (hbc : b < c) {t : ℝ}
    (ht : (y c) 0 ≤ t) :
    pvSgn σ * pvHgt (y b) (y c) t ≤ pvSgn σ * pvHgt (y a) (y c) t := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  · exact pv_hgt_le_of_lt_left' hmono hshape hab hbc ht

/-- An `ε`-affine function `ε`-positive at both endpoints of a closed
interval is `ε`-positive on the open interval. -/
lemma pv_affine_pos_of_pos {c0 c1 : ℝ} {ε : ℝ} {t lo hi : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hlo : lo < t) (hhi : t < hi)
    (f : ℝ → ℝ) (hf : ∀ s, f s = c0 + c1 * s)
    (h₁ : 0 < ε * f lo) (h₂ : 0 < ε * f hi) : 0 < ε * f t := by
  have hpos : (0:ℝ) < hi - lo := sub_pos.mpr (hlo.trans hhi)
  have hfrac : f t * (hi - lo) = (hi - t) * f lo + (t - lo) * f hi := by
    rw [hf t, hf lo, hf hi]; ring
  have hw1 : (0:ℝ) < hi - t := sub_pos.mpr hhi
  have hw2 : (0:ℝ) < t - lo := sub_pos.mpr hlo
  rcases hε with rfl | rfl
  · have h3 : (0:ℝ) < f lo := by linarith
    have h4 : (0:ℝ) < f hi := by linarith
    have h5 : (0:ℝ) < (hi - t) * f lo + (t - lo) * f hi :=
      add_pos (mul_pos hw1 h3) (mul_pos hw2 h4)
    have h6 : (0:ℝ) < f t := pos_of_mul_pos_right
      (show (0:ℝ) < (hi - lo) * f t by rw [mul_comm, hfrac]; exact h5) hpos.le
    linarith
  · have h3 : f lo < 0 := by linarith
    have h4 : f hi < 0 := by linarith
    have h5 : (hi - t) * f lo + (t - lo) * f hi < 0 :=
      add_neg (mul_neg_of_pos_of_neg hw1 h3) (mul_neg_of_pos_of_neg hw2 h4)
    have h6 : f t < 0 := by nlinarith
    linarith

/-- The line height function is symmetric in its two points (when they have
distinct first coordinates). -/
lemma pvHgt_comm {u v : Euc 2} (h : u 0 ≠ v 0) (t : ℝ) :
    pvHgt u v t = pvHgt v u t := by
  unfold pvHgt pvSl
  field_simp
  ring

/-- Evaluating a line at its left point. -/
lemma pvHgt_left_pt (u v : Euc 2) : pvHgt u v (u 0) = u 1 := by
  unfold pvHgt; simp

/-- `ε`-scaled cross is positive iff the point is `ε`-above the line. -/
lemma pv_cross_pos_iff {u v p : Euc 2} (huv : u 0 < v 0) :
    0 < pvSgn σ * pvCross u v p ↔ pvSgn σ * pvHgt u v (p 0) < pvSgn σ * p 1 := by
  rw [pv_cross_hgt_sign huv]
  constructor
  · intro h; have h2 := pv_mul_pos_of_pos_out (sub_pos.mpr huv) h; linarith
  · intro h; have h2 : 0 < pvSgn σ * (p 1 - pvHgt u v (p 0)) := by linarith
    exact mul_pos (sub_pos.mpr huv) h2

/-- `ε`-scaled cross is negative iff the point is `ε`-below the line. -/
lemma pv_cross_neg_iff {u v p : Euc 2} (huv : u 0 < v 0) :
    pvSgn σ * pvCross u v p < 0 ↔ pvSgn σ * p 1 < pvSgn σ * pvHgt u v (p 0) := by
  rw [pv_cross_hgt_sign huv]
  constructor
  · intro h; have h2 := pv_mul_neg_of_pos_out (sub_pos.mpr huv) h; linarith
  · intro h; have h2 : pvSgn σ * (p 1 - pvHgt u v (p 0)) < 0 := by linarith
    exact mul_neg_of_pos_of_neg (sub_pos.mpr huv) h2

/-- `ε`-scaled cross for a right-to-left segment is negative iff the point
is `ε`-above the line. -/
lemma pv_cross_neg_iff_rev {u v p : Euc 2} (hvu : v 0 < u 0) :
    pvSgn σ * pvCross u v p < 0 ↔ pvSgn σ * pvHgt u v (p 0) < pvSgn σ * p 1 := by
  rw [pvCross_eq_hgt (ne_of_lt hvu)]
  constructor
  · intro h
    have e : pvSgn σ * ((v 0 - u 0) * (p 1 - pvHgt u v (p 0))) =
        (v 0 - u 0) * (pvSgn σ * (p 1 - pvHgt u v (p 0))) := by ring
    have h3 := pos_of_mul_neg_right (e ▸ h) (sub_nonpos.mpr hvu.le)
    linarith
  · intro h
    have h2 : 0 < pvSgn σ * (p 1 - pvHgt u v (p 0)) := by linarith
    have e : pvSgn σ * ((v 0 - u 0) * (p 1 - pvHgt u v (p 0))) =
        (v 0 - u 0) * (pvSgn σ * (p 1 - pvHgt u v (p 0))) := by ring
    rw [e]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hvu) h2

/-- A point of an interior (`1 ≤ i`) support region lies strictly to the
right of the region's left vertex. -/
lemma pv_supp_gt_left {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {i : Fin m} {p : Euc 2} (hp : p ∈ supportOf y σ i) (hi : 1 ≤ i.val) :
    (y ⟨i.val, by omega⟩) 0 < p 0 := by
  have hA := mem_supportOf_inner hp
  have hB := mem_supportOf_left hp hi
  have hA' : pvSgn σ * pvHgt (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) (p 0) <
      pvSgn σ * p 1 :=
    (pv_cross_pos_iff (hmono (Fin.mk_lt_mk.mpr (by omega)))).mp hA
  have hB' : pvSgn σ * p 1 <
      pvSgn σ * pvHgt (y ⟨i.val - 1, by omega⟩) (y ⟨i.val, by omega⟩) (p 0) :=
    (pv_cross_neg_iff (hmono (Fin.mk_lt_mk.mpr (by omega)))).mp hB
  have h10 : (y ⟨i.val - 1, by omega⟩ : Euc 2) 0 < (y ⟨i.val, by omega⟩) 0 :=
    hmono (Fin.mk_lt_mk.mpr (by omega))
  have h20 : (y ⟨i.val, by omega⟩ : Euc 2) 0 < (y ⟨i.val + 1, by omega⟩) 0 :=
    hmono (Fin.mk_lt_mk.mpr (by omega))
  -- rewrite both lines through `y_i`
  have eB : pvHgt (y ⟨i.val - 1, by omega⟩) (y ⟨i.val, by omega⟩) (p 0) =
      (y ⟨i.val, by omega⟩) 1 +
        pvSl (y ⟨i.val - 1, by omega⟩) (y ⟨i.val, by omega⟩) *
          (p 0 - (y ⟨i.val, by omega⟩) 0) :=
    pvHgt_at_right (ne_of_gt h10) _
  have eA : pvHgt (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) (p 0) =
      (y ⟨i.val, by omega⟩) 1 +
        pvSl (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) *
          (p 0 - (y ⟨i.val, by omega⟩) 0) :=
    rfl
  have hslope : pvSgn σ * pvSl (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) <
      pvSgn σ * pvSl (y ⟨i.val - 1, by omega⟩) (y ⟨i.val, by omega⟩) := by
    have h := pvSl_edge hmono hshape (a := i.val - 1) (b := i.val) (by omega)
      (by omega)
    have e : (⟨i.val - 1 + 1, by omega⟩ : Fin (m + 1)) = ⟨i.val, by omega⟩ :=
      Fin.ext_iff.mpr (show i.val - 1 + 1 = i.val by omega)
    rw [e] at h
    exact h
  have key : (0:ℝ) < pvSgn σ *
      (pvSl (y ⟨i.val - 1, by omega⟩) (y ⟨i.val, by omega⟩) -
        pvSl (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩)) *
      (p 0 - (y ⟨i.val, by omega⟩) 0) := by
    have e : pvSgn σ *
        (pvSl (y ⟨i.val - 1, by omega⟩) (y ⟨i.val, by omega⟩) -
          pvSl (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩)) *
        (p 0 - (y ⟨i.val, by omega⟩) 0) =
        pvSgn σ * pvHgt (y ⟨i.val - 1, by omega⟩) (y ⟨i.val, by omega⟩) (p 0) -
          pvSgn σ * pvHgt (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) (p 0) := by
      rw [eB, eA]; ring
    rw [e]; linarith
  have hpos : (0:ℝ) < pvSgn σ *
      (pvSl (y ⟨i.val - 1, by omega⟩) (y ⟨i.val, by omega⟩) -
        pvSl (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩)) := by linarith
  exact sub_pos.mp (pos_of_mul_pos_right key hpos.le)

/-- A point of a non-last (`i + 2 ≤ m`) support region lies strictly to the
left of the region's right vertex. -/
lemma pv_supp_lt_right {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {i : Fin m} {p : Euc 2} (hp : p ∈ supportOf y σ i) (hi : i.val + 2 ≤ m) :
    p 0 < (y ⟨i.val + 1, by omega⟩) 0 := by
  have hA := mem_supportOf_inner hp
  have hC := mem_supportOf_right hp hi
  have hA' : pvSgn σ * pvHgt (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) (p 0) <
      pvSgn σ * p 1 :=
    (pv_cross_pos_iff (hmono (Fin.mk_lt_mk.mpr (by omega)))).mp hA
  have hC' : pvSgn σ * p 1 <
      pvSgn σ * pvHgt (y ⟨i.val + 1, by omega⟩) (y ⟨i.val + 2, by omega⟩) (p 0) :=
    (pv_cross_neg_iff (hmono (Fin.mk_lt_mk.mpr (by omega)))).mp hC
  have h10 : (y ⟨i.val, by omega⟩ : Euc 2) 0 < (y ⟨i.val + 1, by omega⟩) 0 :=
    hmono (Fin.mk_lt_mk.mpr (by omega))
  have h20 : (y ⟨i.val + 1, by omega⟩ : Euc 2) 0 < (y ⟨i.val + 2, by omega⟩) 0 :=
    hmono (Fin.mk_lt_mk.mpr (by omega))
  have eA : pvHgt (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) (p 0) =
      (y ⟨i.val + 1, by omega⟩) 1 +
        pvSl (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) *
          (p 0 - (y ⟨i.val + 1, by omega⟩) 0) :=
    pvHgt_at_right (ne_of_gt h10) _
  have eC : pvHgt (y ⟨i.val + 1, by omega⟩) (y ⟨i.val + 2, by omega⟩) (p 0) =
      (y ⟨i.val + 1, by omega⟩) 1 +
        pvSl (y ⟨i.val + 1, by omega⟩) (y ⟨i.val + 2, by omega⟩) *
          (p 0 - (y ⟨i.val + 1, by omega⟩) 0) :=
    rfl
  have hslope : pvSgn σ * pvSl (y ⟨i.val + 1, by omega⟩) (y ⟨i.val + 2, by omega⟩) <
      pvSgn σ * pvSl (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) :=
    pvSl_edge hmono hshape (a := i.val) (b := i.val + 1) (by omega) (by omega)
  have key : (0:ℝ) < pvSgn σ *
      (pvSl (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) -
        pvSl (y ⟨i.val + 1, by omega⟩) (y ⟨i.val + 2, by omega⟩)) *
      ((y ⟨i.val + 1, by omega⟩) 0 - p 0) := by
    have e : pvSgn σ *
        (pvSl (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) -
          pvSl (y ⟨i.val + 1, by omega⟩) (y ⟨i.val + 2, by omega⟩)) *
        ((y ⟨i.val + 1, by omega⟩) 0 - p 0) =
        pvSgn σ * pvHgt (y ⟨i.val + 1, by omega⟩) (y ⟨i.val + 2, by omega⟩) (p 0) -
          pvSgn σ * pvHgt (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) (p 0) := by
      rw [eA, eC]; ring
    rw [e]; linarith
  have hpos : (0:ℝ) < pvSgn σ *
      (pvSl (y ⟨i.val, by omega⟩) (y ⟨i.val + 1, by omega⟩) -
        pvSl (y ⟨i.val + 1, by omega⟩) (y ⟨i.val + 2, by omega⟩)) := by linarith
  exact sub_pos.mp (pos_of_mul_pos_right key hpos.le)

/-- Mirror of `pv_hgt_le_of_le_right`: sharing the left endpoint `y a`, for
`b ≤ c` and `t ≤ (y a) 0` the line to the nearer point is `ε`-below the
line to the farther point. -/
lemma pv_hgt_le_of_le_right' {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a b c : Fin (m + 1)} (hab : a < b) (hbc : b ≤ c) {t : ℝ}
    (ht : t ≤ (y a) 0) :
    pvSgn σ * pvHgt (y a) (y b) t ≤ pvSgn σ * pvHgt (y a) (y c) t := by
  rcases eq_or_lt_of_le hbc with heq | hlt
  · rw [heq]
  · have hs := pvSl_chord_left hmono hshape hab hlt
    have e : pvSgn σ * (pvHgt (y a) (y c) t - pvHgt (y a) (y b) t) =
        pvSgn σ * (pvSl (y a) (y c) - pvSl (y a) (y b)) * (t - (y a) 0) := by
      unfold pvHgt; ring
    have hprod : (0:ℝ) ≤
        pvSgn σ * (pvSl (y a) (y c) - pvSl (y a) (y b)) * (t - (y a) 0) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (sub_nonpos.mpr ht)
    have h : (0:ℝ) ≤ pvSgn σ * (pvHgt (y a) (y c) t - pvHgt (y a) (y b) t) := by
      rw [e]; exact hprod
    linarith

/-- **Own-edge bound transfers to a farther right endpoint**: if
`p ∈ T_d(y)` and `d < e ≤ m` then `p` is strictly `ε`-above the line
`y_d y_e`.  Used for the first `supportOf` condition of the refined chain. -/
lemma pv_supp_inner {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {d e : ℕ} (hdm : d < m) (he : d < e) (hem : e ≤ m)
    {p : Euc 2} (hp : p ∈ supportOf y σ ⟨d, hdm⟩) :
    0 < pvSgn σ * pvCross (y ⟨d, by omega⟩) (y ⟨e, by omega⟩) p := by
  have hA : pvSgn σ * pvHgt (y ⟨d, by omega⟩) (y ⟨d + 1, by omega⟩) (p 0) <
      pvSgn σ * p 1 :=
    (pv_cross_pos_iff (hmono (Fin.mk_lt_mk.mpr (by omega)))).mp
      (mem_supportOf_inner hp)
  have hde : (y ⟨d, by omega⟩ : Euc 2) 0 < (y ⟨e, by omega⟩) 0 :=
    hmono (Fin.mk_lt_mk.mpr he)
  apply (pv_cross_pos_iff hde).mpr
  by_cases hd0 : d = 0
  · subst d
    -- `d = 0`: the second region condition is the chord `y_0 y_m`
    have hB0 : pvSgn σ * pvHgt (y ⟨0, by omega⟩) (y ⟨m, by omega⟩) (p 0) <
        pvSgn σ * p 1 := by
      have h := (mem_supportOf_iff.mp hp).2.1
      have h' : pvSgn σ * pvCross (y ⟨(0 + m) % (m + 1), Nat.mod_lt _ (by omega)⟩)
          (y ⟨0, by omega⟩) p < 0 := h
      have e : (⟨(0 + m) % (m + 1), Nat.mod_lt _ (by omega)⟩ : Fin (m + 1)) =
          ⟨m, by omega⟩ := Fin.ext_iff.mpr
        (show (0 + m) % (m + 1) = m by
          rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (Nat.lt_succ_self m))
      rw [e] at h'
      have h0m : (y ⟨0, by omega⟩ : Euc 2) 0 < (y ⟨m, by omega⟩) 0 :=
        hmono (Fin.mk_lt_mk.mpr (by omega))
      have h2 := (pv_cross_neg_iff_rev h0m).mp h'
      rwa [pvHgt_comm (ne_of_gt h0m)] at h2
    rcases le_or_gt (p 0) ((y ⟨0, by omega⟩) 0) with hpx | hpx
    · have hle := pv_hgt_le_of_le_right' hmono hshape (a := ⟨0, by omega⟩)
        (b := ⟨e, by omega⟩) (c := ⟨m, by omega⟩)
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_le_mk.mpr hem) hpx
      linarith
    · have hle := pv_hgt_le_of_le_right hmono hshape (a := ⟨0, by omega⟩)
        (b := ⟨1, by omega⟩) (c := ⟨e, by omega⟩)
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega)) hpx.le
      linarith
  · have hpx := pv_supp_gt_left hmono hshape hp (show 1 ≤ d by omega)
    have hle := pv_hgt_le_of_le_right hmono hshape (a := ⟨d, by omega⟩)
        (b := ⟨d + 1, by omega⟩) (c := ⟨e, by omega⟩)
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega)) hpx.le
    linarith

/-- **Left-neighbour bound transfers to an earlier left endpoint**: if
`p ∈ T_d(y)` with `a + 1 ≤ d` then `p` is strictly `ε`-below the line
`y_a y_d`.  Used for the second `supportOf` condition when `j ≥ 1`. -/
lemma pv_supp_left {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a d : ℕ} (ha : a + 1 ≤ d) (hdm : d < m)
    {p : Euc 2} (hp : p ∈ supportOf y σ ⟨d, hdm⟩) :
    pvSgn σ * pvCross (y ⟨a, by omega⟩) (y ⟨d, by omega⟩) p < 0 := by
  have hB : pvSgn σ * p 1 <
      pvSgn σ * pvHgt (y ⟨d - 1, by omega⟩) (y ⟨d, by omega⟩) (p 0) :=
    (pv_cross_neg_iff (hmono (Fin.mk_lt_mk.mpr (by omega)))).mp
      (mem_supportOf_left hp (show 1 ≤ d by omega))
  have hpx := pv_supp_gt_left hmono hshape hp (show 1 ≤ d by omega)
  have had : (y ⟨a, by omega⟩ : Euc 2) 0 < (y ⟨d, by omega⟩) 0 :=
    hmono (Fin.mk_lt_mk.mpr (by omega))
  apply (pv_cross_neg_iff had).mpr
  rcases eq_or_lt_of_le (show a ≤ d - 1 by omega) with haeq | halt
  · subst a; exact hB
  · have hle := pv_hgt_le_of_le_left' hmono hshape (a := ⟨a, by omega⟩)
      (b := ⟨d - 1, by omega⟩) (c := ⟨d, by omega⟩)
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega)) hpx.le
    linarith

/-- **Wraparound bound on the region itself**: if `p ∈ T_d(y)` then `p` is
strictly `ε`-above the wraparound chord `y_d y_m` (equivalently, strictly
`ε`-below the reverse cross).  Used for the second `supportOf` condition
when `j = 0`. -/
lemma pv_supp_wrap_left {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {d : ℕ} (hdm : d < m) {p : Euc 2} (hp : p ∈ supportOf y σ ⟨d, hdm⟩) :
    pvSgn σ * pvCross (y ⟨m, by omega⟩) (y ⟨d, by omega⟩) p < 0 := by
  by_cases hd0 : d = 0
  · subst d
    have h := (mem_supportOf_iff.mp hp).2.1
    have h' : pvSgn σ * pvCross (y ⟨(0 + m) % (m + 1), Nat.mod_lt _ (by omega)⟩)
        (y ⟨0, by omega⟩) p < 0 := h
    have e : (⟨(0 + m) % (m + 1), Nat.mod_lt _ (by omega)⟩ : Fin (m + 1)) =
        ⟨m, by omega⟩ := Fin.ext_iff.mpr
      (show (0 + m) % (m + 1) = m by
        rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (Nat.lt_succ_self m))
    rw [e] at h'
    exact h'
  · have hA : pvSgn σ * pvHgt (y ⟨d, by omega⟩) (y ⟨d + 1, by omega⟩) (p 0) <
        pvSgn σ * p 1 :=
      (pv_cross_pos_iff (hmono (Fin.mk_lt_mk.mpr (by omega)))).mp (mem_supportOf_inner hp)
    have hpx := pv_supp_gt_left hmono hshape hp (show 1 ≤ d by omega)
    have hdm0 : (y ⟨d, by omega⟩ : Euc 2) 0 < (y ⟨m, by omega⟩) 0 :=
      hmono (Fin.mk_lt_mk.mpr hdm)
    apply (pv_cross_neg_iff_rev hdm0).mpr
    rw [pvHgt_comm (ne_of_gt hdm0)]
    have hle := pv_hgt_le_of_le_right hmono hshape (a := ⟨d, by omega⟩)
        (b := ⟨d + 1, by omega⟩) (c := ⟨m, by omega⟩)
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega)) hpx.le
    linarith

/-- **Right-neighbour bound transfers to a farther edge**: if `p ∈ T_d(y)`
with `d + 2 ≤ m` then `p` is strictly `ε`-below every chord `y_c y_e` with
`d + 1 ≤ c` and `c + 1 ≤ e ≤ m`.  Used for the third `supportOf`
condition when `j ≤ k - 2`. -/
lemma pv_supp_right {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {d c e : ℕ} (hdm : d < m) (hdm2 : d + 2 ≤ m) (hc : d + 1 ≤ c)
    (hce : c + 1 ≤ e) (hem : e ≤ m)
    {p : Euc 2} (hp : p ∈ supportOf y σ ⟨d, hdm⟩) :
    pvSgn σ * pvCross (y ⟨c, by omega⟩) (y ⟨e, by omega⟩) p < 0 := by
  have hC : pvSgn σ * p 1 <
      pvSgn σ * pvHgt (y ⟨d + 1, by omega⟩) (y ⟨d + 2, by omega⟩) (p 0) :=
    (pv_cross_neg_iff (hmono (Fin.mk_lt_mk.mpr (by omega)))).mp
      (mem_supportOf_right hp hdm2)
  have hpx := pv_supp_lt_right hmono hshape hp hdm2
  have hce' : (y ⟨c, by omega⟩ : Euc 2) 0 < (y ⟨e, by omega⟩) 0 :=
    hmono (Fin.mk_lt_mk.mpr (by omega))
  apply (pv_cross_neg_iff hce').mpr
  rcases eq_or_lt_of_le hc with hceq | hclt
  · -- `c = d + 1`: shared left endpoint `y_{d+1}`, farther chord is `ε`-above
    subst c
    have hle := pv_hgt_le_of_le_right' hmono hshape (a := ⟨d + 1, by omega⟩)
        (b := ⟨d + 2, by omega⟩) (c := ⟨e, by omega⟩)
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega)) hpx.le
    linarith
  · -- `c ≥ d + 2`: endpoint bound at `y_{d+1}` plus smaller `ε`-slope
    have hvert : pvSgn σ * ((y ⟨d + 1, by omega⟩) 1) <
        pvSgn σ * pvHgt (y ⟨c, by omega⟩) (y ⟨e, by omega⟩)
          ((y ⟨d + 1, by omega⟩) 0) :=
      pv_hgt_above_vertex hmono hshape (a := ⟨c, by omega⟩) (b := ⟨e, by omega⟩)
        (c := ⟨d + 1, by omega⟩) (Fin.mk_lt_mk.mpr (by omega))
        (Or.inl (Fin.mk_lt_mk.mpr (by omega)))
    have hbase : (0:ℝ) < pvSgn σ * (pvHgt (y ⟨c, by omega⟩) (y ⟨e, by omega⟩)
          ((y ⟨d + 1, by omega⟩) 0) -
        pvHgt (y ⟨d + 1, by omega⟩) (y ⟨d + 2, by omega⟩)
          ((y ⟨d + 1, by omega⟩) 0)) := by
      rw [pvHgt_left_pt]; linarith
    have hslope : pvSgn σ * pvSl (y ⟨c, by omega⟩) (y ⟨e, by omega⟩) <
        pvSgn σ * pvSl (y ⟨d + 1, by omega⟩) (y ⟨d + 2, by omega⟩) := by
      rcases eq_or_lt_of_le hce with hceq' | hclt'
      · subst e
        exact pvSl_edge hmono hshape (a := d + 1) (b := c) (by omega) (by omega)
      · exact lt_trans
          (pvSl_chord_left hmono hshape (a := ⟨c, by omega⟩) (b := ⟨c + 1, by omega⟩)
            (c := ⟨e, by omega⟩) (Fin.mk_lt_mk.mpr (by omega))
            (Fin.mk_lt_mk.mpr (by omega)))
          (pvSl_edge hmono hshape (a := d + 1) (b := c) (by omega) (by omega))
    have key : (0:ℝ) < pvSgn σ * (pvHgt (y ⟨c, by omega⟩) (y ⟨e, by omega⟩) (p 0) -
        pvHgt (y ⟨d + 1, by omega⟩) (y ⟨d + 2, by omega⟩) (p 0)) := by
      have e1 : pvSgn σ * (pvHgt (y ⟨c, by omega⟩) (y ⟨e, by omega⟩) (p 0) -
          pvHgt (y ⟨d + 1, by omega⟩) (y ⟨d + 2, by omega⟩) (p 0)) =
          pvSgn σ * (pvHgt (y ⟨c, by omega⟩) (y ⟨e, by omega⟩)
              ((y ⟨d + 1, by omega⟩) 0) -
            pvHgt (y ⟨d + 1, by omega⟩) (y ⟨d + 2, by omega⟩)
              ((y ⟨d + 1, by omega⟩) 0)) +
          pvSgn σ * (pvSl (y ⟨c, by omega⟩) (y ⟨e, by omega⟩) -
              pvSl (y ⟨d + 1, by omega⟩) (y ⟨d + 2, by omega⟩)) *
            (p 0 - (y ⟨d + 1, by omega⟩) 0) := by
        rw [pvHgt_affine _ _ (p 0) ((y ⟨d + 1, by omega⟩) 0),
          pvHgt_affine _ _ (p 0) ((y ⟨d + 1, by omega⟩) 0)]; ring
      rw [e1]
      have hprod : (0:ℝ) < pvSgn σ * (pvSl (y ⟨c, by omega⟩) (y ⟨e, by omega⟩) -
            pvSl (y ⟨d + 1, by omega⟩) (y ⟨d + 2, by omega⟩)) *
          (p 0 - (y ⟨d + 1, by omega⟩) 0) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      linarith
    linarith

/-- **Wraparound bound from a later region**: if `p ∈ T_d(y)` and `a < d`
then `p` is strictly `ε`-above the wraparound chord `y_a y_m`.  Used for
the third `supportOf` condition when `j = k - 1`. -/
lemma pv_supp_wrap_right {m : ℕ} {y : Fin (m + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    {a d : ℕ} (hdm : d < m) (ha : a < d)
    {p : Euc 2} (hp : p ∈ supportOf y σ ⟨d, hdm⟩) :
    pvSgn σ * pvCross (y ⟨m, by omega⟩) (y ⟨a, by omega⟩) p < 0 := by
  have ham : a < m := ha.trans hdm
  have huv : (y ⟨a, by omega⟩ : Euc 2) 0 < (y ⟨m, by omega⟩) 0 :=
    hmono (Fin.mk_lt_mk.mpr ham)
  apply (pv_cross_neg_iff_rev huv).mpr
  rw [pvHgt_comm (ne_of_gt huv)]
  -- goal: `ε * hgt (y a) (y m) (p 0) < ε * p 1`
  have hA : pvSgn σ * pvHgt (y ⟨d, by omega⟩) (y ⟨d + 1, by omega⟩) (p 0) <
      pvSgn σ * p 1 :=
    (pv_cross_pos_iff (hmono (Fin.mk_lt_mk.mpr (by omega)))).mp (mem_supportOf_inner hp)
  by_cases hdm2 : d ≤ m - 2
  · -- interior `d`: the chord stays `ε`-below the own edge on the whole strip
    have hpx := pv_supp_gt_left hmono hshape hp (show 1 ≤ d by omega)
    have hpx' := pv_supp_lt_right hmono hshape hp (show d + 2 ≤ m by omega)
    have hlo : (0:ℝ) < pvSgn σ * (pvHgt (y ⟨d, by omega⟩) (y ⟨d + 1, by omega⟩)
          ((y ⟨d, by omega⟩) 0) -
        pvHgt (y ⟨a, by omega⟩) (y ⟨m, by omega⟩) ((y ⟨d, by omega⟩) 0)) := by
      rw [pvHgt_left_pt]
      have h := pv_hgt_below_vertex hmono hshape (a := ⟨a, by omega⟩)
        (b := ⟨m, by omega⟩) (c := ⟨d, by omega⟩)
        (Fin.mk_lt_mk.mpr ha) (Fin.mk_lt_mk.mpr hdm)
      linarith
    have hhi : (0:ℝ) < pvSgn σ * (pvHgt (y ⟨d, by omega⟩) (y ⟨d + 1, by omega⟩)
          ((y ⟨d + 1, by omega⟩) 0) -
        pvHgt (y ⟨a, by omega⟩) (y ⟨m, by omega⟩) ((y ⟨d + 1, by omega⟩) 0)) := by
      rw [pvHgt_at_right (ne_of_gt (hmono (Fin.mk_lt_mk.mpr (by omega))))]
      have h := pv_hgt_below_vertex hmono hshape (a := ⟨a, by omega⟩)
        (b := ⟨m, by omega⟩) (c := ⟨d + 1, by omega⟩)
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
      linarith
    have key : (0:ℝ) < pvSgn σ * (pvHgt (y ⟨d, by omega⟩) (y ⟨d + 1, by omega⟩)
        (p 0) - pvHgt (y ⟨a, by omega⟩) (y ⟨m, by omega⟩) (p 0)) := by
      apply pv_affine_pos_of_pos (pvSgn_eq_or σ) hpx hpx'
        (f := fun t ↦ pvHgt (y ⟨d, by omega⟩) (y ⟨d + 1, by omega⟩) t -
          pvHgt (y ⟨a, by omega⟩) (y ⟨m, by omega⟩) t)
        (c0 := (y ⟨d, by omega⟩) 1 -
          pvHgt (y ⟨a, by omega⟩) (y ⟨m, by omega⟩) ((y ⟨d, by omega⟩) 0) -
          (pvSl (y ⟨d, by omega⟩) (y ⟨d + 1, by omega⟩) -
            pvSl (y ⟨a, by omega⟩) (y ⟨m, by omega⟩)) * ((y ⟨d, by omega⟩) 0))
        (c1 := pvSl (y ⟨d, by omega⟩) (y ⟨d + 1, by omega⟩) -
          pvSl (y ⟨a, by omega⟩) (y ⟨m, by omega⟩))
      · intro s; unfold pvHgt; ring
      · exact hlo
      · exact hhi
    linarith
  · -- `d = m - 1`: compare against the edge `y_{m-1} y_m` or the chord `y_0 y_m`
    have hdm1 : d = m - 1 := by omega
    have hC0 : pvSgn σ * pvHgt (y ⟨0, by omega⟩) (y ⟨d + 1, by omega⟩) (p 0) <
        pvSgn σ * p 1 := by
      have h := (mem_supportOf_iff.mp hp).2.2
      have h' : pvSgn σ * pvCross (y ⟨d + 1, by omega⟩)
          (y ⟨(d + 2) % (m + 1), Nat.mod_lt _ (by omega)⟩) p < 0 := h
      have e : (⟨(d + 2) % (m + 1), Nat.mod_lt _ (by omega)⟩ : Fin (m + 1)) =
          ⟨0, by omega⟩ := Fin.ext_iff.mpr
        (show (d + 2) % (m + 1) = 0 by
          have h2 : d + 2 = m + 1 := by omega
          rw [h2]; exact Nat.mod_self _)
      rw [e] at h'
      have huv2 : (y ⟨0, by omega⟩ : Euc 2) 0 < (y ⟨d + 1, by omega⟩) 0 :=
        hmono (Fin.mk_lt_mk.mpr (by omega))
      have h2 := (pv_cross_neg_iff_rev huv2).mp h'
      rwa [pvHgt_comm (ne_of_gt huv2)] at h2
    -- rewrite the endpoint `y_{d+1}` as `y_m` throughout (`d + 1 = m`)
    have edm : (⟨d + 1, by omega⟩ : Fin (m + 1)) = ⟨m, by omega⟩ :=
      Fin.ext_iff.mpr (show d + 1 = m by omega)
    rw [edm] at hC0 hA
    rcases le_or_gt (p 0) ((y ⟨m, by omega⟩) 0) with hpx | hpx
    · have hle := pv_hgt_le_of_lt_left hmono hshape (a := ⟨a, by omega⟩)
        (b := ⟨d, by omega⟩) (c := ⟨m, by omega⟩)
        (Fin.mk_lt_mk.mpr ha) (Fin.mk_lt_mk.mpr hdm) hpx
      linarith
    · rcases eq_or_lt_of_le (Nat.zero_le a) with ha0 | ha0
      · subst a; exact hC0
      · have hle := pv_hgt_le_of_lt_left' hmono hshape (a := ⟨0, by omega⟩)
          (b := ⟨a, by omega⟩) (c := ⟨m, by omega⟩)
          (Fin.mk_lt_mk.mpr ha0) (Fin.mk_lt_mk.mpr ham) hpx.le
        linarith

end
