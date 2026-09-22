import JSPProblem.CupsCaps

/-!
# JSP-000527 — the planar `K`-cap / convex-position dichotomy

This file develops the planar core of
Pohoata–Zakharov, *Convex polytopes from fewer points* (arXiv:2208.04878),
Proposition 2.1: for a compact convex `K ⊆ ℝ²` and a finite `Z ⊆ ℝ²` in
general position which is *pairwise `K`-free* — for every distinct `p, q ∈ Z`
the point `q` lies outside `convexHull ℝ (K ∪ {p})` — the Erdős–Szekeres bound

```
|Z| > (a + b - 4 choose a - 2)
```

forces either a `K`-cap of size `a` (a subset `A ⊆ Z` with every point outside
`conv (K ∪ (A ∖ {·}))`) or a convex-position subset of size `b`.

## Reduction to `DistinctX`

The theorem has no `DistinctX` hypothesis, but `cupsCaps` needs one.  A generic
horizontal shear `T_δ : (x, y) ↦ (x + δ·y, y)` is a linear automorphism of
`ℝ²`, hence preserves convexity, affine independence, compactness and all
membership hypotheses.  Choosing `δ` to avoid the finitely many "bad" slopes
of `Z` makes `T_δ '' Z` have pairwise distinct first coordinates.

## Status

The reduction to `DistinctX` is complete (`planar_dichotomy'` below).  The
combinatorial core `planar_dichotomy_aux` — the actual relative
cups–caps/dichotomy — is the genuinely difficult step; see the comments there
for a discussion of the mathematics and the obstruction to naively applying
`cupsCaps`.
-/

noncomputable section

open scoped Classical

namespace JSPProblem.PlanarDichotomy

/-! ### The horizontal shear and its basic properties -/

/-- The horizontal shear `(x, y) ↦ (x + δ·y, y)` as a linear map. -/
def shearX (δ : ℝ) : Euc 2 →ₗ[ℝ] Euc 2 where
  toFun v := WithLp.toLp 2 fun i : Fin 2 ↦ if i = 0 then v 0 + δ * v 1 else v 1
  map_add' v w := by
    apply PiLp.ext; intro i
    fin_cases i <;> simp [PiLp.add_apply]
    · ring
  map_smul' c v := by
    apply PiLp.ext; intro i
    fin_cases i <;> simp [PiLp.smul_apply, smul_eq_mul]
    · ring

theorem shearX_zero (δ : ℝ) (v : Euc 2) :
    (shearX δ v) 0 = v 0 + δ * v 1 := by
  simp [shearX]

theorem shearX_one (δ : ℝ) (v : Euc 2) :
    (shearX δ v) 1 = v 1 := by
  simp [shearX]

theorem shearX_injective (δ : ℝ) : Function.Injective (shearX δ) := by
  intro v w h
  have h1 : v 1 = w 1 := by
    have := congrArg (fun x : Euc 2 ↦ x 1) h
    simpa [shearX_one] using this
  have h0 : v 0 = w 0 := by
    have := congrArg (fun x : Euc 2 ↦ x 0) h
    simp [shearX_zero, h1] at this
    linarith
  apply PiLp.ext; intro i
  fin_cases i
  · exact h0
  · exact h1

/-- There is a shear parameter `δ` making all first coordinates of `Z`
distinct: for each pair `p ≠ q` the equation `(shearX δ p) 0 = (shearX δ q) 0`
has at most one solution in `δ`. -/
theorem exists_shearX_distinct (Z : Finset (Euc 2)) :
    ∃ δ : ℝ, ∀ p ∈ Z, ∀ q ∈ Z, (shearX δ p) 0 = (shearX δ q) 0 → p = q := by
  classical
  -- the finite set of "bad" parameters.
  set bad : Finset ℝ := (Z ×ˢ Z).image fun pq ↦
    if pq.1 1 = pq.2 1 then 0 else (pq.2 0 - pq.1 0) / (pq.1 1 - pq.2 1)
  have hb : (Set.univ : Set ℝ).Infinite := Set.infinite_univ
  obtain ⟨δ, -, hδ⟩ := Set.Infinite.exists_notMem_finset hb bad
  refine ⟨δ, fun p hp q hq heq ↦ ?_⟩
  by_contra hpq
  apply hδ
  rw [Finset.mem_image]
  refine ⟨(p, q), Finset.mem_product.2 ⟨hp, hq⟩, ?_⟩
  rw [shearX_zero, shearX_zero] at heq
  by_cases h1 : p 1 = q 1
  · -- then `p 0 = q 0` too, so `p = q`.
    exfalso; apply hpq
    rw [h1] at heq
    have h0 : p 0 = q 0 := by linarith
    apply PiLp.ext; intro i
    fin_cases i
    · exact h0
    · exact h1
  · have h2 : δ * (p 1 - q 1) = q 0 - p 0 := by linarith
    show (if p 1 = q 1 then (0 : ℝ) else (q 0 - p 0) / (p 1 - q 1)) = δ
    rw [ite_eq_right h1, ← h2, mul_div_cancel_right₀ _ (sub_ne_zero.2 h1)]

/-! ### Transferring the hypotheses through the shear -/

theorem inGeneralPosition_image_shearX {Z : Finset (Euc 2)}
    (hZ : InGeneralPosition (Z : Set (Euc 2))) (hZcard : 3 ≤ Z.card) (δ : ℝ) :
    InGeneralPosition ((Z.image (shearX δ)) : Set (Euc 2)) := by
  intro s' hs' hcard'
  -- preimage finset `s ⊆ Z` with `s.image (shearX δ) = s'`.
  set s : Finset (Euc 2) := Z.filter (fun x ↦ shearX δ x ∈ s') with hsdef
  have hsX : s ⊆ Z := Finset.filter_subset _ Z
  have hsimage : s.image (shearX δ) = s' := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hxs, rfl⟩
      exact (Finset.mem_filter.1 hxs).2
    · intro hz
      have hzX : z ∈ Z.image (shearX δ) := hs' (Finset.mem_coe.2 hz)
      rw [Finset.mem_image] at hzX
      obtain ⟨x, hxX, rfl⟩ := hzX
      exact ⟨x, Finset.mem_filter.2 ⟨hxX, hz⟩, rfl⟩
  have hscard : s.card = 3 := by
    have hinj : Set.InjOn (shearX δ) (s : Set (Euc 2)) :=
      fun _ _ _ _ h ↦ JSPProblem.PlanarDichotomy.shearX_injective δ h
    have hc := Finset.card_image_of_injOn hinj
    rw [hsimage, hcard'] at hc
    exact hc.symm
  have hsi : AffineIndependent ℝ (fun x : ↥s ↦ (x : Euc 2)) :=
    affineIndependent_of_inGeneralPosition hZ hZcard hsX (by omega)
  have hmap : AffineIndependent ℝ
      ((shearX δ).toAffineMap ∘ fun x : ↥s ↦ (x : Euc 2)) :=
    AffineIndependent.map' hsi _ (JSPProblem.PlanarDichotomy.shearX_injective δ)
  rw [LinearMap.coe_toAffineMap] at hmap
  -- the bijection `↥s ≃ ↥s'` induced by `shearX δ`.
  have hbij : Function.Bijective
      (fun x : ↥s ↦ (⟨shearX δ x, by
        rw [← hsimage]; exact Finset.mem_image.2 ⟨x, x.2, rfl⟩⟩ : ↥s')) := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact JSPProblem.PlanarDichotomy.shearX_injective δ (Subtype.ext_iff.1 hxy)
    · intro y
      have hy : (y : Euc 2) ∈ s.image (shearX δ) := hsimage.symm ▸ y.2
      obtain ⟨x, hxs, hxeq⟩ := Finset.mem_image.1 hy
      exact ⟨⟨x, hxs⟩, Subtype.ext hxeq⟩
  set e := Equiv.ofBijective _ hbij
  have hcomp : (fun x : ↥s' ↦ (x : Euc 2)) ∘ e =
      fun x : ↥s ↦ shearX δ x := rfl
  exact (affineIndependent_equiv e).1 (hcomp.symm ▸ hmap)

theorem pairwiseFree_image_shearX {K : Set (Euc 2)} {Z : Finset (Euc 2)}
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2)))) (δ : ℝ) :
    ∀ p' ∈ Z.image (shearX δ), ∀ q' ∈ Z.image (shearX δ), p' ≠ q' →
      q' ∉ convexHull ℝ ((shearX δ '' K) ∪ ({p'} : Set (Euc 2))) := by
  intro p' hp' q' hq' hne hmem
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hp'
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hq'
  have hpq : p ≠ q := fun e ↦ hne (congrArg _ e)
  apply hpair p hp q hq hpq
  have himg : shearX δ '' (K ∪ ({p} : Set (Euc 2))) =
      (shearX δ '' K) ∪ ({shearX δ p} : Set (Euc 2)) := by
    rw [Set.image_union, Set.image_singleton]
  have hconv : shearX δ q ∈ shearX δ '' convexHull ℝ (K ∪ ({p} : Set _)) := by
    rw [LinearMap.image_convexHull, himg]
    exact hmem
  obtain ⟨w, hw, hweq⟩ := hconv
  rwa [shearX_injective δ hweq] at hw

/-! ### The combinatorial core

For the `DistinctX` case we would like to run the Erdős–Szekeres endpoint
induction relative to `K`.  The difficulty, documented at length in
`Caps3D.lean`, is that an ordinary cup or cap need not be a `K`-cap: for
`K` a segment, `Z = {(0,5),(5,4),(10,5)}` is pairwise `K`-free and a `3`-cup,
but `(5,4) ∈ conv (K ∪ {(0,5),(10,5)})`.

#### Structural reductions (proved in comments, not yet formalized)

*Carathéodory reduction.*  For `y ∈ Z` and `A ⊆ Z` finite,
`y ∈ conv (K ∪ (A ∖ {y}))` iff `y ∈ conv (A ∖ {y})` or there exist
`a, a' ∈ A ∖ {y}` with `y ∈ conv (K ∪ {a, a'})` — the other Carathéodory cases
are excluded by `Z ∩ K = ∅` and the pairwise condition.  Hence

```
A is a K-cap  ⟺  InConvexPosition A ∧ no triple {y,a,a'} ⊆ A has
                 y ∈ conv (K ∪ {a, a'}).
```

*Endpoint-chord reduction in the separated case.*  If `K` is separated from
`conv Z` (say `K` strictly below `Z`), then a cap `S` (in the `cupsCaps`
sense, i.e. a concave `x`-chain) is already a `K`-cap: the three
Carathéodory cases for `v ∈ conv (K ∪ S ∖ {v})` are excluded by
convex position of `S`, by pairwise `K`-freeness, and by `v ∉ K`.

#### The angular-order strategy (the intended proof)

The right coordinate system is *angular order around a point* `O ∈ K`.
Sort `Z` by direction from `O` (choosing `O` so the directions are distinct —
possible if `K` has nonempty interior, since `int K` is not contained in any
of the finitely many lines through pairs of `Z`).  For an angularly sorted
triple `a, m, b`, "m beyond the chord `ab` away from `O`" is a cross-sign
condition, so the cups–caps endpoint induction runs verbatim in angular
order, producing an `a`-term *angular cup* or a `b`-term *angular cap*.

*Key lemma (cap ⇒ `K`-cap in angular order).*  Let `C` be an angular cap
(every angularly-interior point beyond its bracketing chord, i.e. outside
`conv (O ∪ chord)`).  Then `C` is a `K`-cap.  Proof sketch: for `v ∈ C`,
Carathéodory reduces `v ∈ conv (K ∪ C ∖ {v})` to
`v ∈ conv (C ∖ {v})` or `v ∈ conv {k, c₁, c₂}` for `k ∈ K`, `c₁, c₂ ∈ C ∖ {v}`.
The ray from `O` through `v` exits the triangle `conv{k,c₁,c₂}` at a point
`w` on one of its three edges, and `v` lies on the segment `O–w`:
- `w` on chord `c₁c₂`: `v ∈ conv (O ∪ {c₁,c₂})`, contradicting the angular
  cap condition;
- `w` on edge `cᵢk`: `v ∈ conv (O ∪ segment cᵢk) ⊆ conv (K ∪ {cᵢ})`,
  contradicting pairwise `K`-freeness;
- `v ∈ conv (C ∖ {v})` contradicts convex position of `C`;
- `v ∈ conv {k₁,k₂,k₃} ⊆ K` contradicts `v ∉ K` (from `hpair`).

Only `O ∈ K` is needed (not `int K`): `O` and `w` are both in the beak
`conv (K ∪ {cᵢ})`, hence so is the segment `Ow` by convexity.

*Remaining difficulties.*  (i) `Z` must have pairwise distinct directions
from `O`; for `dim K ≤ 1` (`K` a point or segment) a generic `O ∈ K` may not
exist when a pair-line of `Z` contains `K` — a separate degenerate argument
is needed.  (ii) A cyclic-order version of `cupsCaps_aux` is required:
angular order is not a linear functional order, so the existing induction
must be generalized (or a cut chosen and wrap-around triples handled).
(iii) Angular caps must be shown to be in `InConvexPosition` for the
`conv (C ∖ {v})` case above.

*Obstruction to the naive endpoint induction.*  In the `x`-order, the wing
case of `v ∈ conv{k,c₁,c₂}` produces only `v ∈ conv(K ∪ {c})` for a
chord-*interior* point `c`, which pairwise freeness does not forbid.  The
angular formulation fixes exactly this: the ray from `O` meets the triangle's
far boundary at a *vertex edge* `cᵢk` or the chord `c₁c₂`, never at a
chord-interior point. -/

/-! ### Implementation of the angular-order strategy -/

/-- The signed area functional `sO O u v = (u - O) × (v - O)`: `sO O u v > 0`
means that the direction of `v` from `O` is obtained from that of `u` by a
counterclockwise rotation through an angle strictly between `0` and `π`. -/
private def sO (O u v : Euc 2) : ℝ :=
  (u 0 - O 0) * (v 1 - O 1) - (u 1 - O 1) * (v 0 - O 0)

/-- The signed double area of the oriented triangle `(x, y, z)`; equals
`sO O x y + sO O y z + sO O z x` for every choice of `O`. -/
private def cycTri (x y z : Euc 2) : ℝ :=
  x 0 * y 1 - x 1 * y 0 + y 0 * z 1 - y 1 * z 0 + z 0 * x 1 - z 1 * x 0

private theorem sO_comm (O u v : Euc 2) : sO O u v = -sO O v u := by
  simp only [sO]; ring

private theorem sO_self (O u : Euc 2) : sO O u u = 0 := by
  simp only [sO]; ring

private theorem sO_eq_cycTri (O x y z : Euc 2) :
    cycTri x y z = sO O x y + sO O y z + sO O z x := by
  simp only [cycTri, sO]; ring

private theorem cycTri_perm (x y z : Euc 2) : cycTri x y z = cycTri y z x := by
  simp only [cycTri]; ring

private theorem cycTri_swap (x y z : Euc 2) : cycTri x y z = -cycTri x z y := by
  simp only [cycTri]; ring

/-- The key "addition" identity: inserting `w` between `u` and `v` changes the
signed area by the oriented triangle area `cycTri u w v`. -/
private theorem sO_add_middle (O u w v : Euc 2) :
    sO O u v = sO O u w + sO O w v - cycTri u w v := by
  simp only [sO, cycTri]; ring

/-- **Every point of `Z` lies outside `K`**: `z ∈ K` would put `z` into
`convexHull ℝ (K ∪ {z'})` for any other `z' ∈ Z`, contradicting pairwise
`K`-freeness. -/
private theorem notMem_K_of_pairwise {K : Set (Euc 2)}
    {Z : Finset (Euc 2)}
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {z z' : Euc 2} (hz : z ∈ Z) (hz' : z' ∈ Z) (hzz' : z ≠ z') : z ∉ K := by
  intro hzK
  exact hpair z' hz' z hz (Ne.symm hzz')
    (subset_convexHull ℝ _ (Set.subset_union_left hzK))

/-- The open lower half-plane `{x | x 1 < a * x 0 + b}` is convex. -/
private theorem convex_lt_line (a b : ℝ) :
    Convex ℝ {x : Euc 2 | x 1 < a * x 0 + b} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have e0 : (s • x + t • y : Euc 2) 0 = s * x 0 + t * y 0 := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  have e1 : (s • x + t • y : Euc 2) 1 = s * x 1 + t * y 1 := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  rw [e0, e1]
  have expand : a * (s * x 0 + t * y 0) + b =
      s * (a * x 0 + b) + t * (a * y 0 + b) := by
    have hb : b = (s + t) * b := by rw [hst]; ring
    conv_lhs => rw [hb]
    ring
  rw [expand]
  rcases lt_or_eq_of_le hs with hsp | hs0
  · have hs' : s * x 1 < s * (a * x 0 + b) := mul_lt_mul_of_pos_left hx hsp
    have ht' : t * y 1 ≤ t * (a * y 0 + b) :=
      mul_le_mul_of_nonneg_left (le_of_lt hy) ht
    linarith [hs', ht']
  · have ht1 : 0 < t := by
      have := hst
      rw [← hs0] at this
      simp at this
      linarith
    have hs' : s * x 1 ≤ s * (a * x 0 + b) := by rw [← hs0]; simp
    have ht' : t * y 1 < t * (a * y 0 + b) := mul_lt_mul_of_pos_left hy ht1
    linarith [hs', ht']

/-- The open upper half-plane `{x | a * x 0 + b < x 1}` is convex. -/
private theorem convex_gt_line (a b : ℝ) :
    Convex ℝ {x : Euc 2 | a * x 0 + b < x 1} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have e0 : (s • x + t • y : Euc 2) 0 = s * x 0 + t * y 0 := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  have e1 : (s • x + t • y : Euc 2) 1 = s * x 1 + t * y 1 := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  rw [e0, e1]
  have expand : a * (s * x 0 + t * y 0) + b =
      s * (a * x 0 + b) + t * (a * y 0 + b) := by
    have hb : b = (s + t) * b := by rw [hst]; ring
    conv_lhs => rw [hb]
    ring
  rw [expand]
  rcases lt_or_eq_of_le hs with hsp | hs0
  · have hs' : s * (a * x 0 + b) < s * x 1 := mul_lt_mul_of_pos_left hx hsp
    have ht' : t * (a * y 0 + b) ≤ t * y 1 :=
      mul_le_mul_of_nonneg_left (le_of_lt hy) ht
    linarith [hs', ht']
  · have ht1 : 0 < t := by
      have := hst
      rw [← hs0] at this
      simp at this
      linarith
    have hs' : s * (a * x 0 + b) ≤ s * x 1 := by rw [← hs0]; simp
    have ht' : t * (a * y 0 + b) < t * y 1 := mul_lt_mul_of_pos_left hy ht1
    linarith [hs', ht']

/-- A cap is in convex position: the supporting line through each point lies
strictly above every other point, hence `p ∉ convexHull (P.erase p)`. -/
private theorem isCap_inConvexPosition {P : Finset (Euc 2)} (hP : IsCap P) :
    InConvexPosition P := by
  intro p hp hmem
  obtain ⟨a, b, hab, hlt⟩ := hP p hp
  have hsub : ((P.erase p : Finset (Euc 2)) : Set (Euc 2)) ⊆
      {x : Euc 2 | x 1 < a * x 0 + b} := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_erase] at hx
    exact hlt x hx.2 hx.1
  have hnotmem : p ∉ {x : Euc 2 | x 1 < a * x 0 + b} := by
    simp [hab]
  exact hnotmem (convexHull_min hsub (convex_lt_line a b) hmem)

/-- A cup is in convex position. -/
private theorem isCup_inConvexPosition {P : Finset (Euc 2)} (hP : IsCup P) :
    InConvexPosition P := by
  intro p hp hmem
  obtain ⟨a, b, hab, hlt⟩ := hP p hp
  have hsub : ((P.erase p : Finset (Euc 2)) : Set (Euc 2)) ⊆
      {x : Euc 2 | a * x 0 + b < x 1} := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_erase] at hx
    exact hlt x hx.2 hx.1
  have hnotmem : p ∉ {x : Euc 2 | a * x 0 + b < x 1} := by
    simp [hab]
  exact hnotmem (convexHull_min hsub (convex_gt_line a b) hmem)

/-- **Empty `K` case**: the ordinary cups–caps theorem produces a cap or a
cup, both of which are in convex position, hence `K`-free in the required
sense for `K = ∅`. -/
private theorem planar_dichotomy_empty
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hdx : DistinctX Z)
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) < Z.card) :
    (∃ A ⊆ Z, A.card = a ∧
      ∀ y ∈ A, y ∉ convexHull ℝ ((∅ : Set (Euc 2)) ∪
        ((A.erase y : Finset _) : Set _))) ∨
    (∃ B ⊆ Z, B.card = b ∧ InConvexPosition B) := by
  obtain ⟨S, hS, hS'⟩ := cupsCaps (a := a) (b := b) (by omega) (by omega) hZ hdx
    (Nat.add_one_le_iff.mpr hcard)
  rcases hS' with ⟨hSa, hScup⟩ | ⟨hSb, hScap⟩
  · refine Or.inl ⟨S, hS, hSa, ?_⟩
    intro y hy
    have h := isCup_inConvexPosition hScup y hy
    rwa [Set.empty_union]
  · exact Or.inr ⟨S, hS, hSb, isCap_inConvexPosition hScap⟩

/-- The convex join of two compact subsets of `ℝ²` is compact, being the image
of the compact set `s × t × [0,1]` under the continuous map
`(x, y, θ) ↦ (1 - θ) • x + θ • y`. -/
private theorem isCompact_convexJoin {s t : Set (Euc 2)}
    (hs : IsCompact s) (ht : IsCompact t) : IsCompact (convexJoin ℝ s t) := by
  have hcont : Continuous
      (fun p : Euc 2 × (Euc 2 × ℝ) ↦ (1 - p.2.2) • p.1 + p.2.2 • p.2.1) := by
    fun_prop
  have himg : convexJoin ℝ s t =
      (fun p : Euc 2 × (Euc 2 × ℝ) ↦ (1 - p.2.2) • p.1 + p.2.2 • p.2.1) ''
        (s ×ˢ (t ×ˢ Set.Icc (0 : ℝ) 1)) := by
    ext z
    constructor
    · intro hz
      rw [mem_convexJoin] at hz
      obtain ⟨x, hx, y, hy, hz⟩ := hz
      rw [segment_eq_image] at hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      exact ⟨⟨x, ⟨y, θ⟩⟩, ⟨hx, hy, hθ⟩, rfl⟩
    · intro hz
      obtain ⟨⟨x, ⟨y, θ⟩⟩, ⟨hx, hy, hθ⟩, rfl⟩ := hz
      rw [mem_convexJoin]
      refine ⟨x, hx, y, hy, ?_⟩
      rw [segment_eq_image]
      exact ⟨θ, hθ, rfl⟩
  rw [himg]
  exact (hs.prod (ht.prod isCompact_Icc)).image hcont

/-- The closed `r`-neighborhood `{x | ∃ w ∈ C, dist x w ≤ r}` of a convex set
`C` is convex. -/
private theorem convex_dist_le {C : Set (Euc 2)} (hC : Convex ℝ C) (r : ℝ) :
    Convex ℝ {x : Euc 2 | ∃ w ∈ C, dist x w ≤ r} := by
  intro x hx y hy s t hs ht hst
  obtain ⟨wx, hwx, hdx⟩ := hx
  obtain ⟨wy, hwy, hdy⟩ := hy
  refine ⟨s • wx + t • wy, hC hwx hwy hs ht hst, ?_⟩
  rw [dist_eq_norm] at hdx hdy ⊢
  have heq : s • x + t • y - (s • wx + t • wy) = s • (x - wx) + t • (y - wy) := by
    rw [smul_sub, smul_sub]; abel
  rw [heq]
  calc ‖s • (x - wx) + t • (y - wy)‖
      ≤ ‖s • (x - wx)‖ + ‖t • (y - wy)‖ := norm_add_le _ _
    _ = s * ‖x - wx‖ + t * ‖y - wy‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hs, abs_of_nonneg ht]
    _ ≤ s * r + t * r :=
        add_le_add (mul_le_mul_of_nonneg_left hdx hs)
          (mul_le_mul_of_nonneg_left hdy ht)
    _ = r := by rw [← add_mul, hst, one_mul]

/-- **The angular-order core of the planar dichotomy.** If `K` has an interior
point `O` such that the directions `z - O` for `z ∈ Z` are pairwise
non-parallel — equivalently `O` lies on no line `affineSpan {p, q}` through two
distinct points `p, q ∈ Z`, expressed as `sO O p q ≠ 0` — then the relative
cups–caps dichotomy holds.

This is the geometric heart of Proposition 2.1: sort `Z` cyclically around `O`;
the cups–caps endpoint induction run in cyclic order produces an `a`-element
*angular cap*, which is a `K`-cap by Carathéodory together with the ray-exit
argument described above (`v ∈ conv {k, c₁, c₂}` forces `v` onto the segment
`O–w` for `w` on the triangle boundary, landing either in `conv (O ∪ {c₁,c₂})`
— contradicting the angular cap condition — or in `conv (K ∪ {cᵢ})` —
contradicting pairwise `K`-freeness), or a `b`-element *angular cup*, which is
in convex position. -/
private theorem planar_dichotomy_intK {K : Set (Euc 2)} (hKc : Convex ℝ K)
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {O : Euc 2} (hO : O ∈ interior K)
    (hdir : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → sO O p q ≠ 0)
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) < Z.card) :
    (∃ A ⊆ Z, A.card = a ∧
      ∀ y ∈ A, y ∉ convexHull ℝ (K ∪ ((A.erase y : Finset _) : Set _))) ∨
    (∃ B ⊆ Z, B.card = b ∧ InConvexPosition B) := by
  sorry

theorem planar_dichotomy_aux {K : Set (Euc 2)} (hKc : Convex ℝ K)
    (hKk : IsCompact K)
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hdx : DistinctX Z)
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) < Z.card) :
    (∃ A ⊆ Z, A.card = a ∧
      ∀ y ∈ A, y ∉ convexHull ℝ (K ∪ ((A.erase y : Finset _) : Set _))) ∨
    (∃ B ⊆ Z, B.card = b ∧ InConvexPosition B) := by
  classical
  -- `Z` has at least three points.
  have hZcard : 3 ≤ Z.card := by
    have h2 : 2 ≤ (a + b - 4).choose (a - 2) := by
      calc 2 ≤ a - 1 := by omega
        _ = (a - 1).choose 1 := (Nat.choose_one_right _).symm
        _ = (a - 1).choose (a - 2) :=
            (Nat.choose_symm (show 1 ≤ a - 1 by omega)).symm
        _ ≤ (a + b - 4).choose (a - 2) :=
            Nat.choose_le_choose _ (by omega)
    omega
  by_cases hKe : K = ∅
  · -- Step 1: the empty case is ordinary cups–caps.
    subst hKe
    exact planar_dichotomy_empty hZ hdx ha hb hcard
  -- Step 2: `K ≠ ∅`.  Fix `O₀ ∈ K` and fatten `K` to `K' = conv (K ∪ B(O₀, r))`
  -- with `r` small enough that pairwise `K`-freeness is preserved.
  obtain ⟨O₀, hO₀⟩ := Set.nonempty_iff_ne_empty.mpr hKe
  -- `convexHull ℝ (K ∪ {p})` is compact for each `p ∈ Z`, so its complement is
  -- open and each `q ∉ conv (K ∪ {p})` has a separating ball.
  have hcomp : ∀ p ∈ Z, IsCompact (convexHull ℝ (K ∪ ({p} : Set (Euc 2)))) := by
    intro p hp
    rw [hKc.convexHull_union (convex_singleton p) ⟨O₀, hO₀⟩
      (Set.singleton_nonempty p)]
    exact isCompact_convexJoin hKk isCompact_singleton
  have hex : ∀ pq ∈ Z.offDiag, ∃ ε : ℝ, 0 < ε ∧
      Metric.ball pq.2 ε ⊆ (convexHull ℝ (K ∪ ({pq.1} : Set (Euc 2))))ᶜ := by
    intro pq hpq
    obtain ⟨hp, hq, hne⟩ := Finset.mem_offDiag.mp hpq
    have hqnot : pq.2 ∉ convexHull ℝ (K ∪ ({pq.1} : Set (Euc 2))) :=
      hpair _ hp _ hq hne
    have hcl : IsOpen (convexHull ℝ (K ∪ ({pq.1} : Set (Euc 2))))ᶜ :=
      (hcomp _ hp).isClosed.isOpen_compl
    exact Metric.isOpen_iff.mp hcl _ hqnot
  choose ε hε hεball using hex
  -- a uniform radius: half the minimum separation over all ordered pairs
  obtain ⟨a₀, ha₀, b₀, hb₀, hne₀⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < Z.card)
  have hoff : Z.offDiag.Nonempty :=
    ⟨(a₀, b₀), Finset.mem_offDiag.mpr ⟨ha₀, hb₀, hne₀⟩⟩
  have hoff' : Z.offDiag.attach.Nonempty :=
    ⟨⟨(a₀, b₀), Finset.mem_offDiag.mpr ⟨ha₀, hb₀, hne₀⟩⟩, Finset.mem_attach _ _⟩
  set r := Z.offDiag.attach.inf' hoff' (fun pq ↦ ε pq.1 pq.2) / 2 with hrdef
  have hinf : 0 < Z.offDiag.attach.inf' hoff' (fun pq ↦ ε pq.1 pq.2) :=
    (Finset.lt_inf'_iff hoff').mpr fun pq _ ↦ hε pq.1 pq.2
  have hr : 0 < r := by rw [hrdef]; linarith
  have hinf_le : ∀ pq (hpq : pq ∈ Z.offDiag),
      Z.offDiag.attach.inf' hoff' (fun pq ↦ ε pq.1 pq.2) ≤ ε pq hpq :=
    fun pq hpq ↦ Finset.inf'_le (f := fun pq ↦ ε pq.1 pq.2)
      (Finset.mem_attach _ ⟨pq, hpq⟩)
  have hr_lt : ∀ pq (hpq : pq ∈ Z.offDiag), r < ε pq hpq := by
    intro pq hpq
    have h1 := hinf_le pq hpq
    have h2 := hε pq hpq
    rw [hrdef]; linarith
  set K' : Set (Euc 2) := convexHull ℝ (K ∪ Metric.closedBall O₀ r) with hK'def
  have hK'c : Convex ℝ K' := convex_convexHull ℝ _
  have hK'k : IsCompact K' := by
    rw [hK'def, hKc.convexHull_union (convex_closedBall O₀ r) ⟨O₀, hO₀⟩
      (Metric.nonempty_closedBall.mpr hr.le)]
    exact isCompact_convexJoin hKk (isCompact_closedBall O₀ r)
  have hKK' : K ⊆ K' :=
    fun x hx ↦ subset_convexHull ℝ _ (Set.subset_union_left hx)
  have hballK' : Metric.ball O₀ r ⊆ K' :=
    fun x hx ↦ subset_convexHull ℝ _
      (Set.subset_union_right (Metric.ball_subset_closedBall hx))
  -- pairwise `K'`-freeness: `conv (K' ∪ {p})` is contained in the closed
  -- `r`-neighborhood of `conv (K ∪ {p})`, which avoids `q` since `r < ε`.
  have hpair' : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K' ∪ ({p} : Set (Euc 2))) := by
    intro p hp q hq hpq hmem
    set C := convexHull ℝ (K ∪ ({p} : Set (Euc 2))) with hCdef
    set T : Set (Euc 2) := {x | ∃ w ∈ C, dist x w ≤ r} with hTdef
    have hTc : Convex ℝ T := convex_dist_le (convex_convexHull ℝ _) r
    have hKT : K ⊆ T := fun k hk ↦
      ⟨k, subset_convexHull ℝ _ (Set.subset_union_left hk), by
        rw [dist_self]; exact hr.le⟩
    have hBT : Metric.closedBall O₀ r ⊆ T := fun x hx ↦
      ⟨O₀, subset_convexHull ℝ _ (Set.subset_union_left hO₀),
        Metric.mem_closedBall.mp hx⟩
    have hpT : ({p} : Set (Euc 2)) ⊆ T := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx, hTdef]
      exact ⟨p, subset_convexHull ℝ _ (Set.subset_union_right rfl), by
        rw [dist_self]; exact hr.le⟩
    have hK'T : K' ⊆ T := convexHull_min (Set.union_subset hKT hBT) hTc
    have hsub : convexHull ℝ (K' ∪ ({p} : Set (Euc 2))) ⊆ T :=
      convexHull_min (Set.union_subset hK'T hpT) hTc
    obtain ⟨w, hwC, hdist⟩ := hsub hmem
    have hpqmem : (p, q) ∈ Z.offDiag := Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩
    have hlt : r < ε (p, q) hpqmem := hr_lt _ hpqmem
    have hwball : w ∈ Metric.ball q (ε (p, q) hpqmem) :=
      Metric.mem_ball.mpr (by rw [← dist_comm q w]; exact hdist.trans_lt hlt)
    exact hεball _ hpqmem hwball hwC
  -- Step 3: find `O ∈ ball O₀ r ⊆ int K'` lying on no pair-line of `Z`.
  -- `sO (O₀ + t • v) p q` is affine in `t`; choose the direction `v = (1, m)`
  -- non-parallel to all pair-differences, then `t` avoiding finitely many
  -- bad values inside `(0, r / ‖v‖)`.
  set badM : Finset ℝ := Z.offDiag.image fun pq ↦
    if pq.1 0 = pq.2 0 then 0 else (pq.2 1 - pq.1 1) / (pq.2 0 - pq.1 0)
    with hbadM
  obtain ⟨m, -, hm⟩ := Set.Infinite.exists_notMem_finset Set.infinite_univ badM
  set v : Euc 2 :=
    WithLp.toLp 2 (fun i : Fin 2 ↦ if i = 0 then (1 : ℝ) else m) with hvdef
  have hv0 : v 0 = 1 := by simp [hvdef]
  have hv1 : v 1 = m := by simp [hvdef]
  have hvne : v ≠ 0 := by
    intro e
    have h : (0 : Euc 2) (0 : Fin 2) = 1 := e ▸ hv0
    simp at h
  have hst : ∀ (t : ℝ) (p q : Euc 2), sO (O₀ + t • v) p q =
      sO O₀ p q + t * (v 0 * (p 1 - q 1) + v 1 * (q 0 - p 0)) := by
    intro t p q
    have e0 : (O₀ + t • v : Euc 2) 0 = O₀ 0 + t * v 0 := by
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have e1 : (O₀ + t • v : Euc 2) 1 = O₀ 1 + t * v 1 := by
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [sO]
    rw [e0, e1]
    ring
  -- the slope `v × (p - q)` of `sO (O₀ + t • v) p q` in `t` is nonzero
  have hcoeff : ∀ pq ∈ Z.offDiag,
      v 0 * (pq.1 1 - pq.2 1) + v 1 * (pq.2 0 - pq.1 0) ≠ 0 := by
    intro pq hpq
    obtain ⟨hp, hq, hne⟩ := Finset.mem_offDiag.mp hpq
    rw [hv0, hv1, one_mul]
    by_cases h0 : pq.1 0 = pq.2 0
    · -- `p 0 = q 0` and `p ≠ q` force `p 1 ≠ q 1`
      have h1 : pq.1 1 ≠ pq.2 1 := by
        intro e
        apply hne
        apply PiLp.ext; intro i
        fin_cases i
        · exact h0
        · exact e
      rw [h0]
      simpa using sub_ne_zero.mpr h1
    · -- `m` was chosen to avoid the bad slope of `(p, q)`
      have hmem : (pq.2 1 - pq.1 1) / (pq.2 0 - pq.1 0) ∈ badM := by
        rw [hbadM, Finset.mem_image]
        exact ⟨pq, hpq, by rw [if_neg h0]⟩
      intro hc
      apply hm
      have hme : m = (pq.2 1 - pq.1 1) / (pq.2 0 - pq.1 0) := by
        rw [eq_div_iff (sub_ne_zero.mpr (Ne.symm h0))]
        linarith [hc]
      rw [hme]
      exact hmem
  set badT : Finset ℝ := Z.offDiag.image fun pq ↦
    -sO O₀ pq.1 pq.2 / (v 0 * (pq.1 1 - pq.2 1) + v 1 * (pq.2 0 - pq.1 0))
    with hbadT
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  obtain ⟨t, htI, htbad⟩ := Set.Infinite.exists_notMem_finset
    (Set.Ioo_infinite (div_pos hr hvnorm)) badT
  rw [Set.mem_Ioo] at htI
  have hOball : O₀ + t • v ∈ Metric.ball O₀ r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos htI.1]
    exact (lt_div_iff₀ hvnorm).mp htI.2
  have hOint : O₀ + t • v ∈ interior K' :=
    interior_maximal hballK' Metric.isOpen_ball hOball
  have hdir : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → sO (O₀ + t • v) p q ≠ 0 := by
    intro p hp q hq hpq hs
    have hpqmem : (p, q) ∈ Z.offDiag := Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩
    rw [hst t p q] at hs
    have hc : v 0 * (p 1 - q 1) + v 1 * (q 0 - p 0) ≠ 0 := hcoeff _ hpqmem
    have ht_eq : t =
        -sO O₀ p q / (v 0 * (p 1 - q 1) + v 1 * (q 0 - p 0)) := by
      rw [eq_div_iff hc]
      linarith [hs]
    apply htbad
    rw [hbadT]
    exact Finset.mem_image.mpr ⟨(p, q), hpqmem, ht_eq.symm⟩
  -- Step 4: the angular-order core, applied to the fattened set `K'`.
  obtain hA | hB := planar_dichotomy_intK hK'c hZ hpair' hOint hdir ha hb hcard
  · obtain ⟨A, hAZ, hAcard, hcap⟩ := hA
    -- a `K'`-cap is a `K`-cap since `K ⊆ K'`
    refine Or.inl ⟨A, hAZ, hAcard, fun y hy hmem ↦ hcap y hy ?_⟩
    exact convexHull_mono (Set.union_subset_union_left _ hKK') hmem
  · obtain ⟨B, hBZ, hBcard, hconv⟩ := hB
    exact Or.inr ⟨B, hBZ, hBcard, hconv⟩

end JSPProblem.PlanarDichotomy

/-! ### The main theorem -/

theorem planar_dichotomy' {K : Set (Euc 2)} (hKc : Convex ℝ K)
    (hKk : IsCompact K)
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) < Z.card) :
    (∃ A ⊆ Z, A.card = a ∧
      ∀ y ∈ A, y ∉ convexHull ℝ (K ∪ ((A.erase y : Finset _) : Set _))) ∨
    (∃ B ⊆ Z, B.card = b ∧ InConvexPosition B) := by
  classical
  obtain ⟨δ, hδ⟩ := JSPProblem.PlanarDichotomy.exists_shearX_distinct Z
  set T := JSPProblem.PlanarDichotomy.shearX δ with hT
  set Z' := Z.image T with hZ'
  set K' := T '' K with hK'
  have hinjZ : Set.InjOn T (Z : Set (Euc 2)) :=
    fun _ _ _ _ h ↦ JSPProblem.PlanarDichotomy.shearX_injective δ h
  have hcardZ' : Z'.card = Z.card := Finset.card_image_of_injOn hinjZ
  have hZcard : 3 ≤ Z.card := by
    have h2 : 2 ≤ (a + b - 4).choose (a - 2) := by
      calc 2 ≤ a - 1 := by omega
        _ = (a - 1).choose 1 := (Nat.choose_one_right _).symm
        _ = (a - 1).choose (a - 2) :=
            (Nat.choose_symm (show 1 ≤ a - 1 by omega)).symm
        _ ≤ (a + b - 4).choose (a - 2) :=
            Nat.choose_le_choose _ (by omega)
    omega
  have hdx' : DistinctX Z' := by
    intro p' hp' q' hq' heq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hp'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hq'
    exact congrArg T (hδ p hp q hq heq)
  have hZ'' : InGeneralPosition (Z' : Set (Euc 2)) :=
    JSPProblem.PlanarDichotomy.inGeneralPosition_image_shearX hZ hZcard δ
  have hKc' : Convex ℝ K' := hKc.linear_image T
  have hKk' : IsCompact K' := hKk.image T.continuous_of_finiteDimensional
  have hpair' : ∀ p' ∈ Z', ∀ q' ∈ Z', p' ≠ q' →
      q' ∉ convexHull ℝ (K' ∪ ({p'} : Set (Euc 2))) :=
    JSPProblem.PlanarDichotomy.pairwiseFree_image_shearX hpair δ
  have hcard' : (a + b - 4).choose (a - 2) < Z'.card := by
    rwa [hcardZ']
  obtain hA | hB := JSPProblem.PlanarDichotomy.planar_dichotomy_aux hKc' hKk' hZ'' hdx'
    hpair' ha hb hcard'
  · obtain ⟨A', hA'Z, hA'card, hcap⟩ := hA
    -- preimage finset `A ⊆ Z` with `A.image T = A'`.
    set A : Finset (Euc 2) := Z.filter (fun x ↦ T x ∈ A') with hAdef
    have hAX : A ⊆ Z := Finset.filter_subset _ Z
    have himg : A.image T = A' := by
      ext z
      simp only [hAdef, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨-, hxA'⟩, rfl⟩; exact hxA'
      · intro hz
        obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.1 (hA'Z hz)
        exact ⟨x, ⟨hxX, hz⟩, rfl⟩
    have hAcard : A.card = a := by
      have hc := Finset.card_image_of_injOn
        (hinjZ.mono (Finset.coe_subset.2 hAX))
      rw [himg, hA'card] at hc
      exact hc.symm
    refine Or.inl ⟨A, hAX, hAcard, ?_⟩
    intro y hy hmem
    have hy' : T y ∈ A' := by
      rw [← himg]; exact Finset.mem_image.2 ⟨y, hy, rfl⟩
    apply hcap _ hy'
    have h1 : T y ∈ convexHull ℝ (T '' (K ∪ ((A.erase y : Finset _) : Set _))) := by
      rw [← LinearMap.image_convexHull]
      exact Set.mem_image_of_mem _ hmem
    have h2 : T '' (K ∪ ((A.erase y : Finset _) : Set _)) =
        K' ∪ ((A'.erase (T y) : Finset _) : Set _) := by
      rw [Set.image_union]
      congr 1
      · ext z
        simp only [Set.mem_image]
        constructor
        · rintro ⟨w, hw, rfl⟩
          rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
            Finset.mem_coe] at hw
          obtain ⟨hwA, hwy⟩ := hw
          rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
            Finset.mem_coe]
          refine ⟨?_, ?_⟩
          · rw [← himg]; exact Finset.mem_image.2 ⟨w, hwA, rfl⟩
          · intro h; apply hwy; exact hinjZ (Finset.mem_coe.2 (hAX hwA))
              (Finset.mem_coe.2 (hAX hy)) h
        · intro hz
          rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
            Finset.mem_coe] at hz
          obtain ⟨hzA', hzne⟩ := hz
          have hzA : z ∈ A.image T := by rwa [himg]
          obtain ⟨w, hwA, rfl⟩ := Finset.mem_image.1 hzA
          refine ⟨w, ?_, rfl⟩
          rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
            Finset.mem_coe]
          exact ⟨hwA, fun h ↦ hzne (congrArg T h)⟩
    rw [h2] at h1
    exact h1
  · obtain ⟨B', hB'Z, hB'card, hconv⟩ := hB
    set B : Finset (Euc 2) := Z.filter (fun x ↦ T x ∈ B') with hBdef
    have hBX : B ⊆ Z := Finset.filter_subset _ Z
    have himg : B.image T = B' := by
      ext z
      simp only [hBdef, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨-, hxB'⟩, rfl⟩; exact hxB'
      · intro hz
        obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.1 (hB'Z hz)
        exact ⟨x, ⟨hxX, hz⟩, rfl⟩
    have hBcard : B.card = b := by
      have hc := Finset.card_image_of_injOn
        (hinjZ.mono (Finset.coe_subset.2 hBX))
      rw [himg, hB'card] at hc
      exact hc.symm
    refine Or.inr ⟨B, hBX, hBcard, ?_⟩
    intro y hy hmem
    have hy' : T y ∈ B' := by
      rw [← himg]; exact Finset.mem_image.2 ⟨y, hy, rfl⟩
    apply hconv _ hy'
    have h1 : T y ∈ convexHull ℝ (T '' ((B.erase y : Finset _) : Set _)) := by
      rw [← LinearMap.image_convexHull]
      exact Set.mem_image_of_mem _ hmem
    have h2 : T '' ((B.erase y : Finset _) : Set _) =
        ((B'.erase (T y) : Finset _) : Set _) := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
          Finset.mem_coe] at hw
        obtain ⟨hwB, hwy⟩ := hw
        rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
          Finset.mem_coe]
        refine ⟨?_, ?_⟩
        · rw [← himg]; exact Finset.mem_image.2 ⟨w, hwB, rfl⟩
        · intro h; apply hwy; exact hinjZ (Finset.mem_coe.2 (hBX hwB))
            (Finset.mem_coe.2 (hBX hy)) h
      · intro hz
        rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
          Finset.mem_coe] at hz
        obtain ⟨hzB', hzne⟩ := hz
        have hzB : z ∈ B.image T := by rwa [himg]
        obtain ⟨w, hwB, rfl⟩ := Finset.mem_image.1 hzB
        refine ⟨w, ?_, rfl⟩
        rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
          Finset.mem_coe]
        exact ⟨hwB, fun h ↦ hzne (congrArg T h)⟩
    rw [h2] at h1
    exact h1

end
