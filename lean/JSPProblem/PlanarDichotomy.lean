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

The proof is complete: `planar_dichotomy2` below establishes the
dichotomy under the weakened hypothesis `2 * (a+b-4 choose a-2) < |Z|`
via the projective halfplane chart of the section "The projective
halfplane chart (factor-`2` variant)".  The reduction to `DistinctX` is
done by the horizontal shear described above; the combinatorial core
`planar_dichotomy_aux2` splits `Z` by a generic line through a point
`O ∈ K` and applies `planar_dichotomy_halfplane` to the larger side.
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

/-! ### The projective halfplane chart (factor-`2` variant)

For the weakened hypothesis `2 * (a+b-4 choose a-2) < |Z|` we use a projective
transformation.  Fix a directed line through `O` with tangent `τ` and normal
`n`; write `z = O + u • τ + w • n` and, on the open halfplane `w > 0`, define
`φ z = (u / w, 1 / w)`.  This map is injective on the halfplane, sends lines
through `O` to vertical lines, preserves collinearity, and satisfies
`y ∈ conv {O, c₁, c₂}` with `y` in the strict interior of the sector iff `φ y`
lies strictly above the chord `φ c₁ φ c₂` (because `1 / w` is a strictly
convex weighting).  A cup of the image pulls back to an *angular cap* about
`O`, which is a `K`-cap by Carathéodory plus the ray-exit argument; a cap
pulls back to a subset in convex position. -/

/-- Coordinate dot product on `ℝ²`. -/
private def dprod (v x : Euc 2) : ℝ := v 0 * x 0 + v 1 * x 1

private theorem dprod_add (v x y : Euc 2) :
    dprod v (x + y) = dprod v x + dprod v y := by
  simp only [dprod, PiLp.add_apply]; ring

private theorem dprod_sub (v x y : Euc 2) :
    dprod v (x - y) = dprod v x - dprod v y := by
  simp only [dprod, PiLp.sub_apply]; ring

private theorem dprod_smul (v : Euc 2) (c : ℝ) (x : Euc 2) :
    dprod v (c • x) = c * dprod v x := by
  simp only [dprod, PiLp.smul_apply, smul_eq_mul]; ring

private theorem dprod_sum {ι : Type*} (v : Euc 2) (s : Finset ι) (f : ι → Euc 2) :
    dprod v (∑ i ∈ s, f i) = ∑ i ∈ s, dprod v (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [dprod]
  · intro a s ha ih
    rw [Finset.sum_insert ha, dprod_add, ih, Finset.sum_insert ha]

/-- If `{τ, n}` has nonzero determinant, a vector orthogonal to both under
`dprod` vanishes. -/
private theorem dprod_eq_zero {τ n x : Euc 2}
    (hdet : τ 0 * n 1 - τ 1 * n 0 ≠ 0)
    (hτ : dprod τ x = 0) (hn : dprod n x = 0) : x = 0 := by
  have key0 : (τ 0 * n 1 - τ 1 * n 0) * x 0 = 0 := by
    have e : (τ 0 * n 1 - τ 1 * n 0) * x 0 =
        n 1 * dprod τ x - τ 1 * dprod n x := by
      simp only [dprod]; ring
    rw [e, hτ, hn]; ring
  have key1 : (τ 0 * n 1 - τ 1 * n 0) * x 1 = 0 := by
    have e : (τ 0 * n 1 - τ 1 * n 0) * x 1 =
        τ 0 * dprod n x - n 0 * dprod τ x := by
      simp only [dprod]; ring
    rw [e, hτ, hn]; ring
  have hx0 : x 0 = 0 := by
    rcases mul_eq_zero.mp key0 with h | h
    · exact absurd h hdet
    · exact h
  have hx1 : x 1 = 0 := by
    rcases mul_eq_zero.mp key1 with h | h
    · exact absurd h hdet
    · exact h
  apply PiLp.ext; intro i
  fin_cases i <;> simp_all

/-- Tangential coordinate `u = τ • (z - O)` of `z` in the frame `(τ, n)`. -/
private def uC (O τ z : Euc 2) : ℝ := dprod τ (z - O)

/-- Normal coordinate `w = n • (z - O)`; the open halfplane is
`{z | 0 < wC O n z}`. -/
private def wC (O n z : Euc 2) : ℝ := dprod n (z - O)

/-- The projective chart `φ z = (u / w, 1 / w)`. -/
private def phiC (O τ n z : Euc 2) : Euc 2 :=
  WithLp.toLp 2 fun i : Fin 2 ↦
    if i = 0 then uC O τ z / wC O n z else 1 / wC O n z

private theorem phiC_zero (O τ n z : Euc 2) :
    (phiC O τ n z) 0 = uC O τ z / wC O n z := by
  simp [phiC]

private theorem phiC_one (O τ n z : Euc 2) :
    (phiC O τ n z) 1 = 1 / wC O n z := by
  simp [phiC]

/-- The determinantal identity linking `u`, `w` and the signed area `sO`. -/
private theorem uC_wC_sO (O τ n x y : Euc 2) :
    uC O τ x * wC O n y - uC O τ y * wC O n x =
      (τ 0 * n 1 - τ 1 * n 0) * sO O x y := by
  simp only [uC, wC, dprod, sO, PiLp.sub_apply]; ring

/-- `φ` is injective on `{z | wC O n z ≠ 0}`. -/
private theorem phiC_injOn {O τ n : Euc 2}
    (hdet : τ 0 * n 1 - τ 1 * n 0 ≠ 0) :
    Set.InjOn (phiC O τ n) {z | wC O n z ≠ 0} := by
  intro x hx y hy h
  have hwx : wC O n x ≠ 0 := hx
  have hwy : wC O n y ≠ 0 := hy
  have h0 := congrArg (fun p : Euc 2 ↦ p 0) h
  have h1 := congrArg (fun p : Euc 2 ↦ p 1) h
  rw [phiC_zero, phiC_zero] at h0
  rw [phiC_one, phiC_one] at h1
  have hw : wC O n x = wC O n y := by
    rwa [one_div, one_div, inv_inj] at h1
  have hu : uC O τ x = uC O τ y := by
    rw [div_eq_div_iff hwx hwy, hw] at h0
    exact mul_right_cancel₀ hwy h0
  have hxy : x - O = y - O := by
    have hz : (x - O) - (y - O) = 0 := by
      refine dprod_eq_zero hdet ?_ ?_
      · rw [dprod_sub]; exact sub_eq_zero.mpr hu
      · rw [dprod_sub]; exact sub_eq_zero.mpr hw
    exact sub_eq_zero.mp hz
  apply PiLp.ext; intro i
  have hi := congrArg (fun p : Euc 2 ↦ p i) hxy
  simp only [PiLp.sub_apply] at hi
  linarith

/-- `sO O y c = 0` when `y - O` is a scalar multiple of `c - O`. -/
private theorem sO_eq_zero_of_smul (O y c : Euc 2) (m : ℝ)
    (h : y - O = m • (c - O)) : sO O y c = 0 := by
  have h0 := congrArg (fun p : Euc 2 ↦ p 0) h
  have h1 := congrArg (fun p : Euc 2 ↦ p 1) h
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
  simp only [sO]
  linear_combination (c 1 - O 1) * h0 - (c 0 - O 0) * h1

/-- Affine independence of the coercion family of a 3-element finset is
non-collinearity. -/
private theorem affineIndependent_coe_iff_not_collinear {s : Finset (Euc 2)}
    (hs : s.card = 3) :
    AffineIndependent ℝ (fun x : s ↦ (x : Euc 2)) ↔
      ¬ Collinear ℝ (s : Set (Euc 2)) := by
  have hc : Fintype.card s = 1 + 2 := by
    rw [Fintype.card_coe]; exact hs
  rw [affineIndependent_iff_not_finrank_vectorSpan_le ℝ _ hc,
    ← collinear_iff_finrank_le_one]
  have hrange : Set.range (fun x : s ↦ (x : Euc 2)) = (s : Set (Euc 2)) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨a, rfl⟩; exact a.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange]

/-- A point in the affine span of two points is collinear with them. -/
private theorem collinear_of_mem_affineSpan_pair {a b c : Euc 2}
    (h : c ∈ affineSpan ℝ ({a, b} : Set (Euc 2))) :
    Collinear ℝ ({a, b, c} : Set (Euc 2)) := by
  have h' := collinear_insert_of_mem_affineSpan_pair h
  rwa [show ({c, a, b} : Set (Euc 2)) = {a, b, c} by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h'

/-- If `φ r` lies on the line through `φ p, φ q`, then `r` lies on the line
through `p, q` (provided `p, q, r` are in the halfplane). -/
private theorem phiC_affineSpan {O τ n : Euc 2}
    (hdet : τ 0 * n 1 - τ 1 * n 0 ≠ 0)
    {p q r : Euc 2}
    (hp : wC O n p ≠ 0) (hq : wC O n q ≠ 0) (hr : wC O n r ≠ 0)
    (h : phiC O τ n r ∈
      affineSpan ℝ ({phiC O τ n p, phiC O τ n q} : Set (Euc 2))) :
    r ∈ affineSpan ℝ ({p, q} : Set (Euc 2)) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at h ⊢
  obtain ⟨θ, hθ⟩ := h
  rw [AffineMap.lineMap_apply_module] at hθ
  have hθ0 := congrArg (fun x : Euc 2 ↦ x 0) hθ
  have hθ1 := congrArg (fun x : Euc 2 ↦ x 1) hθ
  simp only [phiC_zero, phiC_one, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul] at hθ0 hθ1
  set wp := wC O n p with hwp
  set wq := wC O n q with hwq
  set wr := wC O n r with hwr
  set up := uC O τ p with hup
  set uq := uC O τ q with huq
  set ur := uC O τ r with hur
  set β1 := (1 - θ) * wr / wp with hβ1
  set β2 := θ * wr / wq with hβ2
  have hβsum : β1 + β2 = 1 := by
    have e : (1 - θ) * wr / wp + θ * wr / wq =
        wr * ((1 - θ) / wp + θ / wq) := by ring
    rw [hβ1, hβ2, e]
    have e2 : (1 - θ) / wp + θ / wq = 1 / wr := by
      rwa [mul_one_div, mul_one_div] at hθ1
    rw [e2, one_div, mul_inv_cancel₀ hr]
  have hβu : β1 * up + β2 * uq = ur := by
    have e : (1 - θ) * wr / wp * up + θ * wr / wq * uq =
        wr * ((1 - θ) * (up / wp) + θ * (uq / wq)) := by ring
    rw [hβ1, hβ2, e]
    have e2 : (1 - θ) * (up / wp) + θ * (uq / wq) = ur / wr := hθ0
    rw [e2, mul_comm wr (ur / wr), div_mul_cancel₀ _ hr]
  have hβw : β1 * wp + β2 * wq = wr := by
    rw [hβ1, hβ2]
    have e : (1 - θ) * wr / wp * wp + θ * wr / wq * wq =
        (1 - θ) * wr + θ * wr := by
      rw [div_mul_cancel₀ _ hp, div_mul_cancel₀ _ hq]
    rw [e]; ring
  have hζ : r - O = β1 • (p - O) + β2 • (q - O) := by
    have hz : (r - O) - (β1 • (p - O) + β2 • (q - O)) = 0 := by
      refine dprod_eq_zero hdet ?_ ?_
      · rw [dprod_sub, dprod_add, dprod_smul, dprod_smul]
        show uC O τ r - (β1 * uC O τ p + β2 * uC O τ q) = 0
        rw [← hur, ← hup, ← huq, hβu, sub_self]
      · rw [dprod_sub, dprod_add, dprod_smul, dprod_smul]
        show wC O n r - (β1 * wC O n p + β2 * wC O n q) = 0
        rw [← hwr, ← hwp, ← hwq, hβw, sub_self]
    exact sub_eq_zero.mp hz
  refine ⟨β2, ?_⟩
  rw [AffineMap.lineMap_apply_module]
  have h1m : (1 : ℝ) - β2 = β1 := by linarith [hβsum]
  rw [h1m]
  have hr' : r = β1 • p + β2 • q := by
    conv_lhs => rw [← sub_add_cancel r O]
    rw [hζ]
    apply PiLp.ext; intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    linear_combination (-(O i)) * hβsum
  exact hr'.symm

/-- `φ` preserves non-collinearity of triples in the halfplane: if the images
are collinear, so are the preimages. -/
private theorem collinear_phiC {O τ n : Euc 2}
    (hdet : τ 0 * n 1 - τ 1 * n 0 ≠ 0)
    {p q r : Euc 2}
    (hp : wC O n p ≠ 0) (hq : wC O n q ≠ 0) (hr : wC O n r ≠ 0)
    (hpq : p ≠ q)
    (h : Collinear ℝ
      ({phiC O τ n p, phiC O τ n q, phiC O τ n r} : Set (Euc 2))) :
    Collinear ℝ ({p, q, r} : Set (Euc 2)) := by
  have hφpq : phiC O τ n p ≠ phiC O τ n q :=
    fun e ↦ hpq (phiC_injOn hdet hp hq e)
  have hφpmem : phiC O τ n p ∈
      ({phiC O τ n p, phiC O τ n q, phiC O τ n r} : Set (Euc 2)) := by simp
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem hφpmem).mp h
  obtain ⟨a, ha⟩ := hv (phiC O τ n q) (by simp)
  obtain ⟨b, hb⟩ := hv (phiC O τ n r) (by simp)
  have ha0 : a ≠ 0 := by
    intro e
    rw [e, zero_smul, zero_vadd] at ha
    exact hφpq ha.symm
  have hmem : phiC O τ n r ∈ affineSpan ℝ
      ({phiC O τ n p, phiC O τ n q} : Set (Euc 2)) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨b / a, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    rw [vadd_eq_add] at ha
    have h1 : (b / a : ℝ) • phiC O τ n q =
        b • v + (b / a) • phiC O τ n p := by
      rw [ha, smul_add, smul_smul, div_mul_cancel₀ _ ha0]
    rw [h1, add_comm (b • v), ← add_assoc, ← add_smul, sub_add_cancel,
      one_smul, add_comm]
    exact hb.symm
  exact collinear_of_mem_affineSpan_pair
    (phiC_affineSpan hdet hp hq hr hmem)

/-- General position transports through `φ`. -/
private theorem inGeneralPosition_phiC {O τ n : Euc 2}
    (hdet : τ 0 * n 1 - τ 1 * n 0 ≠ 0)
    {Z W : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hZcard : 3 ≤ Z.card) (hWZ : W ⊆ Z)
    (hW : ∀ z ∈ W, wC O n z ≠ 0) :
    InGeneralPosition ((W.image (phiC O τ n)) : Set (Euc 2)) := by
  intro s' hs' hcard'
  obtain ⟨x, y, z', hxy, hxz, hyz, hs'eq⟩ := Finset.card_eq_three.mp hcard'
  subst hs'eq
  obtain ⟨p, hpW, rfl⟩ := Finset.mem_image.mp
    (hs' (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)))
  obtain ⟨q, hqW, rfl⟩ := Finset.mem_image.mp
    (hs' (Finset.mem_coe.mpr
      (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _)))))
  obtain ⟨r, hrW, rfl⟩ := Finset.mem_image.mp
    (hs' (Finset.mem_coe.mpr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton_self _)))))))
  have hpq : p ≠ q := fun e ↦ hxy (by rw [e])
  have hpr : p ≠ r := fun e ↦ hxz (by rw [e])
  have hqr : q ≠ r := fun e ↦ hyz (by rw [e])
  have hc3 : ({phiC O τ n p, phiC O τ n q, phiC O τ n r} :
      Finset (Euc 2)).card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, hxy, hxz, hyz, rfl⟩
  rw [affineIndependent_coe_iff_not_collinear hc3]
  intro hC
  rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton] at hC
  have hpre : Collinear ℝ ({p, q, r} : Set (Euc 2)) :=
    collinear_phiC hdet (hW p hpW) (hW q hqW) (hW r hrW) hpq hC
  have hsub : (({p, q, r} : Finset (Euc 2)) : Set (Euc 2)) ⊆
      (Z : Set (Euc 2)) := by
    intro t ht
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact hWZ hpW
    · exact hWZ hqW
    · exact hWZ hrW
  have hc3z : ({p, q, r} : Finset (Euc 2)).card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, hpq, hpr, hqr, rfl⟩
  have hAI := affineIndependent_of_inGeneralPosition hZ hZcard hsub hc3z.le
  have hnc := (affineIndependent_coe_iff_not_collinear hc3z).mp hAI
  rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton] at hnc
  exact hnc hpre

/-- Coordinatewise evaluation of a finite sum in `Euc 2`. -/
private theorem euc_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Euc 2)
    (j : Fin 2) : (∑ i ∈ s, f i) j = ∑ i ∈ s, (f i) j := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, PiLp.add_apply, ih, Finset.sum_insert ha]

/-- `φ` transports convex-hull membership forward (the positive weights
`wt · w` stay nonnegative since all `w > 0`). -/
private theorem phiC_mem_convexHull {O τ n : Euc 2} {T : Finset (Euc 2)}
    {y : Euc 2} (hT : ∀ z ∈ T, 0 < wC O n z) (hy : 0 < wC O n y)
    (h : y ∈ convexHull ℝ (T : Set (Euc 2))) :
    phiC O τ n y ∈
      convexHull ℝ ((T.image (phiC O τ n)) : Set (Euc 2)) := by
  classical
  rw [Finset.mem_convexHull'] at h
  obtain ⟨wt, hwt0, hwt1, hwy⟩ := h
  have hwyO : y - O = ∑ i ∈ T, wt i • ((i : Euc 2) - O) := by
    have e : (∑ i ∈ T, wt i • ((i : Euc 2) - O)) =
        (∑ i ∈ T, wt i • (i : Euc 2)) - (∑ i ∈ T, wt i) • O := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_sub]
    rw [e, ← hwy, hwt1, one_smul]
  have hwsum : wC O n y = ∑ i ∈ T, wt i * wC O n i := by
    show dprod n (y - O) = _
    rw [hwyO, dprod_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [dprod_smul]; rfl
  have husum : uC O τ y = ∑ i ∈ T, wt i * uC O τ i := by
    show dprod τ (y - O) = _
    rw [hwyO, dprod_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [dprod_smul]; rfl
  have hwy' : wC O n y ≠ 0 := hy.ne'
  refine mem_convexHull_of_exists_fintype
    (w := fun i : T ↦ wt (i : Euc 2) * wC O n (i : Euc 2) / wC O n y)
    (z := fun i : T ↦ phiC O τ n (i : Euc 2)) ?_ ?_ ?_ ?_
  · intro i
    exact div_nonneg (mul_nonneg (hwt0 i i.2) (hT i i.2).le) hy.le
  · have h1 : (∑ i : T, wt (i : Euc 2) * wC O n (i : Euc 2) / wC O n y) =
        ∑ i ∈ T, wt i * wC O n i / wC O n y :=
      Finset.sum_coe_sort T (fun x ↦ wt x * wC O n x / wC O n y)
    rw [h1, ← Finset.sum_div, ← hwsum]
    exact div_self hwy'
  · intro i
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨i, i.2, rfl⟩
  · have h1 : (∑ i : T,
        (wt (i : Euc 2) * wC O n (i : Euc 2) / wC O n y) •
          phiC O τ n (i : Euc 2)) =
        ∑ i ∈ T, (wt i * wC O n i / wC O n y) • phiC O τ n i :=
      Finset.sum_coe_sort T
        (fun x ↦ (wt x * wC O n x / wC O n y) • phiC O τ n x)
    rw [h1]
    apply PiLp.ext
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [euc_sum_apply, phiC_zero]
      have hsum' : (∑ i ∈ T,
            ((wt i * wC O n i / wC O n y) • phiC O τ n i).ofLp 0) =
          ∑ i ∈ T, wt i * uC O τ i / wC O n y := by
        apply Finset.sum_congr rfl; intro i hi
        have hwi : wC O n i ≠ 0 := (hT i hi).ne'
        rw [PiLp.smul_apply, smul_eq_mul, phiC_zero]
        field_simp [hwi, hwy']
        try ring
      rw [hsum', ← Finset.sum_div, ← husum]
    · rw [euc_sum_apply, phiC_one]
      rw [← hwt1]
      have hsum' : (∑ i ∈ T,
            ((wt i * wC O n i / wC O n y) • phiC O τ n i).ofLp 1) =
          ∑ i ∈ T, wt i / wC O n y := by
        apply Finset.sum_congr rfl; intro i hi
        have hwi : wC O n i ≠ 0 := (hT i hi).ne'
        rw [PiLp.smul_apply, smul_eq_mul, phiC_one]
        field_simp [hwi, hwy']
        try ring
      rw [hsum', ← Finset.sum_div]

/-- Image of an erase under an injective-on-`Z` map. -/
private theorem image_erase_eq {Z : Finset (Euc 2)} {f : Euc 2 → Euc 2}
    (hinj : Set.InjOn f (Z : Set (Euc 2))) {S : Finset (Euc 2)} (hS : S ⊆ Z)
    {y : Euc 2} (hy : y ∈ S) :
    (S.erase y).image f = (S.image f).erase (f y) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨w, ⟨hwne, hwS⟩, rfl⟩
    refine ⟨?_, w, hwS, rfl⟩
    intro e
    exact hwne (hinj (Finset.mem_coe.mpr (hS hwS))
      (Finset.mem_coe.mpr (hS hy)) e)
  · rintro ⟨hzne, w, hwS, rfl⟩
    exact ⟨w, ⟨fun e ↦ hzne (congrArg f e), hwS⟩, rfl⟩

/-- **Ray exit.** The ray from `O` through a point `y` of the triangle
`conv {k, c₁, c₂}` (with `{k, c₁, c₂}` affinely independent) exits the
triangle at a point `O + λ (y - O)` with `λ ≥ 1` lying on one of the three
edges. -/
private theorem ray_exit {O y k c1 c2 : Euc 2}
    (hyO : y ≠ O)
    (hAI : AffineIndependent ℝ ![k, c1, c2])
    (hyT : y ∈ convexHull ℝ (({k, c1, c2} : Finset (Euc 2)) : Set (Euc 2))) :
    ∃ lam : ℝ, 1 ≤ lam ∧
      (O + lam • (y - O) ∈ convexHull ℝ ({c1, c2} : Set (Euc 2)) ∨
       O + lam • (y - O) ∈ convexHull ℝ ({k, c1} : Set (Euc 2)) ∨
       O + lam • (y - O) ∈ convexHull ℝ ({k, c2} : Set (Euc 2))) := by
  classical
  set T := convexHull ℝ (({k, c1, c2} : Finset (Euc 2)) : Set (Euc 2)) with hTdef
  set Λ : Set ℝ := Set.Ici 0 ∩ (fun lam ↦ O + lam • (y - O)) ⁻¹' T with hΛdef
  have hTcomp : IsCompact T := (Finset.finite_toSet _).isCompact_convexHull ℝ
  have hΛclosed : IsClosed Λ :=
    isClosed_Ici.inter (hTcomp.isClosed.preimage (by fun_prop))
  have hζ : y - O ≠ 0 := sub_ne_zero.mpr hyO
  have hnormζ : 0 < ‖y - O‖ := norm_pos_iff.mpr hζ
  have hΛmem : (1 : ℝ) ∈ Λ := by
    refine ⟨Set.mem_Ici.mpr zero_le_one, ?_⟩
    show O + (1 : ℝ) • (y - O) ∈ T
    rw [one_smul, add_comm, sub_add_cancel]
    exact hyT
  have hΛne : Λ.Nonempty := ⟨1, hΛmem⟩
  have hΛbdd : BddAbove Λ := by
    obtain ⟨B, hB⟩ := hTcomp.isBounded.exists_norm_le
    refine ⟨(B + ‖O‖) / ‖y - O‖, ?_⟩
    intro lam hlam
    have hl0 : 0 ≤ lam := hlam.1
    have hmem : O + lam • (y - O) ∈ T := hlam.2
    have hn := hB _ hmem
    have key : lam * ‖y - O‖ ≤ B + ‖O‖ := by
      have h1 : ‖lam • (y - O)‖ = lam * ‖y - O‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0]
      have h2 : lam • (y - O) = (O + lam • (y - O)) - O := by
        rw [add_sub_cancel_left]
      calc lam * ‖y - O‖ = ‖(O + lam • (y - O)) - O‖ := by rw [← h2, h1]
        _ ≤ ‖O + lam • (y - O)‖ + ‖O‖ := norm_sub_le _ _
        _ ≤ B + ‖O‖ := by linarith
    exact (le_div_iff₀ hnormζ).mpr key
  set lam0 := sSup Λ with hlam0def
  have hlam0mem : lam0 ∈ Λ := hΛclosed.csSup_mem hΛne hΛbdd
  have hlam0ge : 1 ≤ lam0 := le_csSup hΛbdd hΛmem
  set wbar := O + lam0 • (y - O) with hwdef
  have hwT : wbar ∈ T := hlam0mem.2
  have hlam0nn : 0 ≤ lam0 := hlam0mem.1
  -- barycentric coordinates on the triangle
  have htop : affineSpan ℝ (Set.range ![k, c1, c2]) = ⊤ := by
    rw [hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  set b : AffineBasis (Fin 3) ℝ (Euc 2) := ⟨![k, c1, c2], hAI, htop⟩ with hbdef
  have hbfun : (b : Fin 3 → Euc 2) = ![k, c1, c2] := by
    rw [hbdef]
    rfl
  have hTrange : convexHull ℝ (Set.range (b : Fin 3 → Euc 2)) = T := by
    rw [hTdef, hbfun]
    congr 1
    ext x
    simp [Matrix.range_cons, Matrix.range_empty]
    tauto
  have hcoord : ∀ i : Fin 3, 0 ≤ b.coord i wbar := by
    have hw := hwT
    rw [← hTrange, b.convexHull_eq_nonneg_coord] at hw
    exact hw
  have hsum1 : ∑ i : Fin 3, b.coord i wbar = 1 := b.sum_coord_apply_eq_one wbar
  by_cases hall : ∀ i : Fin 3, 0 < b.coord i wbar
  · -- interior point: extend the ray, contradicting maximality of `lam0`
    exfalso
    have hint : wbar ∈ interior T := by
      rw [← hTrange, b.interior_convexHull]
      exact hall
    obtain ⟨ε, hε, hεsub⟩ :=
      Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    set δ := ε / (2 * ‖y - O‖) with hδdef
    have hδpos : 0 < δ := div_pos hε (mul_pos two_pos hnormζ)
    have hballmem : O + (lam0 + δ) • (y - O) ∈ Metric.ball wbar ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have e : (O + (lam0 + δ) • (y - O)) - wbar = δ • (y - O) := by
        rw [hwdef, add_smul]
        abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
      have e2 : δ * ‖y - O‖ = ε / 2 := by
        rw [hδdef]
        field_simp
      rw [e2]
      exact half_lt_self hε
    have hmem2 : lam0 + δ ∈ Λ :=
      ⟨le_trans hlam0nn (le_add_of_nonneg_right hδpos.le), hεsub hballmem⟩
    have := le_csSup hΛbdd hmem2
    linarith
  · push_neg at hall
    obtain ⟨i, hi⟩ := hall
    have hi0 : b.coord i wbar = 0 := le_antisymm hi (hcoord i)
    have hcomb : ∑ j : Fin 3, b.coord j wbar • (b : Fin 3 → Euc 2) j = wbar :=
      b.linear_combination_coord_eq_self wbar
    rw [hbfun, Fin.sum_univ_three] at hcomb
    refine ⟨lam0, hlam0ge, ?_⟩
    fin_cases i
    · -- `coord 0 = 0`: `wbar` is on the edge `c₁c₂`
      left
      have h0 : b.coord 0 wbar = 0 := by simpa using hi0
      have hc12 : b.coord 1 wbar + b.coord 2 wbar = 1 := by
        rw [Fin.sum_univ_three, h0, zero_add] at hsum1
        exact hsum1
      have e : wbar = b.coord 1 wbar • c1 + b.coord 2 wbar • c2 := by
        simp only [h0, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
          zero_smul, zero_add, add_zero] at hcomb
        exact hcomb.symm
      rw [hwdef] at e
      rw [e]
      exact (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
        (hcoord 1) (hcoord 2) hc12
    · -- `coord 1 = 0`: `wbar` is on the edge `k c₂`
      right; right
      have h1' : b.coord 1 wbar = 0 := by simpa using hi0
      have hk2 : b.coord 0 wbar + b.coord 2 wbar = 1 := by
        rw [Fin.sum_univ_three, h1', add_zero] at hsum1
        exact hsum1
      have e : wbar = b.coord 0 wbar • k + b.coord 2 wbar • c2 := by
        simp only [h1', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
          zero_smul, zero_add, add_zero] at hcomb
        exact hcomb.symm
      rw [hwdef] at e
      rw [e]
      exact (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
        (hcoord 0) (hcoord 2) hk2
    · -- `coord 2 = 0`: `wbar` is on the edge `k c₁`
      right; left
      have h2' : b.coord 2 wbar = 0 := by simpa using hi0
      have hk1 : b.coord 0 wbar + b.coord 1 wbar = 1 := by
        rw [Fin.sum_univ_three, h2', add_zero] at hsum1
        exact hsum1
      have e : wbar = b.coord 0 wbar • k + b.coord 1 wbar • c1 := by
        simp only [h2', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
          zero_smul, zero_add, add_zero] at hcomb
        exact hcomb.symm
      rw [hwdef] at e
      rw [e]
      exact (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
        (hcoord 0) (hcoord 1) hk1

/-- **Halfplane dichotomy.** If `W ⊆ Z` lies in an open halfplane through
`O ∈ K` with more than `(a+b-4 choose a-2)` points, and the directions
`z - O` are pairwise nonparallel, then `Z` contains an `a`-element `K`-cap
or a `b`-element subset in convex position. -/
private theorem planar_dichotomy_halfplane {K : Set (Euc 2)} (hKc : Convex ℝ K)
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {O : Euc 2} (hOK : O ∈ K)
    (hdir : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → sO O p q ≠ 0)
    (τ n : Euc 2) (hdet : τ 0 * n 1 - τ 1 * n 0 ≠ 0)
    {W : Finset (Euc 2)} (hWZ : W ⊆ Z)
    (hW : ∀ z ∈ W, 0 < wC O n z)
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) < W.card) :
    (∃ A ⊆ Z, A.card = a ∧
      ∀ y ∈ A, y ∉ convexHull ℝ (K ∪ ((A.erase y : Finset _) : Set _))) ∨
    (∃ B ⊆ Z, B.card = b ∧ InConvexPosition B) := by
  classical
  have hZcard : 3 ≤ Z.card := by
    have h2 : 2 ≤ (a + b - 4).choose (a - 2) := by
      calc 2 ≤ a - 1 := by omega
        _ = (a - 1).choose 1 := (Nat.choose_one_right _).symm
        _ = (a - 1).choose (a - 2) :=
            (Nat.choose_symm (show 1 ≤ a - 1 by omega)).symm
        _ ≤ (a + b - 4).choose (a - 2) := Nat.choose_le_choose _ (by omega)
    have hW3 : 3 ≤ W.card := by omega
    exact le_trans hW3 (Finset.card_le_card hWZ)
  have hinjW : Set.InjOn (phiC O τ n) (W : Set (Euc 2)) :=
    (phiC_injOn hdet).mono (fun z hz ↦ (hW z hz).ne')
  set W' : Finset (Euc 2) := W.image (phiC O τ n) with hW'def
  have hcardW' : W'.card = W.card := Finset.card_image_of_injOn hinjW
  have hdx : DistinctX W' := by
    intro x' hx' y' hy' heq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
    rw [phiC_zero, phiC_zero] at heq
    have hxy : uC O τ x * wC O n y = uC O τ y * wC O n x := by
      rwa [div_eq_div_iff (hW x hx).ne' (hW y hy).ne'] at heq
    have hsd := uC_wC_sO O τ n x y
    rw [hxy, sub_self] at hsd
    have hsO : sO O x y = 0 := by
      have e : (τ 0 * n 1 - τ 1 * n 0) * sO O x y = 0 := hsd.symm
      exact (mul_eq_zero.mp e).resolve_left hdet
    by_cases hxy' : x = y
    · exact congrArg _ hxy'
    · exact absurd hsO (hdir x (hWZ hx) y (hWZ hy) hxy')
  have hgp : InGeneralPosition (W' : Set (Euc 2)) :=
    inGeneralPosition_phiC hdet hZ hZcard hWZ (fun z hz ↦ (hW z hz).ne')
  obtain ⟨S', hS'W', hS'⟩ := cupsCaps (a := a) (b := b) (by omega) (by omega)
    hgp hdx (by rw [hcardW']; omega)
  -- the pullback finset `S ⊆ W` with `S.image φ = S'`
  set S : Finset (Euc 2) := W.filter (fun z ↦ phiC O τ n z ∈ S') with hSdef
  have hSW : S ⊆ W := Finset.filter_subset _ _
  have hSZ : S ⊆ Z := hSW.trans hWZ
  have hSimg : S.image (phiC O τ n) = S' := by
    ext z
    simp only [hSdef, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
    · intro hz
      obtain ⟨x, hxW, rfl⟩ := Finset.mem_image.mp (hS'W' hz)
      exact ⟨x, ⟨hxW, hz⟩, rfl⟩
  have hScard : S.card = S'.card := by
    have hc := Finset.card_image_of_injOn
      (hinjW.mono (Finset.coe_subset.mpr hSW))
    rw [hSimg] at hc
    exact hc.symm
  -- convex position transports back along `φ`
  have transport_conv {Q' : Finset (Euc 2)} (hQ : InConvexPosition Q')
      (hQeq : S.image (phiC O τ n) = Q') : InConvexPosition S := by
    intro y hy hmem
    have hy' : phiC O τ n y ∈ Q' := by
      rw [← hQeq]; exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    apply hQ _ hy'
    rw [← hQeq, ← image_erase_eq hinjW hSW hy]
    exact phiC_mem_convexHull
      (fun z hz ↦ hW z (hSW (Finset.mem_erase.mp hz).2)) (hW y (hSW hy)) hmem
  rcases hS' with ⟨hSa, hScup⟩ | ⟨hSb, hScap⟩
  · -- a cup of the image pulls back to a `K`-cap
    have hconvS : InConvexPosition S :=
      transport_conv (isCup_inConvexPosition hScup) hSimg
    refine Or.inl ⟨S, hSZ, by rw [hScard, hSa], ?_⟩
    intro y hy hmem
    set F : Finset (Euc 2) := S.erase y with hFdef
    rw [convexHull_eq_union] at hmem
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨t, htKF, htAI, hyt⟩ := hmem
    have hcard3 : t.card ≤ 3 := by
      have h := htAI.card_le_finrank_succ
      rw [Fintype.card_coe] at h
      have hfin : Module.finrank ℝ
          (vectorSpan ℝ (Set.range ((↑) : ↥t → Euc 2))) ≤ 2 :=
        (Submodule.finrank_le _).trans
          (le_of_eq finrank_euclideanSpace_fin)
      omega
    set tF := t.filter (· ∈ F) with htFdef
    set tK := t.filter (· ∈ K) with htKdef
    have htU : t = tK ∪ tF := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hx' := htKF (Finset.mem_coe.mpr hx)
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rcases (Set.mem_union _ _ _).mp hx' with hxK | hxF
        · exact Or.inl ⟨hx, hxK⟩
        · exact Or.inr ⟨hx, Finset.mem_coe.mp hxF⟩
      · intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with h | h
        · exact (Finset.mem_filter.mp h).1
        · exact (Finset.mem_filter.mp h).1
    -- `Z ∩ K = ∅`
    have hZK : ∀ z ∈ Z, z ∉ K := by
      intro z hz
      obtain ⟨a₀, ha₀, b₀, hb₀, hne₀⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < Z.card)
      rcases eq_or_ne z a₀ with rfl | hza
      · exact notMem_K_of_pairwise hpair ha₀ hb₀ hne₀
      · exact notMem_K_of_pairwise hpair hz ha₀ hza
    have hdisj : Disjoint tK tF := by
      rw [Finset.disjoint_left]
      intro x hxK hxF
      have hxK' : x ∈ K := (Finset.mem_filter.mp hxK).2
      have hxZ : x ∈ Z :=
        hSZ (Finset.erase_subset _ _ (hFdef ▸ (Finset.mem_filter.mp hxF).2))
      exact hZK x hxZ hxK'
    have htF_sub : tF ⊆ F := fun x hx ↦ (Finset.mem_filter.mp hx).2
    have htF_sub_t : tF ⊆ t := Finset.filter_subset _ _
    have htFcard : tF.card ≤ 3 := (Finset.card_le_card htF_sub_t).trans hcard3
    have hcardt : t.card = tK.card + tF.card := by
      rw [htU]
      exact Finset.card_union_of_disjoint hdisj
    interval_cases hfc : tF.card
    · -- `tF = ∅`: `y ∈ conv K = K`, contradicting `y ∉ K`
      have htFe : tF = ∅ := Finset.card_eq_zero.mp hfc
      have htK : ↑t ⊆ K := by
        intro x hx
        have hx' : x ∈ tK ∪ tF := htU ▸ Finset.mem_coe.mp hx
        rw [htFe, Finset.union_empty] at hx'
        exact (Finset.mem_filter.mp hx').2
      have hyK : y ∈ convexHull ℝ K := convexHull_mono htK hyt
      rw [hKc.convexHull_eq] at hyK
      exact hZK y (hSZ hy) hyK
    · -- `tF = {c}`: `y ∈ conv (K ∪ {c})`, contradicting `hpair`
      obtain ⟨c, htc⟩ := Finset.card_eq_one.mp hfc
      have hcF : c ∈ F := htF_sub (by rw [htc]; exact Finset.mem_singleton_self c)
      have hcS : c ∈ S := Finset.erase_subset _ _ (hFdef ▸ hcF)
      have hcy : c ≠ y := (Finset.mem_erase.mp (hFdef ▸ hcF)).1
      have hsub : ↑t ⊆ K ∪ ({c} : Set (Euc 2)) := by
        intro x hx
        have hx' : x ∈ tK ∪ tF := htU ▸ Finset.mem_coe.mp hx
        rw [htc] at hx'
        rcases Finset.mem_union.mp hx' with h | h
        · exact Set.subset_union_left (Finset.mem_filter.mp h).2
        · exact Set.subset_union_right
            (Set.mem_singleton_iff.mpr (Finset.mem_singleton.mp h))
      exact hpair c (hSZ hcS) y (hSZ hy) hcy (convexHull_mono hsub hyt)
    · -- `tF = {c₁, c₂}`: the interesting ray-exit case
      obtain ⟨c1, c2, hc12, htc2⟩ := Finset.card_eq_two.mp hfc
      have htKcard : tK.card ≤ 1 := by omega
      have hc1F : c1 ∈ F := htF_sub (by rw [htc2]; simp)
      have hc2F : c2 ∈ F := htF_sub (by rw [htc2]; simp)
      have hc1S : c1 ∈ S := Finset.erase_subset _ _ (hFdef ▸ hc1F)
      have hc2S : c2 ∈ S := Finset.erase_subset _ _ (hFdef ▸ hc2F)
      have hc1Z : c1 ∈ Z := hSZ hc1S
      have hc2Z : c2 ∈ Z := hSZ hc2S
      have hc1y : c1 ≠ y := (Finset.mem_erase.mp (hFdef ▸ hc1F)).1
      have hc2y : c2 ≠ y := (Finset.mem_erase.mp (hFdef ▸ hc2F)).1
      by_cases htKe : tK = ∅
      · -- `t ⊆ {c₁, c₂} ⊆ F`: contradicts convex position of `S`
        have htF' : ↑t ⊆ (↑F : Set (Euc 2)) := by
          intro x hx
          have hx' : x ∈ tK ∪ tF := htU ▸ Finset.mem_coe.mp hx
          rw [htKe, Finset.empty_union] at hx'
          exact Finset.mem_coe.mpr (htF_sub hx')
        exact hconvS y hy (convexHull_mono htF' hyt)
      · -- `t = {k, c₁, c₂}` with `k ∈ K`: the ray `Ov` exits the triangle
        have htk1 : tK.card = 1 := by
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp htKcard with h | h
          · exact absurd (Finset.card_eq_zero.mp h) htKe
          · exact h
        obtain ⟨k, hk⟩ := Finset.card_eq_one.mp htk1
        have hkm : k ∈ tK := by rw [hk]; exact Finset.mem_singleton_self k
        have hkK : k ∈ K := (Finset.mem_filter.mp hkm).2
        have ht_eq : t = {k, c1, c2} := by
          rw [htU, hk, htc2, Finset.singleton_union]
        have hkc1 : k ≠ c1 := fun e ↦ hZK c1 hc1Z (e ▸ hkK)
        have hkc2 : k ≠ c2 := fun e ↦ hZK c2 hc2Z (e ▸ hkK)
        have ht3 : t.card = 3 := by
          rw [ht_eq]
          exact Finset.card_eq_three.mpr ⟨k, c1, c2, hkc1, hkc2, hc12, rfl⟩
        have hnc : ¬ Collinear ℝ
            (↑({k, c1, c2} : Finset (Euc 2)) : Set (Euc 2)) := by
          rw [← ht_eq]
          exact (affineIndependent_coe_iff_not_collinear ht3).mp htAI
        rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton] at hnc
        have hAI3 : AffineIndependent ℝ ![k, c1, c2] :=
          affineIndependent_iff_not_collinear_set.mpr hnc
        have hyO : y ≠ O := fun e ↦ hZK y (hSZ hy) (e.symm ▸ hOK)
        have hyt' : y ∈ convexHull ℝ
            (↑({k, c1, c2} : Finset (Euc 2)) : Set (Euc 2)) := ht_eq ▸ hyt
        obtain ⟨lam, hlam1, hed⟩ := ray_exit hyO hAI3 hyt'
        have hlampos : 0 < lam := by linarith
        have hlam0 : lam ≠ 0 := hlampos.ne'
        rcases hed with h12 | hk1 | hk2
        · -- the exit point is on edge `c₁c₂`
          rw [convexHull_pair, segment_eq_image] at h12
          obtain ⟨θ, hθ01, hθeq⟩ := h12
          obtain ⟨hθ0, hθ1⟩ := Set.mem_Icc.mp hθ01
          set α1 := lam⁻¹ * (1 - θ) with hα1def
          set α2 := lam⁻¹ * θ with hα2def
          have hζeq : y - O = α1 • (c1 - O) + α2 • (c2 - O) := by
            have h1 : lam • (y - O) =
                (1 - θ) • (c1 - O) + θ • (c2 - O) := by
              have e := congrArg (fun v : Euc 2 ↦ v - O) hθeq
              rw [add_sub_cancel_left] at e
              rw [← e]
              apply PiLp.ext; intro i
              simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
                smul_eq_mul]
              ring
            have h2 := congrArg (fun v : Euc 2 ↦ lam⁻¹ • v) h1
            rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul] at h2
            rw [h2, smul_add, smul_smul, smul_smul, ← hα1def, ← hα2def]
          rcases lt_or_eq_of_le hθ0 with hθpos | hθeq0
          · rcases lt_or_eq_of_le hθ1 with hθlt1 | hθeq1
            · -- `0 < θ < 1`: `φ y` lies strictly above the chord,
              -- contradicting the cup's supporting line
              have hα1pos : 0 < α1 :=
                mul_pos (inv_pos.mpr hlampos) (sub_pos.mpr hθlt1)
              have hα2pos : 0 < α2 := mul_pos (inv_pos.mpr hlampos) hθpos
              obtain ⟨A, B₀, hline, habove⟩ := hScup (phiC O τ n y)
                (by rw [← hSimg]; exact Finset.mem_image.mpr ⟨y, hy, rfl⟩)
              have hc1' : phiC O τ n c1 ∈ S' := by
                rw [← hSimg]; exact Finset.mem_image.mpr ⟨c1, hc1S, rfl⟩
              have hc2' : phiC O τ n c2 ∈ S' := by
                rw [← hSimg]; exact Finset.mem_image.mpr ⟨c2, hc2S, rfl⟩
              have hne1 : phiC O τ n c1 ≠ phiC O τ n y :=
                fun e ↦ hc1y (hinjW (Finset.mem_coe.mpr (hSW hc1S))
                  (Finset.mem_coe.mpr (hSW hy)) e)
              have hne2 : phiC O τ n c2 ≠ phiC O τ n y :=
                fun e ↦ hc2y (hinjW (Finset.mem_coe.mpr (hSW hc2S))
                  (Finset.mem_coe.mpr (hSW hy)) e)
              have hs1 := habove _ hc1' hne1
              have hs2 := habove _ hc2' hne2
              rw [phiC_one, phiC_zero] at hs1 hs2 hline
              have hw1 : 0 < wC O n c1 := hW c1 (hSW hc1S)
              have hw2 : 0 < wC O n c2 := hW c2 (hSW hc2S)
              have hwy0 : 0 < wC O n y := hW y (hSW hy)
              have hu : uC O τ y =
                  α1 * uC O τ c1 + α2 * uC O τ c2 := by
                show dprod τ (y - O) =
                  α1 * dprod τ (c1 - O) + α2 * dprod τ (c2 - O)
                rw [hζeq, dprod_add, dprod_smul, dprod_smul]
              have hw : wC O n y =
                  α1 * wC O n c1 + α2 * wC O n c2 := by
                show dprod n (y - O) =
                  α1 * dprod n (c1 - O) + α2 * dprod n (c2 - O)
                rw [hζeq, dprod_add, dprod_smul, dprod_smul]
              have hs1' : α1 * wC O n c1 *
                  (A * (uC O τ c1 / wC O n c1) + B₀) < α1 := by
                have h := mul_lt_mul_of_pos_left hs1 (mul_pos hα1pos hw1)
                have e1 : α1 * wC O n c1 * (1 / wC O n c1) = α1 := by
                  field_simp [hw1.ne']
                rwa [e1] at h
              have hs2' : α2 * wC O n c2 *
                  (A * (uC O τ c2 / wC O n c2) + B₀) < α2 := by
                have h := mul_lt_mul_of_pos_left hs2 (mul_pos hα2pos hw2)
                have e2 : α2 * wC O n c2 * (1 / wC O n c2) = α2 := by
                  field_simp [hw2.ne']
                rwa [e2] at h
              have hlt : α1 * wC O n c1 * (A * (uC O τ c1 / wC O n c1) + B₀) +
                  α2 * wC O n c2 * (A * (uC O τ c2 / wC O n c2) + B₀) <
                  α1 + α2 := add_lt_add hs1' hs2'
              have hRHS : α1 * wC O n c1 * (A * (uC O τ c1 / wC O n c1) + B₀) +
                  α2 * wC O n c2 * (A * (uC O τ c2 / wC O n c2) + B₀) = 1 := by
                have e1r : α1 * wC O n c1 * (A * (uC O τ c1 / wC O n c1) + B₀) =
                    A * (α1 * uC O τ c1) + α1 * wC O n c1 * B₀ := by
                  field_simp [hw1.ne']
                have e2r : α2 * wC O n c2 * (A * (uC O τ c2 / wC O n c2) + B₀) =
                    A * (α2 * uC O τ c2) + α2 * wC O n c2 * B₀ := by
                  field_simp [hw2.ne']
                have key : A * (α1 * uC O τ c1) + α1 * wC O n c1 * B₀ +
                    (A * (α2 * uC O τ c2) + α2 * wC O n c2 * B₀) =
                    A * uC O τ y + B₀ * wC O n y := by
                  linear_combination A * hu.symm + B₀ * hw.symm
                have e : A * uC O τ y + B₀ * wC O n y = 1 := by
                  field_simp [hwy0.ne'] at hline ⊢
                  linarith [hline]
                rw [e1r, e2r]
                exact key.trans e
              have hαsum : α1 + α2 = lam⁻¹ := by
                rw [hα1def, hα2def]; ring
              have hle : α1 + α2 ≤ 1 := by
                rw [hαsum]; exact inv_le_one_of_one_le₀ hlam1
              linarith [hlt, hRHS, hle]
            · -- `θ = 1`: the exit point is `c₂`, so `y` and `c₂` are
              -- parallel directions — contradiction
              have hα1z : α1 = 0 := by rw [hα1def, hθeq1]; simp
              rw [hα1z, zero_smul, zero_add] at hζeq
              exact absurd (sO_eq_zero_of_smul O y c2 α2 hζeq)
                (hdir y (hSZ hy) c2 hc2Z (Ne.symm hc2y))
          · -- `θ = 0`: the exit point is `c₁`
            have hα2z : α2 = 0 := by rw [hα2def, ← hθeq0]; simp
            rw [hα2z, zero_smul, add_zero] at hζeq
            exact absurd (sO_eq_zero_of_smul O y c1 α1 hζeq)
              (hdir y (hSZ hy) c1 hc1Z (Ne.symm hc1y))
        · -- the exit point is on edge `k c₁`: `y ∈ conv (K ∪ {c₁})`
          rw [convexHull_pair, segment_eq_image] at hk1
          obtain ⟨θ, hθ01, hθeq⟩ := hk1
          obtain ⟨hθ0, hθ1⟩ := Set.mem_Icc.mp hθ01
          have hζeq : y - O =
              (lam⁻¹ * (1 - θ)) • (k - O) + (lam⁻¹ * θ) • (c1 - O) := by
            have h1 : lam • (y - O) = (1 - θ) • (k - O) + θ • (c1 - O) := by
              have e := congrArg (fun v : Euc 2 ↦ v - O) hθeq
              rw [add_sub_cancel_left] at e
              rw [← e]
              apply PiLp.ext; intro i
              simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
                smul_eq_mul]
              ring
            have h2 := congrArg (fun v : Euc 2 ↦ lam⁻¹ • v) h1
            rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul] at h2
            rw [h2, smul_add, smul_smul, smul_smul]
          have hmem' : y ∈ convexHull ℝ ({O, k, c1} : Set (Euc 2)) := by
            have hw1 : 0 ≤ 1 - lam⁻¹ :=
              sub_nonneg.mpr (inv_le_one_of_one_le₀ hlam1)
            have hw2 : 0 ≤ lam⁻¹ * (1 - θ) :=
              mul_nonneg (inv_nonneg.mpr hlampos.le) (sub_nonneg.mpr hθ1)
            have hw3 : 0 ≤ lam⁻¹ * θ :=
              mul_nonneg (inv_nonneg.mpr hlampos.le) hθ0
            apply mem_convexHull_of_exists_fintype
              (w := ![1 - lam⁻¹, lam⁻¹ * (1 - θ), lam⁻¹ * θ])
              (z := ![O, k, c1])
            · intro i
              fin_cases i
              · simpa using hw1
              · simpa using hw2
              · simpa using hw3
            · rw [Fin.sum_univ_three]
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
              ring
            · intro i; fin_cases i <;> simp
            · rw [Fin.sum_univ_three]
              apply PiLp.ext; intro i
              have hi := congrArg (fun v : Euc 2 ↦ v i) hζeq
              simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
                smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
                at hi ⊢
              linear_combination -hi
          have hsub : ({O, k, c1} : Set (Euc 2)) ⊆ K ∪ ({c1} : Set (Euc 2)) := by
            intro x hx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl | rfl
            · exact Set.subset_union_left hOK
            · exact Set.subset_union_left hkK
            · exact Set.subset_union_right rfl
          exact hpair c1 hc1Z y (hSZ hy) hc1y (convexHull_mono hsub hmem')
        · -- the exit point is on edge `k c₂`: `y ∈ conv (K ∪ {c₂})`
          rw [convexHull_pair, segment_eq_image] at hk2
          obtain ⟨θ, hθ01, hθeq⟩ := hk2
          obtain ⟨hθ0, hθ1⟩ := Set.mem_Icc.mp hθ01
          have hζeq : y - O =
              (lam⁻¹ * (1 - θ)) • (k - O) + (lam⁻¹ * θ) • (c2 - O) := by
            have h1 : lam • (y - O) = (1 - θ) • (k - O) + θ • (c2 - O) := by
              have e := congrArg (fun v : Euc 2 ↦ v - O) hθeq
              rw [add_sub_cancel_left] at e
              rw [← e]
              apply PiLp.ext; intro i
              simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
                smul_eq_mul]
              ring
            have h2 := congrArg (fun v : Euc 2 ↦ lam⁻¹ • v) h1
            rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul] at h2
            rw [h2, smul_add, smul_smul, smul_smul]
          have hmem' : y ∈ convexHull ℝ ({O, k, c2} : Set (Euc 2)) := by
            have hw1 : 0 ≤ 1 - lam⁻¹ :=
              sub_nonneg.mpr (inv_le_one_of_one_le₀ hlam1)
            have hw2 : 0 ≤ lam⁻¹ * (1 - θ) :=
              mul_nonneg (inv_nonneg.mpr hlampos.le) (sub_nonneg.mpr hθ1)
            have hw3 : 0 ≤ lam⁻¹ * θ :=
              mul_nonneg (inv_nonneg.mpr hlampos.le) hθ0
            apply mem_convexHull_of_exists_fintype
              (w := ![1 - lam⁻¹, lam⁻¹ * (1 - θ), lam⁻¹ * θ])
              (z := ![O, k, c2])
            · intro i
              fin_cases i
              · simpa using hw1
              · simpa using hw2
              · simpa using hw3
            · rw [Fin.sum_univ_three]
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
              ring
            · intro i; fin_cases i <;> simp
            · rw [Fin.sum_univ_three]
              apply PiLp.ext; intro i
              have hi := congrArg (fun v : Euc 2 ↦ v i) hζeq
              simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
                smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
                at hi ⊢
              linear_combination -hi
          have hsub : ({O, k, c2} : Set (Euc 2)) ⊆ K ∪ ({c2} : Set (Euc 2)) := by
            intro x hx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl | rfl
            · exact Set.subset_union_left hOK
            · exact Set.subset_union_left hkK
            · exact Set.subset_union_right rfl
          exact hpair c2 hc2Z y (hSZ hy) hc2y (convexHull_mono hsub hmem')
    · -- `tF` has three elements: `t = tF ⊆ F`, contradicting convex position
      have httF : tF = t :=
        Finset.eq_of_subset_of_card_le htF_sub_t (by rw [hfc]; exact hcard3)
      have : y ∈ convexHull ℝ (↑F : Set (Euc 2)) :=
        convexHull_mono (Finset.coe_subset.mpr htF_sub) (httF.symm ▸ hyt)
      exact hconvS y hy this
  · -- a cap of the image pulls back to a convex-position subset
    exact Or.inr ⟨S, hSZ, by rw [hScard, hSb],
      transport_conv (isCap_inConvexPosition hScap) hSimg⟩

/-- **Angular core, factor-`2` variant.** If `K` has an interior point `O`
such that the directions `z - O` for `z ∈ Z` are pairwise non-parallel and
`|Z| > 2 · (a+b-4 choose a-2)`: split `Z` by a
line through `O` in a generic direction and apply
`planar_dichotomy_halfplane` to the larger side. -/
private theorem planar_dichotomy_intK2 {K : Set (Euc 2)} (hKc : Convex ℝ K)
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {O : Euc 2} (hO : O ∈ interior K)
    (hdir : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → sO O p q ≠ 0)
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : 2 * (a + b - 4).choose (a - 2) < Z.card) :
    (∃ A ⊆ Z, A.card = a ∧
      ∀ y ∈ A, y ∉ convexHull ℝ (K ∪ ((A.erase y : Finset _) : Set _))) ∨
    (∃ B ⊆ Z, B.card = b ∧ InConvexPosition B) := by
  classical
  have hOK : O ∈ K := interior_subset hO
  have hZcard : 3 ≤ Z.card := by
    have h2 : 2 ≤ (a + b - 4).choose (a - 2) := by
      calc 2 ≤ a - 1 := by omega
        _ = (a - 1).choose 1 := (Nat.choose_one_right _).symm
        _ = (a - 1).choose (a - 2) :=
            (Nat.choose_symm (show 1 ≤ a - 1 by omega)).symm
        _ ≤ (a + b - 4).choose (a - 2) := Nat.choose_le_choose _ (by omega)
    omega
  -- no `z ∈ Z` equals `O`
  have hzO : ∀ z ∈ Z, z ≠ O := by
    intro z hz e
    obtain ⟨a₀, ha₀, b₀, hb₀, hne₀⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < Z.card)
    rcases eq_or_ne z a₀ with rfl | hza
    · apply hdir _ hz _ hb₀ hne₀
      rw [e]
      simp [sO]
    · apply hdir _ hz _ ha₀ hza
      rw [e]
      simp [sO]
  -- a slope `m` avoiding all `z`-slopes through `O`
  set badM : Finset ℝ := Z.image fun z ↦
    if z 0 = O 0 then (0 : ℝ) else (z 1 - O 1) / (z 0 - O 0) with hbadM
  obtain ⟨m, -, hm⟩ := Set.Infinite.exists_notMem_finset Set.infinite_univ badM
  set n : Euc 2 := WithLp.toLp 2 fun i : Fin 2 ↦ if i = 0 then -m else 1
    with hndef
  set τ : Euc 2 := WithLp.toLp 2 fun i : Fin 2 ↦ if i = 0 then 1 else m
    with hτdef
  have hdet : τ 0 * n 1 - τ 1 * n 0 ≠ 0 := by
    have e : τ 0 * n 1 - τ 1 * n 0 = 1 + m * m := by simp [hτdef, hndef]
    rw [e]
    nlinarith [sq_nonneg m]
  -- every `z ∈ Z` has `wC z ≠ 0`
  have hWne : ∀ z ∈ Z, wC O n z ≠ 0 := by
    intro z hz hz0
    have hw : z 1 - O 1 = m * (z 0 - O 0) := by
      have e : wC O n z = -m * (z 0 - O 0) + (z 1 - O 1) := by
        simp [wC, dprod, hndef, PiLp.sub_apply]
      rw [e] at hz0
      linarith
    by_cases h0 : z 0 = O 0
    · have h1 : z 1 = O 1 := by
        have hw' : z 1 - O 1 = 0 := by simpa [h0] using hw
        exact sub_eq_zero.mp hw'
      apply hzO z hz
      apply PiLp.ext; intro i
      fin_cases i
      · exact h0
      · exact h1
    · apply hm
      rw [Finset.mem_image]
      refine ⟨z, hz, ?_⟩
      rw [if_neg h0]
      exact (div_eq_iff (sub_ne_zero.mpr h0)).mpr hw
  -- the two open halfplanes cover `Z`
  set W : Finset (Euc 2) := Z.filter fun z ↦ 0 < wC O n z with hWdef
  set W2 : Finset (Euc 2) := Z.filter fun z ↦ wC O n z < 0 with hW2def
  have hWW2 : W ∪ W2 = Z := by
    ext z
    simp only [hWdef, hW2def, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
    · intro hz
      rcases lt_or_gt_of_ne (hWne z hz) with h | h
      · exact Or.inr ⟨hz, h⟩
      · exact Or.inl ⟨hz, h⟩
  have hcardW : W.card + W2.card = Z.card := by
    have hd : Disjoint W W2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : 0 < wC O n x := (Finset.mem_filter.mp hx1).2
      have h2 : wC O n x < 0 := (Finset.mem_filter.mp hx2).2
      linarith
    rw [← Finset.card_union_of_disjoint hd, hWW2]
  by_cases hbig : (a + b - 4).choose (a - 2) < W.card
  · exact planar_dichotomy_halfplane hKc hZ hpair hOK hdir τ n hdet
      (Finset.filter_subset _ _) (fun z hz ↦ (Finset.mem_filter.mp hz).2)
      ha hb hbig
  · have hbig2 : (a + b - 4).choose (a - 2) < W2.card := by omega
    have hdet' : (-τ) 0 * (-n) 1 - (-τ) 1 * (-n) 0 ≠ 0 := by
      have e : (-τ) 0 * (-n) 1 - (-τ) 1 * (-n) 0 =
          τ 0 * n 1 - τ 1 * n 0 := by
        simp [PiLp.neg_apply]
      rw [e]; exact hdet
    have hW2pos : ∀ z ∈ W2, 0 < wC O (-n) z := by
      intro z hz
      have hlt : wC O n z < 0 := (Finset.mem_filter.mp hz).2
      have e : wC O (-n) z = -wC O n z := by
        simp [wC, dprod, PiLp.neg_apply]; ring
      rw [e]; linarith
    exact planar_dichotomy_halfplane hKc hZ hpair hOK hdir (-τ) (-n) hdet'
      (Finset.filter_subset _ _) hW2pos ha hb hbig2

/-- Factor-`2` variant of the `DistinctX` combinatorial core (proved via the
projective halfplane argument of `planar_dichotomy_intK2`). -/
theorem planar_dichotomy_aux2 {K : Set (Euc 2)} (hKc : Convex ℝ K)
    (hKk : IsCompact K)
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hdx : DistinctX Z)
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : 2 * (a + b - 4).choose (a - 2) < Z.card) :
    (∃ A ⊆ Z, A.card = a ∧
      ∀ y ∈ A, y ∉ convexHull ℝ (K ∪ ((A.erase y : Finset _) : Set _))) ∨
    (∃ B ⊆ Z, B.card = b ∧ InConvexPosition B) := by
  classical
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
  · subst hKe
    exact planar_dichotomy_empty hZ hdx ha hb (by omega)
  obtain ⟨O₀, hO₀⟩ := Set.nonempty_iff_ne_empty.mpr hKe
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
  have hcoeff : ∀ pq ∈ Z.offDiag,
      v 0 * (pq.1 1 - pq.2 1) + v 1 * (pq.2 0 - pq.1 0) ≠ 0 := by
    intro pq hpq
    obtain ⟨hp, hq, hne⟩ := Finset.mem_offDiag.mp hpq
    rw [hv0, hv1, one_mul]
    by_cases h0 : pq.1 0 = pq.2 0
    · have h1 : pq.1 1 ≠ pq.2 1 := by
        intro e
        apply hne
        apply PiLp.ext; intro i
        fin_cases i
        · exact h0
        · exact e
      rw [h0]
      simpa using sub_ne_zero.mpr h1
    · have hmem : (pq.2 1 - pq.1 1) / (pq.2 0 - pq.1 0) ∈ badM := by
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
  obtain hA | hB := planar_dichotomy_intK2 hK'c hZ hpair' hOint hdir ha hb hcard
  · obtain ⟨A, hAZ, hAcard, hcap⟩ := hA
    refine Or.inl ⟨A, hAZ, hAcard, fun y hy hmem ↦ hcap y hy ?_⟩
    exact convexHull_mono (Set.union_subset_union_left _ hKK') hmem
  · obtain ⟨B, hBZ, hBcard, hconv⟩ := hB
    exact Or.inr ⟨B, hBZ, hBcard, hconv⟩

end JSPProblem.PlanarDichotomy

/-! ### The main theorem -/

/-- **Factor-`2` variant of the planar dichotomy** (proved by a projective
halfplane argument via `planar_dichotomy_aux2`). -/
theorem planar_dichotomy2 {K : Set (Euc 2)} (hKc : Convex ℝ K)
    (hKk : IsCompact K)
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : 2 * (a + b - 4).choose (a - 2) < Z.card) :
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
  have hcard' : 2 * (a + b - 4).choose (a - 2) < Z'.card := by
    rwa [hcardZ']
  obtain hA | hB := JSPProblem.PlanarDichotomy.planar_dichotomy_aux2 hKc' hKk'
    hZ'' hdx' hpair' ha hb hcard'
  · obtain ⟨A', hA'Z, hA'card, hcap⟩ := hA
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
