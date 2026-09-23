import JSPProblem.PorValtrBase

open Finset
open scoped Nat

noncomputable section
/-! ### Counting infrastructure: `x`-ordered enumerations of caps and cups

The remaining existence clause is proved by the double-counting argument of
[PV02, Theorem 4]: every `(4k+1)`-cap/cup `z` is encoded by its even-indexed
sub-chain `y` (a `(2k+1)`-cap/cup) together with the odd points `z_{2i+1}`,
each of which lies in the `i`-th support region of `y`.  A density
pigeonhole then produces a `y` with `k` dense support regions, and the
sub-chain formed by their left endpoints (plus the last vertex of `y`) is
the desired `(k+1)`-cap/cup. -/

/-- Lexicographic order on `Euc 2` (first coordinate, then second), used to
enumerate finite point sets left-to-right.  Under `DistinctX` it coincides
with the `x`-coordinate order. -/
private noncomputable instance eucLex : LinearOrder (Euc 2) :=
  LinearOrder.lift' (fun p : Euc 2 ↦ (toLex (p 0, p 1) : ℝ ×ₗ ℝ))
    fun a b h ↦ by
      have h0 : a 0 = b 0 := congrArg (fun z : ℝ ×ₗ ℝ ↦ (ofLex z).1) h
      have h1 : a 1 = b 1 := congrArg (fun z : ℝ ×ₗ ℝ ↦ (ofLex z).2) h
      exact PiLp.ext (Fin.forall_fin_two.mpr ⟨h0, h1⟩)

/-- In `eucLex` order, `p < q` means `(p 0, p 1) < (q 0, q 1)` in `ℝ ×ₗ ℝ`. -/
lemma eucLex_lt_def {p q : Euc 2} :
    p < q ↔ (toLex (p 0, p 1) : ℝ ×ₗ ℝ) < toLex (q 0, q 1) :=
  Iff.rfl

/-- In `eucLex` order, `p ≤ q` means `(p 0, p 1) ≤ (q 0, q 1)` in `ℝ ×ₗ ℝ`. -/
lemma eucLex_le_def {p q : Euc 2} :
    p ≤ q ↔ (toLex (p 0, p 1) : ℝ ×ₗ ℝ) ≤ toLex (q 0, q 1) :=
  Iff.rfl

/-- Strict inequality in the first coordinate implies `eucLex`-order. -/
lemma lex_lt_of_x_lt {p q : Euc 2} (h : p 0 < q 0) : p < q :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- For points of a `DistinctX` set, `eucLex`-order is exactly the
`x`-coordinate order. -/
lemma x_lt_of_lex_lt {X : Finset (Euc 2)} (hdx : DistinctX X)
    {p q : Euc 2} (hp : p ∈ X) (hq : q ∈ X) (h : p < q) : p 0 < q 0 := by
  have hne : p ≠ q := ne_of_lt h
  rw [eucLex_lt_def, Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h
  · exact absurd (hdx p hp q hq h) hne

/-- The increasing enumeration of a finite point set (in `eucLex` order). -/
noncomputable abbrev pvEnum {n : ℕ} (s : Finset (Euc 2)) (h : s.card = n) :
    Fin n → Euc 2 := s.orderEmbOfFin h

lemma pvEnum_mem {n : ℕ} {s : Finset (Euc 2)} (h : s.card = n) (i : Fin n) :
    pvEnum s h i ∈ s := Finset.orderEmbOfFin_mem s h i

lemma pvEnum_image {n : ℕ} {s : Finset (Euc 2)} (h : s.card = n) :
    Finset.image (pvEnum s h) Finset.univ = s := by
  apply Finset.coe_injective
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact Finset.range_orderEmbOfFin s h

lemma pvEnum_strictMono {n : ℕ} {s : Finset (Euc 2)} (h : s.card = n) :
    StrictMono (pvEnum s h) := (s.orderEmbOfFin h).strictMono

/-- For a subset of a `DistinctX` set, the enumeration is `x`-strictly
monotone. -/
lemma pvEnum_xmono {n : ℕ} {s : Finset (Euc 2)} (h : s.card = n)
    {X : Finset (Euc 2)} (hsX : s ⊆ X) (hdx : DistinctX X) :
    StrictMono (fun i ↦ (pvEnum s h i) 0) :=
  fun _ _ hij ↦ x_lt_of_lex_lt hdx
    (hsX (pvEnum_mem h _)) (hsX (pvEnum_mem h _)) (pvEnum_strictMono h hij)

noncomputable instance decCapOrCup (σ : Bool) :
    DecidablePred fun S : Finset (Euc 2) ↦ if σ then IsCap S else IsCup S :=
  Classical.decPred _

/-- The `(m+1)`-subsets of `X` forming a cap (`σ = true`) or cup
(`σ = false`). -/
noncomputable def pvSets (X : Finset (Euc 2)) (σ : Bool) (m : ℕ) :
    Finset (Finset (Euc 2)) :=
  (X.powersetCard (m + 1)).filter fun S ↦ if σ then IsCap S else IsCup S

lemma mem_pvSets {X : Finset (Euc 2)} {σ : Bool} {m : ℕ}
    {S : Finset (Euc 2)} :
    S ∈ pvSets X σ m ↔
      S ⊆ X ∧ S.card = m + 1 ∧ (if σ then IsCap S else IsCup S) := by
  unfold pvSets
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  exact and_assoc

/-- The `eucLex`-increasing enumerations of the cap/cup `(m+1)`-subsets of
`X`.  Under `DistinctX X` they enumerate left-to-right in `x`. -/
noncomputable def pvSeqs (X : Finset (Euc 2)) (σ : Bool) (m : ℕ) :
    Finset (Fin (m + 1) → Euc 2) :=
  @Finset.image _ _ (Classical.decEq _)
    (fun s : {S // S ∈ pvSets X σ m} ↦
      pvEnum s.1 ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp s.2).1).2))
    (pvSets X σ m).attach

lemma mem_pvSeqs {X : Finset (Euc 2)} {σ : Bool} {m : ℕ}
    {z : Fin (m + 1) → Euc 2} :
    z ∈ pvSeqs X σ m ↔
      StrictMono z ∧ (∀ i, z i ∈ X) ∧
        (if σ then IsCap (Finset.image z Finset.univ)
              else IsCup (Finset.image z Finset.univ)) := by
  unfold pvSeqs
  rw [@Finset.mem_image _ _ (Classical.decEq _) _ _ _]
  constructor
  · rintro ⟨s, -, rfl⟩
    obtain ⟨hsX, -⟩ :=
      Finset.mem_powersetCard.mp (Finset.mem_filter.mp s.2).1
    have hshape := (Finset.mem_filter.mp s.2).2
    exact ⟨pvEnum_strictMono _, fun i ↦ hsX (pvEnum_mem _ i),
      by rw [pvEnum_image _]; exact hshape⟩
  · rintro ⟨hmono, hX, hshape⟩
    have hcard : (Finset.image z Finset.univ).card = m + 1 := by
      rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ,
        Fintype.card_fin]
    have hmem : Finset.image z Finset.univ ∈ pvSets X σ m :=
      mem_pvSets.mpr ⟨fun p hp ↦ by
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp; exact hX i,
        hcard, hshape⟩
    refine ⟨⟨Finset.image z Finset.univ, hmem⟩, Finset.mem_attach _ _, ?_⟩
    exact (Finset.orderEmbOfFin_unique hcard
      (fun i ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hmono).symm

lemma card_pvSeqs {X : Finset (Euc 2)} {σ : Bool} {m : ℕ} :
    #(pvSeqs X σ m) = #(pvSets X σ m) := by
  have hinj : Function.Injective
      (fun s : {S // S ∈ pvSets X σ m} ↦
        pvEnum s.1 ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp s.2).1).2)) := by
    intro a b hab
    apply Subtype.ext
    have e1 : Finset.image (pvEnum a.1
        ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp a.2).1).2))
        Finset.univ = a.1 := pvEnum_image _
    have e2 : Finset.image (pvEnum b.1
        ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp b.2).1).2))
        Finset.univ = b.1 := pvEnum_image _
    rw [← e1, ← e2]
    exact congrArg (fun f ↦ Finset.image f Finset.univ) hab
  unfold pvSeqs
  rw [@Finset.card_image_of_injective _ _ _ (Classical.decEq _) _ hinj,
    Finset.card_attach]

lemma pvSets_le {X : Finset (Euc 2)} {σ : Bool} {m : ℕ} :
    #(pvSets X σ m) ≤ X.card.choose (m + 1) := by
  unfold pvSets
  exact (Finset.card_filter_le _ _).trans (Finset.card_powersetCard _ _).le

lemma pvSeqs_le {X : Finset (Euc 2)} {σ : Bool} {m : ℕ} :
    #(pvSeqs X σ m) ≤ X.card.choose (m + 1) :=
  card_pvSeqs.trans_le pvSets_le

noncomputable instance decMemSupp {m : ℕ} (y : Fin (m + 1) → Euc 2) (σ : Bool)
    (i : Fin m) : DecidablePred fun x : Euc 2 ↦ x ∈ supportOf y σ i :=
  Classical.decPred _

/-- The points of `X` lying in the `i`-th support region of `y`. -/
noncomputable def pvSupp (X : Finset (Euc 2)) {m : ℕ}
    (y : Fin (m + 1) → Euc 2) (σ : Bool) (i : Fin m) : Finset (Euc 2) :=
  X.filter (· ∈ supportOf y σ i)

lemma mem_pvSupp {X : Finset (Euc 2)} {m : ℕ} {y : Fin (m + 1) → Euc 2}
    {σ : Bool} {i : Fin m} {p : Euc 2} :
    p ∈ pvSupp X y σ i ↔ p ∈ X ∧ p ∈ supportOf y σ i :=
  Finset.mem_filter

lemma pvSupp_le_card {X : Finset (Euc 2)} {m : ℕ}
    (y : Fin (m + 1) → Euc 2) (σ : Bool) (i : Fin m) :
    #(pvSupp X y σ i) ≤ X.card :=
  Finset.card_filter_le _ _

lemma pv_ncard_supp {X : Finset (Euc 2)} {m : ℕ}
    (y : Fin (m + 1) → Euc 2) (σ : Bool) (i : Fin m) :
    (supportOf y σ i ∩ (X : Set (Euc 2))).ncard = #(pvSupp X y σ i) := by
  have e : (supportOf y σ i ∩ ↑X : Set (Euc 2)) = ↑(pvSupp X y σ i) := by
    ext p
    rw [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_coe, mem_pvSupp]
    exact and_comm
  rw [e, Set.ncard_coe_finset]

/-- The even-indexed sub-chain `z_0, z_2, …, z_{4k}` of a `(4k+1)`-chain. -/
abbrev pvEven {k : ℕ} (z : Fin (4 * k + 1) → Euc 2) :
    Fin (2 * k + 1) → Euc 2 :=
  fun j ↦ z ⟨2 * j.val, by have := j.isLt; omega⟩

/-- The odd-indexed sub-chain `z_1, z_3, …, z_{4k-1}` of a `(4k+1)`-chain. -/
abbrev pvOdd {k : ℕ} (z : Fin (4 * k + 1) → Euc 2) :
    Fin (2 * k) → Euc 2 :=
  fun i ↦ z ⟨2 * i.val + 1, by have := i.isLt; omega⟩

/-- A member of `pvSeqs` is `x`-strictly increasing (under `DistinctX`). -/
lemma pvSeqs_xmono {X : Finset (Euc 2)} {σ : Bool} {m : ℕ}
    {z : Fin (m + 1) → Euc 2} (hz : z ∈ pvSeqs X σ m) (hdx : DistinctX X) :
    StrictMono fun i ↦ (z i) 0 :=
  fun a b hab ↦ x_lt_of_lex_lt hdx ((mem_pvSeqs.mp hz).2.1 a)
    ((mem_pvSeqs.mp hz).2.1 b) ((mem_pvSeqs.mp hz).1 hab)

/-- A member of `pvSeqs` is `pvShaped`. -/
lemma pvSeqs_shaped {X : Finset (Euc 2)} {σ : Bool} {m : ℕ}
    {z : Fin (m + 1) → Euc 2} (hz : z ∈ pvSeqs X σ m) (hdx : DistinctX X) :
    pvShaped z σ :=
  pvShaped_of_capOrCup (pvSeqs_xmono hz hdx) (mem_pvSeqs.mp hz).2.2

/-- `IsCup` is hereditary under taking subsets. -/
lemma pv_isCup_mono {S T : Finset (Euc 2)} (hST : S ⊆ T) (hT : IsCup T) :
    IsCup S := by
  intro p hp
  obtain ⟨a, b, hb, hall⟩ := hT p (hST hp)
  exact ⟨a, b, hb, fun q hq hqp ↦ hall q (hST hq) hqp⟩

/-- `IsCap` is hereditary under taking subsets. -/
lemma pv_isCap_mono {S T : Finset (Euc 2)} (hST : S ⊆ T) (hT : IsCap T) :
    IsCap S := by
  intro p hp
  obtain ⟨a, b, hb, hall⟩ := hT p (hST hp)
  exact ⟨a, b, hb, fun q hq hqp ↦ hall q (hST hq) hqp⟩

/-- The even sub-chain of a `(4k+1)`-cap/cup sequence is itself a
`(2k+1)`-cap/cup sequence. -/
lemma pvEven_mem {k : ℕ} {X : Finset (Euc 2)} {σ : Bool}
    {z : Fin (4 * k + 1) → Euc 2} (hz : z ∈ pvSeqs X σ (4 * k)) :
    pvEven z ∈ pvSeqs X σ (2 * k) := by
  obtain ⟨hmono, hX, hshape⟩ := mem_pvSeqs.mp hz
  refine mem_pvSeqs.mpr ⟨?_, ?_, ?_⟩
  · intro a b hab
    exact hmono (Fin.mk_lt_mk.mpr (by have := hab; omega))
  · intro j; exact hX _
  · have hsub : Finset.image (pvEven z) Finset.univ ⊆
        Finset.image z Finset.univ := by
      intro p hp
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨⟨2 * j.val, by have := j.isLt; omega⟩,
        Finset.mem_univ _, rfl⟩
    cases σ
    · exact pv_isCup_mono hsub hshape
    · exact pv_isCap_mono hsub hshape

/-- **Odd points lie in support regions**: for a `(4k+1)`-cap/cup `z`, the
odd-indexed point `z_{2i+1}` lies in the `i`-th support region of the even
sub-chain `z_0, z_2, …`. -/
lemma pv_odd_mem_supp {k : ℕ} {X : Finset (Euc 2)} {σ : Bool}
    {z : Fin (4 * k + 1) → Euc 2} (hz : z ∈ pvSeqs X σ (4 * k)) (hdx : DistinctX X)
    (i : Fin (2 * k)) :
    pvOdd z i ∈ supportOf (pvEven z) σ i := by
  obtain ⟨hmono, hX, hshape0⟩ := mem_pvSeqs.mp hz
  have hxmono : StrictMono fun t ↦ (z t) 0 :=
    fun a b hab ↦ x_lt_of_lex_lt hdx (hX a) (hX b) (hmono hab)
  have hshape : pvShaped z σ := pvShaped_of_capOrCup hxmono hshape0
  rw [mem_supportOf_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- own edge: `ε·cross(z_{2i}, z_{2i+2}, z_{2i+1}) > 0`
    show (0:ℝ) < pvSgn σ * pvCross (z ⟨2 * i.val, by omega⟩)
        (z ⟨2 * i.val + 2, by omega⟩) (pvOdd z i)
    have e : pvCross (z ⟨2 * i.val, by omega⟩) (z ⟨2 * i.val + 2, by omega⟩)
        (pvOdd z i) =
        -pvCross (z ⟨2 * i.val, by omega⟩) (pvOdd z i)
          (z ⟨2 * i.val + 2, by omega⟩) := pvCross_swap23 _ _ _
    rw [e, mul_neg]
    exact neg_pos.mpr (hshape ⟨2 * i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩
      ⟨2 * i.val + 2, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
      (Fin.mk_lt_mk.mpr (by omega)))
  · -- left edge: `ε·cross(y_l, y_i, z_{2i+1}) < 0`
    rcases Nat.eq_zero_or_pos i.val with hi0 | hi0
    · -- `i = 0`: `l = y_{2k} = z_{4k}`; cyclic shift of the triple `(0,1,4k)`
      have e : pvEven z ⟨(i.val + 2 * k) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩
          = z ⟨4 * k, by omega⟩ :=
        congrArg z (Fin.ext_iff.mpr (by
          show 2 * ((i.val + 2 * k) % (2 * k + 1)) = 4 * k
          rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 2 * k < 2 * k + 1)]
          omega))
      rw [e]
      have e0 : pvEven z ⟨i.val, by omega⟩ = z ⟨0, by omega⟩ :=
        congrArg z (Fin.ext_iff.mpr (by show 2 * i.val = 0; omega))
      rw [e0]
      have e1 : pvOdd z i = z ⟨1, by omega⟩ :=
        congrArg z (Fin.ext_iff.mpr (by show 2 * i.val + 1 = 1; omega))
      rw [e1, pvCross_cyc]
      exact hshape ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨4 * k, by omega⟩
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
    · -- `i ≥ 1`: `l = y_{i-1} = z_{2i-2}`; plain triple `(2i-2, 2i, 2i+1)`
      have e : pvEven z ⟨(i.val + 2 * k) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩
          = z ⟨2 * i.val - 2, by omega⟩ :=
        congrArg z (Fin.ext_iff.mpr (by
          show 2 * ((i.val + 2 * k) % (2 * k + 1)) = 2 * i.val - 2
          have h : i.val + 2 * k = (i.val - 1) + (2 * k + 1) := by omega
          rw [h, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega : i.val - 1 < 2 * k + 1)]
          omega))
      rw [e]
      have e0 : pvEven z ⟨i.val, by omega⟩ = z ⟨2 * i.val, by omega⟩ := rfl
      rw [e0]
      exact hshape ⟨2 * i.val - 2, by omega⟩ ⟨2 * i.val, by omega⟩
        ⟨2 * i.val + 1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
        (Fin.mk_lt_mk.mpr (by omega))
  · -- right edge: `ε·cross(y_{i+1}, y_r, z_{2i+1}) < 0`
    by_cases hjc : i.val + 2 ≤ 2 * k
    · -- `r = y_{i+2} = z_{2i+4}`; two cyclic shifts of `(2i+1, 2i+2, 2i+4)`
      have e : pvEven z ⟨(i.val + 2) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩
          = z ⟨2 * i.val + 4, by omega⟩ :=
        congrArg z (Fin.ext_iff.mpr (by
          show 2 * ((i.val + 2) % (2 * k + 1)) = 2 * i.val + 4
          rw [Nat.mod_eq_of_lt (by omega : i.val + 2 < 2 * k + 1)]
          omega))
      rw [e]
      have e0 : pvEven z ⟨i.val + 1, by omega⟩ = z ⟨2 * i.val + 2, by omega⟩ := rfl
      rw [e0]
      have e2 : pvCross (z ⟨2 * i.val + 2, by omega⟩)
          (z ⟨2 * i.val + 4, by omega⟩) (pvOdd z i) =
          pvCross (pvOdd z i) (z ⟨2 * i.val + 2, by omega⟩)
            (z ⟨2 * i.val + 4, by omega⟩) :=
        (pvCross_cyc _ _ _).trans (pvCross_cyc _ _ _)
      rw [e2]
      exact hshape ⟨2 * i.val + 1, by omega⟩ ⟨2 * i.val + 2, by omega⟩
        ⟨2 * i.val + 4, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
        (Fin.mk_lt_mk.mpr (by omega))
    · -- `i = 2k-1`: `r = y_0 = z_0`; cyclic shift of the triple `(0, 4k-1, 4k)`
      have e : pvEven z ⟨(i.val + 2) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩
          = z ⟨0, by omega⟩ :=
        congrArg z (Fin.ext_iff.mpr (by
          show 2 * ((i.val + 2) % (2 * k + 1)) = 0
          have hi : i.val + 2 = 2 * k + 1 := by omega
          rw [hi, Nat.mod_self, Nat.mul_zero]))
      rw [e]
      have e0 : pvEven z ⟨i.val + 1, by omega⟩ = z ⟨4 * k, by omega⟩ :=
        congrArg z (Fin.ext_iff.mpr (by show 2 * (i.val + 1) = 4 * k; omega))
      rw [e0]
      have e1 : pvOdd z i = z ⟨4 * k - 1, by omega⟩ :=
        congrArg z (Fin.ext_iff.mpr (by show 2 * i.val + 1 = 4 * k - 1; omega))
      rw [e1, pvCross_cyc]
      exact hshape ⟨0, by omega⟩ ⟨4 * k - 1, by omega⟩ ⟨4 * k, by omega⟩
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

/-- **Fiber bound**: the number of `(4k+1)`-cap/cup sequences is at most the
sum, over `(2k+1)`-cap/cup sequences `y`, of the product of the sizes of
`y`'s support regions.  The encoding `z ↦ (even z, odd z)` is injective and
lands in `Σ y, Πᵢ Tᵢ(y)`. -/
lemma pv_fiber_bound {k : ℕ} {X : Finset (Euc 2)} (hdx : DistinctX X)
    (σ : Bool) :
    #(pvSeqs X σ (4 * k)) ≤
      ∑ y ∈ pvSeqs X σ (2 * k), ∏ i : Fin (2 * k), #(pvSupp X y σ i) := by
  classical
  have hinj := Finset.card_le_card_of_injOn
    (fun z ↦ (⟨pvEven z, pvOdd z⟩ :
      Σ _ : Fin (2 * k + 1) → Euc 2, Fin (2 * k) → Euc 2))
    (show Set.MapsTo
      (fun z ↦ (⟨pvEven z, pvOdd z⟩ :
        Σ _ : Fin (2 * k + 1) → Euc 2, Fin (2 * k) → Euc 2))
      ↑(pvSeqs X σ (4 * k))
      ↑((pvSeqs X σ (2 * k)).sigma
        fun y ↦ Fintype.piFinset fun i : Fin (2 * k) ↦ pvSupp X y σ i) from
      fun z hz ↦ by
        rw [Finset.mem_coe, Finset.mem_sigma]
        refine ⟨pvEven_mem hz, ?_⟩
        rw [Fintype.mem_piFinset]
        intro i
        rw [mem_pvSupp]
        exact ⟨(mem_pvSeqs.mp hz).2.1 _, pv_odd_mem_supp hz hdx i⟩)
    (show (↑(pvSeqs X σ (4 * k)) : Set _).InjOn
      (fun z ↦ (⟨pvEven z, pvOdd z⟩ :
        Σ _ : Fin (2 * k + 1) → Euc 2, Fin (2 * k) → Euc 2)) from
      fun z₁ _ z₂ _ heq ↦ by
        have hev : pvEven z₁ = pvEven z₂ := congrArg Sigma.fst heq
        have hod : pvOdd z₁ = pvOdd z₂ :=
          eq_of_heq (Sigma.mk.inj_iff.mp heq).2
        funext t
        rcases Nat.mod_two_eq_zero_or_one t.val with hmod | hmod
        · have ht : t = ⟨2 * (t.val / 2), by have := t.isLt; omega⟩ :=
            Fin.ext_iff.mpr (by show t.val = 2 * (t.val / 2); omega)
          have e1 : z₁ t = pvEven z₁ ⟨t.val / 2, by have := t.isLt; omega⟩ :=
            congrArg z₁ ht
          have e2 : z₂ t = pvEven z₂ ⟨t.val / 2, by have := t.isLt; omega⟩ :=
            congrArg z₂ ht
          rw [e1, e2]; exact congrFun hev _
        · have ht : t = ⟨2 * (t.val / 2) + 1, by have := t.isLt; omega⟩ :=
            Fin.ext_iff.mpr (by show t.val = 2 * (t.val / 2) + 1; omega)
          have e1 : z₁ t = pvOdd z₁ ⟨t.val / 2, by have := t.isLt; omega⟩ :=
            congrArg z₁ ht
          have e2 : z₂ t = pvOdd z₂ ⟨t.val / 2, by have := t.isLt; omega⟩ :=
            congrArg z₂ ht
          rw [e1, e2]; exact congrFun hod _)
  refine hinj.trans ?_
  rw [Finset.card_sigma]
  simp only [Fintype.card_piFinset]
  exact le_rfl

/-- The number of `s`-subsets of `X` containing a fixed `t`-subset `G ⊆ X`
equals `(X.card - t).choose (s - t)`, via the bijection `S ↦ S \ G`. -/
lemma pv_powersetCard_sup {X : Finset (Euc 2)} {G : Finset (Euc 2)}
    (hGX : G ⊆ X) {t s : ℕ} (hts : t ≤ s) (hGt : G.card = t) :
    ((X.powersetCard s).filter fun S ↦ G ⊆ S).card =
      (X.card - t).choose (s - t) := by
  classical
  have hbij : ((X.powersetCard s).filter fun S ↦ G ⊆ S).card =
      ((X \ G).powersetCard (s - t)).card := by
    apply Finset.card_bij (fun S _ ↦ S \ G)
    · intro S hS
      rw [Finset.mem_filter] at hS
      obtain ⟨hS, hGS⟩ := hS
      obtain ⟨hSX, hSc⟩ := Finset.mem_powersetCard.mp hS
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.sdiff_subset_sdiff hSX (Finset.Subset.refl _),
        by rw [Finset.card_sdiff_of_subset hGS, hSc, hGt]⟩
    · intro S₁ hS₁ S₂ hS₂ heq
      rw [Finset.mem_filter] at hS₁ hS₂
      have e1 : G ∪ (S₁ \ G) = S₁ := Finset.union_sdiff_of_subset hS₁.2
      have e2 : G ∪ (S₂ \ G) = S₂ := Finset.union_sdiff_of_subset hS₂.2
      rw [← e1, ← e2, heq]
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨hTXG, hTc⟩ := hT
      refine ⟨G ∪ T, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨Finset.union_subset hGX (hTXG.trans Finset.sdiff_subset), ?_⟩,
          Finset.subset_union_left⟩
        have hdisj : Disjoint G T := Finset.disjoint_left.mpr fun p hpG hpT ↦
          (Finset.mem_sdiff.mp (hTXG hpT)).2 hpG
        rw [Finset.card_union_of_disjoint hdisj, hGt, hTc]
        omega
      · ext p
        rw [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hpG | hpT, hpG'⟩
          · exact absurd hpG hpG'
          · exact hpT
        · intro hpT
          exact ⟨Or.inr hpT, fun hpG ↦ (Finset.mem_sdiff.mp (hTXG hpT)).2 hpG⟩
  rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset hGX, hGt]

/-- **Counting step**: every `s`-subset of `X` contains a `t`-cap or `t`-cup
(`cupsCaps`), so `X.card.choose s` is at most the number of cap/cup
`t`-subsets of `X` times `(X.card - t).choose (s - t)`. -/
lemma pv_choose_count {X : Finset (Euc 2)}
    (hX : InGeneralPosition (X : Set (Euc 2))) (hdx : DistinctX X)
    {t s : ℕ} (ht : 2 ≤ t) (hts : t ≤ s)
    (hs : (t + t - 4).choose (t - 2) + 1 ≤ s) (hsn : s ≤ X.card) :
    X.card.choose s ≤
      ((pvSets X true (t - 1)).card + (pvSets X false (t - 1)).card) *
        (X.card - t).choose (s - t) := by
  classical
  set Good := pvSets X true (t - 1) ∪ pvSets X false (t - 1) with hGood
  have hmem : ∀ S ∈ X.powersetCard s, ∃ G ∈ Good, G ⊆ S := by
    intro S hS
    obtain ⟨hSX, hSc⟩ := Finset.mem_powersetCard.mp hS
    have hgp : InGeneralPosition (S : Set (Euc 2)) :=
      inGeneralPosition_mono hX (Finset.coe_subset.mpr hSX)
    have hdxS : DistinctX S := fun p hp q hq hpq ↦ hdx p (hSX hp) q (hSX hq) hpq
    obtain ⟨G, hGS, hG⟩ := cupsCaps ht ht hgp hdxS (hSc ▸ hs)
    rcases hG with ⟨hGc, hGsh⟩ | ⟨hGc, hGsh⟩
    · exact ⟨G, Finset.mem_union_right _
        (mem_pvSets.mpr ⟨hGS.trans hSX, by rw [hGc]; omega, hGsh⟩), hGS⟩
    · exact ⟨G, Finset.mem_union_left _
        (mem_pvSets.mpr ⟨hGS.trans hSX, by rw [hGc]; omega, hGsh⟩), hGS⟩
  have hbelow : ∀ G ∈ Good, ((X.powersetCard s).bipartiteBelow
      (fun S G ↦ G ⊆ S) G).card ≤ (X.card - t).choose (s - t) := by
    intro G hG
    have hGX : G ⊆ X := by
      rcases Finset.mem_union.mp hG with h | h <;> exact (mem_pvSets.mp h).1
    have hGt : G.card = t := by
      rcases Finset.mem_union.mp hG with h | h <;>
        · have h' := (mem_pvSets.mp h).2.1; omega
    have e : (X.powersetCard s).bipartiteBelow (fun S G ↦ G ⊆ S) G =
        (X.powersetCard s).filter fun S ↦ G ⊆ S := rfl
    rw [e, pv_powersetCard_sup hGX hts hGt]
  have key := Finset.card_mul_le_card_mul (m := 1)
    (fun (S : Finset (Euc 2)) (G : Finset (Euc 2)) ↦ G ⊆ S)
    (fun S hS ↦ Finset.card_pos.mpr (by
      obtain ⟨G, hG, hGS⟩ := hmem S hS
      exact ⟨G, (Finset.mem_bipartiteAbove (fun (S : Finset (Euc 2)) (G : Finset (Euc 2)) ↦
        G ⊆ S)).mpr ⟨hG, hGS⟩⟩))
    hbelow
  rw [mul_one, Finset.card_powersetCard, hGood] at key
  exact key.trans (Nat.mul_le_mul (Finset.card_union_le _ _) (le_refl _))

/-- `(n - t + 1)^t` lower-bounds the descending factorial `n.descFactorial t`
when `t ≤ n`. -/
lemma pow_le_descFactorial {n : ℕ} : ∀ {t : ℕ}, t ≤ n →
    (n - t + 1) ^ t ≤ n.descFactorial t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have e : n - (j + 1) + 1 = n - j := by omega
    rw [e, pow_succ', Nat.descFactorial_succ]
    have h1 : (n - j) ^ j ≤ n.descFactorial j :=
      (Nat.pow_le_pow_left (by omega : n - j ≤ n - j + 1) _).trans (ih (by omega))
    exact Nat.mul_le_mul (le_refl _) h1

/-- **Final arithmetic estimate**: the density threshold `2^{40k}` is so large
that if `2^{40k·(k+1)} · ∏ |Tᵢ(y)| ≤ n^{k-1}(n-1)^{k+1}` then the counting
lower bound `2·C(n,2k+1)·C(s,4k+1)·∏ ≥ C(n,4k+1)` cannot hold.  Multiplying
through by `(4k+1)!` turns the binomial coefficients into descending
factorials. -/
lemma pv_arith {k n s : ℕ} (hk : 1 ≤ k) (hn : 2 ^ (40 * k) ≤ n)
    (hs : s ≤ 2 ^ (8 * k)) :
    2 * n.choose (2 * k + 1) * s.choose (4 * k + 1) * n ^ (k - 1) * (n - 1) ^ (k + 1) <
      2 ^ (40 * k * (k + 1)) * n.choose (4 * k + 1) := by
  have h8k : 8 * k ≤ n := by
    calc 8 * k ≤ 2 ^ (8 * k) := by
          have h : 8 * k < 2 ^ (8 * k) :=
            Nat.lt_pow_self (a := 2) (n := 8 * k) (by norm_num : (1:ℕ) < 2)
          omega
      _ ≤ 2 ^ (40 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ n := hn
  have h41n : 4 * k + 1 ≤ n := by omega
  have hdesclow : (n - 4 * k) ^ (4 * k + 1) ≤ n.descFactorial (4 * k + 1) := by
    have h := pow_le_descFactorial h41n
    rwa [show n - (4 * k + 1) + 1 = n - 4 * k by omega] at h
  have hdescup : s.descFactorial (4 * k + 1) ≤ s ^ (4 * k + 1) :=
    Nat.descFactorial_le_pow _ _
  have hcn : n.choose (2 * k + 1) ≤ n ^ (2 * k + 1) := Nat.choose_le_pow _ _
  have hn1 : (n - 1) ^ (k + 1) ≤ n ^ (k + 1) :=
    Nat.pow_le_pow_left (by omega : n - 1 ≤ n) _
  have hpow : 2 * n ^ (2 * k + 1) * s ^ (4 * k + 1) * n ^ (k - 1) * n ^ (k + 1) <
      2 ^ (40 * k * (k + 1)) * (n - 4 * k) ^ (4 * k + 1) := by
    have hs' : s ^ (4 * k + 1) ≤ 2 ^ (8 * k * (4 * k + 1)) := by
      calc s ^ (4 * k + 1) ≤ (2 ^ (8 * k)) ^ (4 * k + 1) :=
            Nat.pow_le_pow_left hs _
        _ = 2 ^ (8 * k * (4 * k + 1)) := by rw [← pow_mul]
    have hn' : n ^ (4 * k + 1) ≤ 2 ^ (4 * k + 1) * (n - 4 * k) ^ (4 * k + 1) := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left (by omega : n ≤ 2 * (n - 4 * k)) _
    have hexp : 8 * k * (4 * k + 1) + (4 * k + 2) < 40 * k * (k + 1) := by
      nlinarith [hk]
    have hnp : 0 < (n - 4 * k) ^ (4 * k + 1) := by
      apply pow_pos; omega
    calc 2 * n ^ (2 * k + 1) * s ^ (4 * k + 1) * n ^ (k - 1) * n ^ (k + 1)
        = 2 * s ^ (4 * k + 1) * n ^ (4 * k + 1) := by
          have e : n ^ (2 * k + 1) * n ^ (k - 1) * n ^ (k + 1) = n ^ (4 * k + 1) := by
            rw [← pow_add, ← pow_add]
            congr 1; omega
          calc 2 * n ^ (2 * k + 1) * s ^ (4 * k + 1) * n ^ (k - 1) * n ^ (k + 1)
              = 2 * s ^ (4 * k + 1) * (n ^ (2 * k + 1) * n ^ (k - 1) * n ^ (k + 1)) := by
                ring
            _ = 2 * s ^ (4 * k + 1) * n ^ (4 * k + 1) := by rw [e]
      _ ≤ 2 * 2 ^ (8 * k * (4 * k + 1)) * (2 ^ (4 * k + 1) * (n - 4 * k) ^ (4 * k + 1)) := by
          gcongr
      _ = 2 ^ (8 * k * (4 * k + 1) + (4 * k + 2)) * (n - 4 * k) ^ (4 * k + 1) := by
          ring
      _ < 2 ^ (40 * k * (k + 1)) * (n - 4 * k) ^ (4 * k + 1) :=
          Nat.mul_lt_mul_of_pos_right
            (pow_lt_pow_right₀ (by norm_num : (1:ℕ) < 2) hexp) hnp
  have hf : (4 * k + 1) ! * n.choose (4 * k + 1) = n.descFactorial (4 * k + 1) :=
    (Nat.descFactorial_eq_factorial_mul_choose n (4 * k + 1)).symm
  have hfs : (4 * k + 1) ! * s.choose (4 * k + 1) = s.descFactorial (4 * k + 1) :=
    (Nat.descFactorial_eq_factorial_mul_choose s (4 * k + 1)).symm
  have hmul : (4 * k + 1) ! *
        (2 * n.choose (2 * k + 1) * s.choose (4 * k + 1) * n ^ (k - 1) * (n - 1) ^ (k + 1)) <
      (4 * k + 1) ! * (2 ^ (40 * k * (k + 1)) * n.choose (4 * k + 1)) := by
    have e1 : (4 * k + 1) ! *
          (2 * n.choose (2 * k + 1) * s.choose (4 * k + 1) * n ^ (k - 1) * (n - 1) ^ (k + 1))
        = 2 * n.choose (2 * k + 1) * ((4 * k + 1) ! * s.choose (4 * k + 1)) *
            n ^ (k - 1) * (n - 1) ^ (k + 1) := by ring
    have e2 : (4 * k + 1) ! * (2 ^ (40 * k * (k + 1)) * n.choose (4 * k + 1))
        = 2 ^ (40 * k * (k + 1)) * ((4 * k + 1) ! * n.choose (4 * k + 1)) := by ring
    rw [e1, e2, hf, hfs]
    calc 2 * n.choose (2 * k + 1) * s.descFactorial (4 * k + 1) * n ^ (k - 1) * (n - 1) ^ (k + 1)
        ≤ 2 * n ^ (2 * k + 1) * s ^ (4 * k + 1) * n ^ (k - 1) * n ^ (k + 1) := by
          gcongr
      _ < 2 ^ (40 * k * (k + 1)) * (n - 4 * k) ^ (4 * k + 1) := hpow
      _ ≤ _ := by gcongr
  rcases Nat.lt_or_ge _ _ with h | h
  · exact h
  · exact absurd (Nat.mul_le_mul (le_refl _) h) (Nat.not_le.mpr hmul)

/-- Indices into a `(2k+1)`-chain picking the left endpoints of the `k` edges
chosen by `e`, plus the last vertex `2k`. -/
def pvIdx {k : ℕ} (e : Fin k ↪o Fin (2 * k)) (a : ℕ) : ℕ :=
  if h : a < k then (e ⟨a, h⟩).val else 2 * k

lemma pvIdx_lt {k : ℕ} (e : Fin k ↪o Fin (2 * k)) (a : ℕ) :
    pvIdx e a < 2 * k + 1 := by
  unfold pvIdx
  split
  · rename_i h
    have h' := (e ⟨a, h⟩).isLt; omega
  · omega

lemma pvIdx_of_lt {k : ℕ} (e : Fin k ↪o Fin (2 * k)) {a : ℕ} (h : a < k) :
    pvIdx e a = (e ⟨a, h⟩).val := dif_pos h

lemma pvIdx_of_not_lt {k : ℕ} (e : Fin k ↪o Fin (2 * k)) {a : ℕ}
    (h : ¬ a < k) : pvIdx e a = 2 * k := dif_neg h

/-- Rewriting `y` at a `pvIdx`-produced `Fin` index: only the value matters. -/
lemma pvIdx_eval {k : ℕ} (e : Fin k ↪o Fin (2 * k)) (y : Fin (2 * k + 1) → Euc 2)
    {a : ℕ} {i : Fin (2 * k + 1)} (h : pvIdx e a = i.val) :
    y ⟨pvIdx e a, pvIdx_lt e a⟩ = y i :=
  congrArg y (Fin.ext h)

lemma pvIdx_strictMono {k : ℕ} (e : Fin k ↪o Fin (2 * k)) {a b : ℕ}
    (hab : a < b) (hb : b ≤ k) : pvIdx e a < pvIdx e b := by
  rcases lt_or_eq_of_le hb with hbk | hbk
  · rw [pvIdx_of_lt e (by omega : a < k), pvIdx_of_lt e hbk]
    exact e.strictMono (Fin.mk_lt_mk.mpr hab)
  · rw [hbk, pvIdx_of_not_lt e (by omega : ¬ k < k),
      pvIdx_of_lt e (by omega : a < k)]
    exact (e ⟨a, by omega⟩).isLt

/-- **Sub-chain containment**: the `j`-th support region of the `(k+1)`-chain
formed by the left endpoints of the `k` edges `e j` plus the last vertex of a
`pvShaped` x-monotone `(2k+1)`-chain `y` contains the `e j`-th support region
of `y`.  For `j = 0` the left wraparound chord is `y_{2k}y_{e 0}`; for
`j = k-1` the right wraparound chord is `y_{2k}y_{e 0}`; interior indices use
the neighbouring `e`-edges. -/
lemma pv_supp_subseq {k : ℕ} {y : Fin (2 * k + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (y i) 0) {σ : Bool} (hshape : pvShaped y σ)
    (e : Fin k ↪o Fin (2 * k)) (j : Fin k) {p : Euc 2}
    (hp : p ∈ supportOf y σ (e j)) :
    p ∈ supportOf (fun i : Fin (k + 1) ↦ y ⟨pvIdx e i.val, pvIdx_lt e _⟩) σ j := by
  have hev : ∀ a b : Fin k, a < b → (e a).val < (e b).val :=
    fun a b h ↦ e.strictMono h
  have hej : ∀ a : Fin k, (e a).val < 2 * k := fun a ↦ (e a).isLt
  rw [mem_supportOf_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- `0 < ε·cross(x_j, x_{j+1}, p)` : strengthen the own-edge bound
    show 0 < pvSgn σ * pvCross (y ⟨pvIdx e j.val, pvIdx_lt e _⟩)
        (y ⟨pvIdx e (j.val + 1), pvIdx_lt e _⟩) p
    by_cases hjk : j.val + 1 < k
    · rw [pvIdx_eval e y (a := j.val)
          (i := ⟨(e j).val, Nat.lt_succ_of_lt (hej j)⟩)
          (pvIdx_of_lt e j.isLt),
        pvIdx_eval e y (a := j.val + 1)
          (i := ⟨(e ⟨j.val + 1, hjk⟩).val,
            Nat.lt_succ_of_lt (hej ⟨j.val + 1, hjk⟩)⟩)
          (pvIdx_of_lt e hjk)]
      exact pv_supp_inner hmono hshape (hej j)
        (hev ⟨j.val, j.isLt⟩ ⟨j.val + 1, hjk⟩ (Fin.mk_lt_mk.mpr (by omega)))
        (Nat.le_of_lt (hej _)) hp
    · rw [pvIdx_eval e y (a := j.val)
          (i := ⟨(e j).val, Nat.lt_succ_of_lt (hej j)⟩)
          (pvIdx_of_lt e j.isLt),
        pvIdx_eval e y (a := j.val + 1) (i := ⟨2 * k, Nat.lt_succ_self _⟩)
          (pvIdx_of_not_lt e hjk)]
      exact pv_supp_inner hmono hshape (hej j) (hej j) le_rfl hp
  · -- `ε·cross(x_l, x_j, p) < 0` : `l = x_{j-1}` (or `x_k = y_{2k}` for `j = 0`)
    show pvSgn σ * pvCross (y ⟨pvIdx e ((j.val + k) % (k + 1)), pvIdx_lt e _⟩)
        (y ⟨pvIdx e j.val, pvIdx_lt e _⟩) p < 0
    rcases Nat.eq_zero_or_pos j.val with hj0 | hj0
    · have hmod : (j.val + k) % (k + 1) = k := by
        rw [hj0, Nat.zero_add]; exact Nat.mod_eq_of_lt (Nat.lt_succ_self k)
      rw [pvIdx_eval e y (a := (j.val + k) % (k + 1))
          (i := ⟨2 * k, Nat.lt_succ_self _⟩)
          (by rw [hmod]; exact pvIdx_of_not_lt e (by omega : ¬ k < k)),
        pvIdx_eval e y (a := j.val)
          (i := ⟨(e j).val, Nat.lt_succ_of_lt (hej j)⟩)
          (pvIdx_of_lt e j.isLt)]
      exact pv_supp_wrap_left hmono hshape (hej j) hp
    · have hm1 : j.val - 1 < k := by omega
      have hmod : (j.val + k) % (k + 1) = j.val - 1 := by
        have h : j.val + k = (j.val - 1) + (k + 1) := by omega
        rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j.val - 1 < k + 1)]
      rw [pvIdx_eval e y (a := (j.val + k) % (k + 1))
          (i := ⟨(e ⟨j.val - 1, hm1⟩).val,
            Nat.lt_succ_of_lt (hej ⟨j.val - 1, hm1⟩)⟩)
          (by rw [hmod]; exact pvIdx_of_lt e hm1),
        pvIdx_eval e y (a := j.val)
          (i := ⟨(e j).val, Nat.lt_succ_of_lt (hej j)⟩)
          (pvIdx_of_lt e j.isLt)]
      exact pv_supp_left hmono hshape
        (show (e ⟨j.val - 1, hm1⟩).val + 1 ≤ (e j).val by
          have h : (e ⟨j.val - 1, hm1⟩).val < (e j).val :=
            hev ⟨j.val - 1, hm1⟩ j (Fin.lt_iff_val_lt_val.mpr (by
              show j.val - 1 < j.val; omega))
          omega)
        (hej j) hp
  · -- `ε·cross(x_{j+1}, x_r, p) < 0` : `r = x_{j+2}` (or `x_0 = y_{e 0}` at `j = k-1`)
    show pvSgn σ * pvCross (y ⟨pvIdx e (j.val + 1), pvIdx_lt e _⟩)
        (y ⟨pvIdx e ((j.val + 2) % (k + 1)), pvIdx_lt e _⟩) p < 0
    by_cases hjk : j.val + 2 < k
    · have hj1 : j.val + 1 < k := by omega
      have hmod : (j.val + 2) % (k + 1) = j.val + 2 := Nat.mod_eq_of_lt (by omega)
      rw [pvIdx_eval e y (a := j.val + 1)
          (i := ⟨(e ⟨j.val + 1, hj1⟩).val,
            Nat.lt_succ_of_lt (hej ⟨j.val + 1, hj1⟩)⟩)
          (pvIdx_of_lt e hj1),
        pvIdx_eval e y (a := (j.val + 2) % (k + 1))
          (i := ⟨(e ⟨j.val + 2, hjk⟩).val,
            Nat.lt_succ_of_lt (hej ⟨j.val + 2, hjk⟩)⟩)
          (by rw [hmod]; exact pvIdx_of_lt e hjk)]
      exact pv_supp_right hmono hshape (hej j)
        (show (e j).val + 2 ≤ 2 * k by
          have h1 : (e j).val < (e ⟨j.val + 1, hj1⟩).val :=
            hev j ⟨j.val + 1, hj1⟩
              (Fin.lt_iff_val_lt_val.mpr (Nat.lt_succ_self _))
          have h2 : (e ⟨j.val + 1, hj1⟩).val < (e ⟨j.val + 2, hjk⟩).val :=
            hev ⟨j.val + 1, hj1⟩ ⟨j.val + 2, hjk⟩
              (Fin.lt_iff_val_lt_val.mpr (Nat.lt_succ_self _))
          have h3 : (e ⟨j.val + 2, hjk⟩).val < 2 * k := hej ⟨j.val + 2, hjk⟩
          omega)
        (show (e j).val + 1 ≤ (e ⟨j.val + 1, hj1⟩).val by
          have h : (e j).val < (e ⟨j.val + 1, hj1⟩).val :=
            hev j ⟨j.val + 1, hj1⟩
              (Fin.lt_iff_val_lt_val.mpr (Nat.lt_succ_self _))
          omega)
        (show (e ⟨j.val + 1, hj1⟩).val + 1 ≤ (e ⟨j.val + 2, hjk⟩).val by
          have h : (e ⟨j.val + 1, hj1⟩).val < (e ⟨j.val + 2, hjk⟩).val :=
            hev ⟨j.val + 1, hj1⟩ ⟨j.val + 2, hjk⟩
              (Fin.lt_iff_val_lt_val.mpr (Nat.lt_succ_self _))
          omega)
        (Nat.le_of_lt (hej ⟨j.val + 2, hjk⟩)) hp
    · rcases (by omega : j.val + 2 = k ∨ j.val + 2 = k + 1) with h | h
      · have hj1 : j.val + 1 < k := by omega
        have hmod : (j.val + 2) % (k + 1) = k := by
          rw [h]; exact Nat.mod_eq_of_lt (Nat.lt_succ_self k)
        rw [pvIdx_eval e y (a := (j.val + 2) % (k + 1))
            (i := ⟨2 * k, Nat.lt_succ_self _⟩)
            (by rw [hmod]; exact pvIdx_of_not_lt e (by omega : ¬ k < k)),
          pvIdx_eval e y (a := j.val + 1)
            (i := ⟨(e ⟨j.val + 1, hj1⟩).val,
              Nat.lt_succ_of_lt (hej ⟨j.val + 1, hj1⟩)⟩)
            (pvIdx_of_lt e hj1)]
        exact pv_supp_right hmono hshape (hej j)
          (show (e j).val + 2 ≤ 2 * k by
            have h1 : (e j).val < (e ⟨j.val + 1, hj1⟩).val :=
              hev j ⟨j.val + 1, hj1⟩
                (Fin.lt_iff_val_lt_val.mpr (Nat.lt_succ_self _))
            have h3 : (e ⟨j.val + 1, hj1⟩).val < 2 * k := hej ⟨j.val + 1, hj1⟩
            omega)
          (show (e j).val + 1 ≤ (e ⟨j.val + 1, hj1⟩).val by
            have h : (e j).val < (e ⟨j.val + 1, hj1⟩).val :=
              hev j ⟨j.val + 1, hj1⟩
                (Fin.lt_iff_val_lt_val.mpr (Nat.lt_succ_self _))
            omega)
          (show (e ⟨j.val + 1, hj1⟩).val + 1 ≤ 2 * k by
            have h : (e ⟨j.val + 1, hj1⟩).val < 2 * k := hej ⟨j.val + 1, hj1⟩
            omega)
          le_rfl hp
      · have hk0 : 0 < k := by omega
        have hmod : (j.val + 2) % (k + 1) = 0 := by
          rw [h]; exact Nat.mod_self _
        rw [pvIdx_eval e y (a := (j.val + 2) % (k + 1))
            (i := ⟨(e ⟨0, hk0⟩).val,
              Nat.lt_succ_of_lt (hej ⟨0, hk0⟩)⟩)
            (by rw [hmod]; exact pvIdx_of_lt e hk0),
          pvIdx_eval e y (a := j.val + 1) (i := ⟨2 * k, Nat.lt_succ_self _⟩)
            (pvIdx_of_not_lt e (by omega : ¬ j.val + 1 < k))]
        rcases Nat.eq_zero_or_pos j.val with hj0 | hj0
        · -- `j = 0` forces `k = 1`: the third support condition is the same
          -- wraparound chord `y_{2k} y_{e 0}` as the second, so
          -- `pv_supp_wrap_left` applies.
          have hje : (⟨0, hk0⟩ : Fin k) = j := Fin.ext hj0.symm
          rw [hje]
          exact pv_supp_wrap_left hmono hshape (hej j) hp
        · exact pv_supp_wrap_right hmono hshape (hej j)
            (hev ⟨0, hk0⟩ j (Fin.lt_iff_val_lt_val.mpr hj0)) hp

end
