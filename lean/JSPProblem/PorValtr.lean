import JSPProblem.PorValtrSeqs

noncomputable section

/-- **Pór–Valtr existence core** — the full mathematical content of

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
    -- ## Step 1: subset counting via `cupsCaps`
    have hs_ub : (8 * k - 2).choose (4 * k - 1) + 1 ≤ 2 ^ (8 * k) := by
      have h1 : (8 * k - 2).choose (4 * k - 1) ≤ 2 ^ (8 * k - 2) :=
        Nat.choose_le_two_pow _ _
      have h2 : (2 : ℕ) ^ (8 * k - 2) + 2 ^ (8 * k - 2) = 2 ^ (8 * k - 1) := by
        rw [← two_mul, ← pow_succ]; congr 1; omega
      have h3 : (1 : ℕ) ≤ 2 ^ (8 * k - 2) := Nat.one_le_pow _ _ (by norm_num)
      calc (8 * k - 2).choose (4 * k - 1) + 1
          ≤ 2 ^ (8 * k - 2) + 2 ^ (8 * k - 2) := by omega
        _ = 2 ^ (8 * k - 1) := h2
        _ ≤ 2 ^ (8 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hs_le : (8 * k - 2).choose (4 * k - 1) + 1 ≤ X.card :=
      hs_ub.trans ((pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
        (by omega : 8 * k ≤ 40 * k)).trans hcard)
    have ht_le_s : 4 * k + 1 ≤ (8 * k - 2).choose (4 * k - 1) + 1 := by
      have hm : (8 * k - 2) / 2 = 4 * k - 1 := by omega
      have h1 := Nat.choose_le_middle 1 (8 * k - 2)
      rw [Nat.choose_one_right, hm] at h1
      omega
    have hshs : (4 * k + 1 + (4 * k + 1) - 4).choose (4 * k + 1 - 2) + 1 ≤
        (8 * k - 2).choose (4 * k - 1) + 1 := by
      have e : (4 * k + 1 + (4 * k + 1) - 4).choose (4 * k + 1 - 2) =
          (8 * k - 2).choose (4 * k - 1) := by
        rw [show 4 * k + 1 + (4 * k + 1) - 4 = 8 * k - 2 by omega,
          show 4 * k + 1 - 2 = 4 * k - 1 by omega]
      omega
    have hcount : X.card.choose ((8 * k - 2).choose (4 * k - 1) + 1) ≤
        ((pvSets X true (4 * k)).card + (pvSets X false (4 * k)).card) *
          (X.card - (4 * k + 1)).choose ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1)) :=
      pv_choose_count hX hdx (by omega) ht_le_s hshs hs_le
    -- ## Step 2: the fiber-bound sum dominates the count of good sets
    have hbool : ∀ f : Bool → ℕ, (∑ σ : Bool, f σ) = f true + f false := fun f ↦ by
      rw [Fintype.univ_bool, Finset.sum_pair (by decide : true ≠ false)]
    have hsum_ge : (pvSets X true (4 * k)).card + (pvSets X false (4 * k)).card ≤
        ∑ σ : Bool, ∑ y ∈ pvSeqs X σ (2 * k), ∏ i : Fin (2 * k), #(pvSupp X y σ i) := by
      rw [← card_pvSeqs, ← card_pvSeqs, hbool]
      exact add_le_add (pv_fiber_bound hdx true) (pv_fiber_bound hdx false)
    have hpairs : (∑ σ : Bool, #(pvSeqs X σ (2 * k))) ≤ 2 * X.card.choose (2 * k + 1) := by
      rw [hbool, two_mul]
      exact add_le_add pvSeqs_le pvSeqs_le
    have hcomb : X.card.choose ((8 * k - 2).choose (4 * k - 1) + 1) ≤
        (∑ σ : Bool, ∑ y ∈ pvSeqs X σ (2 * k), ∏ i : Fin (2 * k), #(pvSupp X y σ i)) *
          ((X.card - (4 * k + 1)).choose ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1))) :=
      hcount.trans (Nat.mul_le_mul_right _ hsum_ge)
    -- ## Step 3: pigeonhole — some `(2k+1)`-cap/cup has a large support product
    obtain ⟨σ, y, hy, hbig⟩ : ∃ σ : Bool, ∃ y ∈ pvSeqs X σ (2 * k),
        X.card.choose ((8 * k - 2).choose (4 * k - 1) + 1) ≤
          2 * X.card.choose (2 * k + 1) *
            ((X.card - (4 * k + 1)).choose ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1))) *
            (∏ i : Fin (2 * k), #(pvSupp X y σ i)) := by
      by_contra hcon
      push_neg at hcon
      have hlt : (∑ σ : Bool, ∑ y ∈ pvSeqs X σ (2 * k),
          2 * X.card.choose (2 * k + 1) *
            ((X.card - (4 * k + 1)).choose ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1))) *
            (∏ i : Fin (2 * k), #(pvSupp X y σ i))) <
          (∑ σ : Bool, #(pvSeqs X σ (2 * k))) *
            X.card.choose ((8 * k - 2).choose (4 * k - 1) + 1) := by
        apply Finset.sum_lt_sum
        · intro σ _
          by_cases hne : (pvSeqs X σ (2 * k)).Nonempty
          · rw [Finset.sum_mul]
            calc ∑ y ∈ pvSeqs X σ (2 * k),
                2 * X.card.choose (2 * k + 1) *
                  ((X.card - (4 * k + 1)).choose
                    ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1))) *
                  (∏ i : Fin (2 * k), #(pvSupp X y σ i))
                ≤ ∑ _y ∈ pvSeqs X σ (2 * k),
                    X.card.choose ((8 * k - 2).choose (4 * k - 1) + 1) :=
                  Finset.sum_le_sum fun y hy ↦ le_of_lt (hcon σ y hy)
              _ = #(pvSeqs X σ (2 * k)) *
                    X.card.choose ((8 * k - 2).choose (4 * k - 1) + 1) := by
                  rw [Finset.sum_const, smul_eq_mul]
          · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
        · obtain ⟨σ, hσ⟩ : ∃ σ : Bool, (pvSeqs X σ (2 * k)).Nonempty := by
            by_contra h2
            push_neg at h2
            have hempty : ∀ σ : Bool, pvSeqs X σ (2 * k) = ∅ := fun σ ↦
              Finset.not_nonempty_iff_eq_empty.mp (h2 σ)
            have hz : (∑ σ : Bool, ∑ y ∈ pvSeqs X σ (2 * k),
                ∏ i : Fin (2 * k), #(pvSupp X y σ i)) = 0 := by
              apply Finset.sum_eq_zero; intro σ _
              rw [hempty σ]; simp
            have hpos : 0 < (pvSets X true (4 * k)).card + (pvSets X false (4 * k)).card := by
              have hTF : X.card.choose (4 * k + 1) ≤
                  ((pvSets X true (4 * k)).card + (pvSets X false (4 * k)).card) *
                    ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) := by
                have e := Nat.choose_mul (n := X.card) (k := (8 * k - 2).choose (4 * k - 1) + 1)
                  (s := 4 * k + 1) ht_le_s
                have h1 := Nat.mul_le_mul_right
                  ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) hcount
                rw [e] at h1
                rw [show (pvSets X true (4 * k)).card + (pvSets X false (4 * k)).card *
                    ((X.card - (4 * k + 1)).choose
                      ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1))) *
                    ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) =
                  ((pvSets X true (4 * k)).card + (pvSets X false (4 * k)).card) *
                    ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) *
                    ((X.card - (4 * k + 1)).choose
                      ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1))) by ring] at h1
                exact Nat.le_of_mul_le_mul_right h1 (Nat.choose_pos.mpr (by omega))
              have h1 : 0 < X.card.choose (4 * k + 1) := Nat.choose_pos (by omega)
              have h2 : 0 < ((pvSets X true (4 * k)).card + (pvSets X false (4 * k)).card) *
                  ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) := h1.trans_le hTF
              rcases Nat.eq_zero_or_pos
                ((pvSets X true (4 * k)).card + (pvSets X false (4 * k)).card) with h0 | h0
              · rw [h0, zero_mul] at h2; exact absurd h2 (lt_irrefl 0)
              · exact h0
            exact absurd (hz ▸ hsum_ge) (Nat.not_le.mpr hpos)
          obtain ⟨y, hy⟩ := hσ
          exact ⟨σ, Finset.mem_univ σ, by
            rw [Finset.sum_mul]
            apply Finset.sum_lt_sum_of_nonempty ⟨y, hy⟩
            intro z hz; exact hcon σ z hz⟩
      have hB : (∑ σ : Bool, ∑ y ∈ pvSeqs X σ (2 * k),
          2 * X.card.choose (2 * k + 1) *
            ((X.card - (4 * k + 1)).choose ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1))) *
            (∏ i : Fin (2 * k), #(pvSupp X y σ i))) =
          (2 * X.card.choose (2 * k + 1) *
            ((X.card - (4 * k + 1)).choose ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1)))) *
            ∑ σ : Bool, ∑ y ∈ pvSeqs X σ (2 * k), ∏ i : Fin (2 * k), #(pvSupp X y σ i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro σ _
        rw [Finset.mul_sum]
      have hlow : 2 * X.card.choose (2 * k + 1) *
          X.card.choose ((8 * k - 2).choose (4 * k - 1) + 1) ≤
          (2 * X.card.choose (2 * k + 1) *
            ((X.card - (4 * k + 1)).choose ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1)))) *
            ∑ σ : Bool, ∑ y ∈ pvSeqs X σ (2 * k), ∏ i : Fin (2 * k), #(pvSupp X y σ i) := by
        calc 2 * X.card.choose (2 * k + 1) *
              X.card.choose ((8 * k - 2).choose (4 * k - 1) + 1)
            ≤ 2 * X.card.choose (2 * k + 1) *
              (((pvSets X true (4 * k)).card + (pvSets X false (4 * k)).card) *
                ((X.card - (4 * k + 1)).choose
                  ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1)))) :=
              Nat.mul_le_mul_left _ hcount
          _ = (2 * X.card.choose (2 * k + 1) *
                ((X.card - (4 * k + 1)).choose
                  ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1)))) *
              ((pvSets X true (4 * k)).card + (pvSets X false (4 * k)).card) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ hsum_ge
      have hfin : (∑ σ : Bool, #(pvSeqs X σ (2 * k))) *
            X.card.choose ((8 * k - 2).choose (4 * k - 1) + 1) ≤
          2 * X.card.choose (2 * k + 1) * X.card.choose ((8 * k - 2).choose (4 * k - 1) + 1) :=
        Nat.mul_le_mul_right _ hpairs
      rw [hB] at hlt
      exact absurd (hlow.trans_lt (hlt.trans_le hfin)) (lt_irrefl _)
    -- ## Step 4: extract `k` dense support edges of `y`
    have hcomb2 : X.card.choose (4 * k + 1) ≤
        2 * X.card.choose (2 * k + 1) *
          ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) *
          (∏ i : Fin (2 * k), #(pvSupp X y σ i)) := by
      have e := Nat.choose_mul (n := X.card) (k := (8 * k - 2).choose (4 * k - 1) + 1)
        (s := 4 * k + 1) ht_le_s
      have h1 := Nat.mul_le_mul_right
        ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) hbig
      rw [e] at h1
      rw [show 2 * X.card.choose (2 * k + 1) *
          ((X.card - (4 * k + 1)).choose ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1))) *
          (∏ i : Fin (2 * k), #(pvSupp X y σ i)) *
          ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) =
        (2 * X.card.choose (2 * k + 1) *
          ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) *
          (∏ i : Fin (2 * k), #(pvSupp X y σ i))) *
          ((X.card - (4 * k + 1)).choose ((8 * k - 2).choose (4 * k - 1) + 1 - (4 * k + 1))) by ring] at h1
      exact Nat.le_of_mul_le_mul_right h1 (Nat.choose_pos.mpr (by omega))
    have hdense_k : k ≤ (Finset.univ.filter fun i : Fin (2 * k) ↦
        X.card ≤ 2 ^ (40 * k) * #(pvSupp X y σ i)).card := by
      by_contra hlt
      push_neg at hlt
      have hnd : k + 1 ≤ (Finset.univ.filter fun i : Fin (2 * k) ↦
          ¬ X.card ≤ 2 ^ (40 * k) * #(pvSupp X y σ i)).card := by
        have e := Finset.card_filter_add_card_filter_not (Finset.univ : Finset (Fin (2 * k)))
          (fun i ↦ X.card ≤ 2 ^ (40 * k) * #(pvSupp X y σ i))
        rw [Finset.card_univ, Fintype.card_fin] at e
        omega
      obtain ⟨S₀, hS₀, hS₀c⟩ := Finset.exists_subset_card_eq hnd
      have hprod : 2 ^ (40 * k * (k + 1)) * (∏ i : Fin (2 * k), #(pvSupp X y σ i)) ≤
          X.card ^ (k - 1) * (X.card - 1) ^ (k + 1) := by
        have hsplit : (∏ i : Fin (2 * k), #(pvSupp X y σ i)) =
            (∏ i ∈ S₀, #(pvSupp X y σ i)) * (∏ i ∈ S₀ᶜ, #(pvSupp X y σ i)) :=
          (Finset.prod_mul_prod_compl S₀ _).symm
        have hA : 2 ^ (40 * k * (k + 1)) * ∏ i ∈ S₀, #(pvSupp X y σ i) ≤
            (X.card - 1) ^ (k + 1) := by
          have e1 : (∏ i ∈ S₀, (2 ^ (40 * k) * #(pvSupp X y σ i))) =
              (2 ^ (40 * k)) ^ (k + 1) * ∏ i ∈ S₀, #(pvSupp X y σ i) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, hS₀c]
          have h2 : ∏ i ∈ S₀, (2 ^ (40 * k) * #(pvSupp X y σ i)) ≤ (X.card - 1) ^ (k + 1) := by
            calc ∏ i ∈ S₀, (2 ^ (40 * k) * #(pvSupp X y σ i))
                ≤ ∏ _i ∈ S₀, (X.card - 1) := by
                  apply Finset.prod_le_prod
                  intro i hi
                  have h := (Finset.mem_filter.mp (hS₀ hi)).2
                  omega
              _ = (X.card - 1) ^ (k + 1) := by rw [Finset.prod_const, hS₀c]
          rw [e1] at h2
          rwa [show (2 ^ (40 * k)) ^ (k + 1) = 2 ^ (40 * k * (k + 1)) by rw [← pow_mul]] at h2
        have hB : ∏ i ∈ S₀ᶜ, #(pvSupp X y σ i) ≤ X.card ^ (k - 1) := by
          calc ∏ i ∈ S₀ᶜ, #(pvSupp X y σ i)
              ≤ ∏ _i ∈ S₀ᶜ, X.card := Finset.prod_le_prod fun i _ ↦ pvSupp_le_card y σ i
            _ = X.card ^ ((S₀ᶜ).card) := Finset.prod_const
            _ = X.card ^ (k - 1) := by
              congr 1
              rw [Finset.card_compl, Fintype.card_fin, hS₀c]; omega
        rw [hsplit]
        calc 2 ^ (40 * k * (k + 1)) *
              (∏ i ∈ S₀, #(pvSupp X y σ i) * ∏ i ∈ S₀ᶜ, #(pvSupp X y σ i))
            = (2 ^ (40 * k * (k + 1)) * ∏ i ∈ S₀, #(pvSupp X y σ i)) *
                ∏ i ∈ S₀ᶜ, #(pvSupp X y σ i) := by ring
          _ ≤ (X.card - 1) ^ (k + 1) * X.card ^ (k - 1) := Nat.mul_le_mul hA hB
          _ = X.card ^ (k - 1) * (X.card - 1) ^ (k + 1) := by ring
      have hcontra : 2 ^ (40 * k * (k + 1)) * X.card.choose (4 * k + 1) ≤
          2 * X.card.choose (2 * k + 1) *
            ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) *
            X.card ^ (k - 1) * (X.card - 1) ^ (k + 1) := by
        calc 2 ^ (40 * k * (k + 1)) * X.card.choose (4 * k + 1)
            ≤ 2 ^ (40 * k * (k + 1)) * (2 * X.card.choose (2 * k + 1) *
                ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) *
                (∏ i : Fin (2 * k), #(pvSupp X y σ i))) :=
              Nat.mul_le_mul_left _ hcomb2
          _ = 2 * X.card.choose (2 * k + 1) *
                ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) *
                (2 ^ (40 * k * (k + 1)) * (∏ i : Fin (2 * k), #(pvSupp X y σ i))) := by ring
          _ ≤ 2 * X.card.choose (2 * k + 1) *
                ((8 * k - 2).choose (4 * k - 1) + 1).choose (4 * k + 1) *
                (X.card ^ (k - 1) * (X.card - 1) ^ (k + 1)) :=
              Nat.mul_le_mul_left _ hprod
          _ = _ := by ring
      have har := pv_arith (show 1 ≤ k by omega) hcard hs_ub
      exact absurd hcontra (Nat.not_le.mpr har)
    -- ## Step 5: the dense-edge sub-chain
    obtain ⟨D', hD'D, hD'c⟩ := Finset.exists_subset_card_eq hdense_k
    let e : Fin k ↪o Fin (2 * k) := D'.orderEmbOfFin hD'c
    have hym := mem_pvSeqs.mp hy
    have hxm : StrictMono fun i ↦ (y i) 0 := pvSeqs_xmono hy hdx
    have hysh : pvShaped y σ := pvSeqs_shaped hy hdx
    refine ⟨fun i : Fin (k + 1) ↦ y ⟨pvIdx e i.val, pvIdx_lt e _⟩,
        σ, fun i ↦ hym.2.1 _, ?_, ?_, ?_⟩
    · intro a b hab
      exact hxm (Fin.mk_lt_mk.mpr (pvIdx_strictMono e hab (Nat.le_of_lt_succ b.isLt)))
    · have hsub : Finset.image (fun i : Fin (k + 1) ↦ y ⟨pvIdx e i.val, pvIdx_lt e _⟩)
          Finset.univ ⊆ Finset.image y Finset.univ := by
        rw [Finset.image_subset_iff]
        intro i _
        exact Finset.mem_image.mpr ⟨⟨pvIdx e i.val, pvIdx_lt e _⟩,
          Finset.mem_univ _, rfl⟩
      cases σ
      · exact pv_isCup_mono hsub hym.2.2
      · exact pv_isCap_mono hsub hym.2.2
    · intro j
      have hdj : X.card ≤ 2 ^ (40 * k) * #(pvSupp X y σ (e j)) := by
        have hm := hD'D (Finset.orderEmbOfFin_mem D' hD'c j)
        exact (Finset.mem_filter.mp hm).2
      have hsub : supportOf y σ (e j) ⊆
          supportOf (fun i : Fin (k + 1) ↦ y ⟨pvIdx e i.val, pvIdx_lt e _⟩) σ j :=
        fun p hp ↦ pv_supp_subseq hxm hysh e j hp
      have hsub2 : supportOf y σ (e j) ∩ (X : Set (Euc 2)) ⊆
          supportOf (fun i : Fin (k + 1) ↦ y ⟨pvIdx e i.val, pvIdx_lt e _⟩) σ j ∩
            (X : Set (Euc 2)) := fun q hq ↦ ⟨hsub hq.1, hq.2⟩
      have hle : (supportOf y σ (e j) ∩ (X : Set (Euc 2))).ncard ≤
          (supportOf (fun i : Fin (k + 1) ↦ y ⟨pvIdx e i.val, pvIdx_lt e _⟩) σ j ∩
            (X : Set (Euc 2))).ncard :=
        Set.ncard_le_ncard hsub2 (X.finite_toSet.subset Set.inter_subset_right)
      calc X.card ≤ 2 ^ (40 * k) * (supportOf y σ (e j) ∩ (X : Set (Euc 2))).ncard := by
            rw [pv_ncard_supp]; exact hdj
        _ ≤ 2 ^ (40 * k) *
            (supportOf (fun i : Fin (k + 1) ↦ y ⟨pvIdx e i.val, pvIdx_lt e _⟩) σ j ∩
              (X : Set (Euc 2))).ncard := Nat.mul_le_mul_left _ hle
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
