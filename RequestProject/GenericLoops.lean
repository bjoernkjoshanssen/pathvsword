import RequestProject.GenericVisitProgression

/-! # Consequences of a maximal block of visits to one loop state -/

namespace AneVsAn.Generic

set_option autoImplicit false

variable {n : ℕ} {Λ S : Type} {c : ℕ → S} {x : ℕ → Λ}

/-- The visits of `c a` are exactly the consecutive times from `a` to `a+r`. -/
def LoopBlock (n : ℕ) (c : ℕ → S) (a r : ℕ) : Prop :=
  0 < r ∧ a + r ≤ n ∧ ∀ t, t ≤ n → (c t = c a ↔ a ≤ t ∧ t ≤ a + r)

theorem LoopBlock.loop {a r : ℕ} (h : LoopBlock n c a r) : c a = c (a + 1) := by
  have hr := h.1
  have hn := h.2.1
  exact ((h.2.2 (a + 1) (by omega)).2 ⟨by omega, by omega⟩).symm

theorem LoopBlock.edge_eq (huaw : IsUAWalk x n c) {a r t : ℕ}
    (h : LoopBlock n c a r) (ha : a ≤ t) (ht : t < a + r) :
    edge x c t = edge x c a := by
  have hr := h.1
  have hn := h.2.1
  have hc0 : c t = c a := (h.2.2 t (by omega)).2 ⟨ha, by omega⟩
  have hc1 : c (t + 1) = c (a + 1) :=
    ((h.2.2 (t + 1) (by omega)).2 ⟨by omega, by omega⟩).trans h.loop
  exact Prod.ext hc0 (Prod.ext (single_label huaw (by omega) (by omega) hc0 hc1) hc1)

/-- A closed path avoiding the loop edge is longer than the block of loop edges. -/
theorem loop_min_closed (huaw : IsUAWalk x n c) {a r : ℕ}
    (hloop : LoopBlock n c a r) {s : S} {len : ℕ} {τ : ℕ → ℕ}
    (hlen : 0 < len) (hC : Seg n c s s len τ)
    (havoid : ∀ t, t < len → edge x c (τ t) ≠ edge x c a) : r < len := by
  classical
  have hr := hloop.1
  have hblockn := hloop.2.1
  by_contra hn
  have hle : len ≤ r := by omega
  have hchord : c a = c (a + len) :=
    ((hloop.2.2 (a + len) (by omega)).2 ⟨by omega, by omega⟩).symm
  have hzero : edgeCount x c len τ (edge x c a) = 0 := edgeCount_eq_zero_iff.mpr havoid
  have hfull : edgeCount x c (a + len - a) (fun t => a + t) (edge x c a) = len := by
    rw [show a + len - a = len by omega]
    apply edgeCount_eq_len_iff.mpr
    intro t ht
    exact hloop.edge_eq huaw (by omega) (by omega)
  by_cases hs : s = c a
  · have hC' : Seg n c (c a) (c a) (a + len - a) τ := by
      simpa only [hs, Nat.add_sub_cancel_left] using hC
    have heq := exchange_one huaw (show a ≤ a + len by omega) (show a + len ≤ n by omega)
      (show a ≤ n by omega) hchord (Or.inl le_rfl) hC' (edge x c a)
    simp only [Nat.add_sub_cancel_left] at heq hfull
    omega
  · have hτn : τ 0 ≤ n := Nat.le_of_lt (hC.1 0 hlen)
    have hτs : c (τ 0) = s := hC.2.2.1 hlen
    have hpos : τ 0 ≤ a ∨ a + len ≤ τ 0 := by
      have hnot : ¬ (a ≤ τ 0 ∧ τ 0 ≤ a + r) := by
        intro hh
        exact hs (hτs.symm.trans ((hloop.2.2 (τ 0) hτn).2 hh))
      omega
    have hC' : Seg n c (c (τ 0)) (c (τ 0)) (a + len - a) τ := by
      simpa only [hτs, Nat.add_sub_cancel_left] using hC
    have heq := exchange_one huaw (show a ≤ a + len by omega) (show a + len ≤ n by omega)
      hτn hchord hpos hC' (edge x c a)
    simp only [Nat.add_sub_cancel_left] at heq hfull
    omega

/-- Every chord is contained in the loop block or strictly encloses it. -/
theorem loop_chord (huaw : IsUAWalk x n c) {a r s t : ℕ}
    (hloop : LoopBlock n c a r) (hst : s < t) (htn : t ≤ n) (hchord : c s = c t) :
    (a ≤ s ∧ t ≤ a + r) ∨ (s < a ∧ a + r < t) := by
  classical
  have hr := hloop.1
  have hblockn := hloop.2.1
  by_cases hs : c s = c a
  · have hsp := (hloop.2.2 s (by omega)).1 hs
    have htp := (hloop.2.2 t htn).1 (hchord.symm.trans hs)
    exact Or.inl ⟨hsp.1, htp.2⟩
  · by_contra hn
    have hnotcross : ¬ (s < a ∧ a + r < t) := fun h => hn (Or.inr h)
    have hanchor : ∃ u, u ≤ n ∧ c u = c a ∧ (u ≤ s ∨ t ≤ u) := by
      by_cases has : a ≤ s
      · exact ⟨a, by omega, rfl, Or.inl has⟩
      · exact ⟨a + r, hloop.2.1,
          (hloop.2.2 (a + r) hloop.2.1).2 ⟨by omega, le_rfl⟩, Or.inr (by omega)⟩
    obtain ⟨u, hun, huca, hup⟩ := hanchor
    have hC : Seg n c (c u) (c u) (t - s) (fun _ => a) := by
      rw [huca]
      exact seg_loop (by omega) hloop.loop (t - s)
    have heq := exchange_one huaw (Nat.le_of_lt hst) htn hun hchord hup hC (edge x c a)
    rw [edgeCount_const] at heq
    have hedge := (edgeCount_eq_len_iff.mp heq) 0 (by omega)
    have hcs : c s = c a := by
      simpa only [edge, Nat.add_zero] using congrArg (fun e : S × Λ × S => e.1) hedge
    exact hs hcs

theorem LoopBlock.edge_eq_iff (huaw : IsUAWalk x n c) {a r t : ℕ}
    (h : LoopBlock n c a r) (ht : t < n) :
    edge x c t = edge x c a ↔ a ≤ t ∧ t < a + r := by
  have hr := h.1
  have hn := h.2.1
  constructor
  · intro he
    have hct : c t = c a := congrArg Prod.fst he
    have hct' : c (t + 1) = c (a + 1) := congrArg (fun e : S × Λ × S => e.2.2) he
    have h1 := (h.2.2 t (by omega)).1 hct
    have h2 := (h.2.2 (t + 1) (by omega)).1 (hct'.trans h.loop.symm)
    omega
  · rintro ⟨ha, ht'⟩
    exact h.edge_eq huaw ha ht'

/-- An enclosing chord has span at least twice the number of loop edges plus one.
Deleting the loop block gives a loop-free closed path, so `loop_min_closed` applies. -/
theorem loop_chord_span (huaw : IsUAWalk x n c) {a r s t : ℕ}
    (hloop : LoopBlock n c a r) (hsa : s < a) (hart : a + r < t)
    (htn : t ≤ n) (hchord : c s = c t) : 2 * r + 1 ≤ t - s := by
  have hr := hloop.1
  have hblockn := hloop.2.1
  have hleft := segW c (show s ≤ a by omega) (show a ≤ n by omega)
  have hright := segW c (show a + r ≤ t by omega) htn
  have har : c (a + r) = c a := (hloop.2.2 (a + r) hblockn).2 ⟨by omega, le_rfl⟩
  rw [har, ← hchord] at hright
  have hC := seg_cat hleft hright
  have havoid : ∀ j, j < (a - s) + (t - (a + r)) →
      edge x c (cat (a - s) (fun i => s + i) (fun i => a + r + i) j) ≠ edge x c a := by
    intro j hj he
    by_cases hja : j < a - s
    · rw [cat_lt hja] at he
      have hh := (hloop.edge_eq_iff huaw (show s + j < n by omega)).1 he
      omega
    · rw [cat_ge hja] at he
      have hh := (hloop.edge_eq_iff huaw (show a + r + (j - (a - s)) < n by omega)).1 he
      omega
  have hmin := loop_min_closed huaw hloop (by omega) hC havoid
  omega

/-- The prefix up to the first loop visit has no repeated states. -/
theorem loop_prefix_injective (huaw : IsUAWalk x n c) {a r : ℕ}
    (hloop : LoopBlock n c a r) {s t : ℕ} (hs : s ≤ a) (ht : t ≤ a)
    (heq : c s = c t) : s = t := by
  have hr := hloop.1
  have hblockn := hloop.2.1
  rcases lt_trichotomy s t with hst | hst | hst
  · rcases loop_chord huaw hloop hst (by omega) heq with h | h <;> omega
  · exact hst
  · rcases loop_chord huaw hloop hst (by omega) heq.symm with h | h <;> omega

/-- The suffix from the last loop visit has no repeated states. -/
theorem loop_suffix_injective (huaw : IsUAWalk x n c) {a r : ℕ}
    (hloop : LoopBlock n c a r) {s t : ℕ} (hs : a + r ≤ s) (ht : a + r ≤ t)
    (hsn : s ≤ n) (htn : t ≤ n) (heq : c s = c t) : s = t := by
  have hr := hloop.1
  have hblockn := hloop.2.1
  rcases lt_trichotomy s t with hst | hst | hst
  · rcases loop_chord huaw hloop hst htn heq with h | h <;> omega
  · exact hst
  · rcases loop_chord huaw hloop hst hsn heq.symm with h | h <;> omega

/-- State count for a loop block. This is the loop lemma's counting conclusion. -/
theorem loop_card [DecidableEq S] (huaw : IsUAWalk x n c) {a r : ℕ}
    (hloop : LoopBlock n c a r) :
    n + 1 - r - min a (n - a - r) ≤ (walkStates n c).card := by
  have hr := hloop.1
  have hblockn := hloop.2.1
  have hleft : a + 1 ≤ (walkStates n c).card := by
    have hinj : Set.InjOn c (Finset.range (a + 1)) := by
      intro i hi j hj hij
      apply loop_prefix_injective huaw hloop (by have := Finset.mem_range.mp hi; omega) (by have := Finset.mem_range.mp hj; omega) hij
    have hcard : ((Finset.range (a + 1)).image c).card = a + 1 := by
      rw [Finset.card_image_of_injOn hinj]
      simp
    rw [← hcard]
    apply Finset.card_le_card
    exact Finset.image_subset_image (Finset.range_mono (by omega))
  have hright : n - (a + r) + 1 ≤ (walkStates n c).card := by
    let f : ℕ → S := fun i => c (a + r + i)
    have hinj : Set.InjOn f (Finset.range (n - (a + r) + 1)) := by
      intro i hi j hj hij
      have hi' : i < n - (a + r) + 1 := Finset.mem_range.mp hi
      have hj' : j < n - (a + r) + 1 := Finset.mem_range.mp hj
      have hh := loop_suffix_injective huaw hloop (show a + r ≤ a + r + i by omega)
        (show a + r ≤ a + r + j by omega) (by omega) (by omega) hij
      omega
    have hcard : ((Finset.range (n - (a + r) + 1)).image f).card = n - (a + r) + 1 := by
      rw [Finset.card_image_of_injOn hinj]
      simp
    rw [← hcard]
    apply Finset.card_le_card
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_image.mpr ⟨a + r + i, Finset.mem_range.mpr (by omega), rfl⟩
  omega

/-- Any adjacent repeated state extends to a single maximal interval of visits. -/
theorem loopBlock_of_adjacent [DecidableEq S] (huaw : IsUAWalk x n c)
    {t : ℕ} (ht : t < n) (hct : c t = c (t + 1)) :
    ∃ a r, LoopBlock n c a r ∧ c a = c t ∧ a ≤ t ∧ t + 1 ≤ a + r := by
  have hv : 2 ≤ (visitTimes n c (c t)).card := by
    apply Finset.one_lt_card.mpr
    exact ⟨t, mem_visitTimes.mpr ⟨by omega, rfl⟩,
      t + 1, mem_visitTimes.mpr ⟨by omega, hct.symm⟩, by omega⟩
  obtain ⟨a, p, hp, hlast, hvis, _, _⟩ := visits_progression huaw (c t) hv
  obtain ⟨i, hi, hti⟩ := (hvis t (by omega)).1 rfl
  obtain ⟨j, hj, htj⟩ := (hvis (t + 1) (by omega)).1 hct.symm
  have hij : i < j := by
    by_contra h
    have hmul := Nat.mul_le_mul_right p (show j ≤ i by omega)
    omega
  have hp1 : p = 1 := by
    have hmul := Nat.mul_le_mul_right p (show i + 1 ≤ j by omega)
    rw [Nat.add_mul] at hmul
    nlinarith
  subst p
  simp only [Nat.mul_one] at hlast hti htj hvis
  have hca : c a = c t := by
    apply (hvis a (by omega)).2
    exact ⟨0, by omega, by omega⟩
  refine ⟨a, (visitTimes n c (c t)).card - 1, ?_, hca, by omega, by omega⟩
  refine ⟨by omega, hlast, ?_⟩
  intro u hu
  rw [hca, hvis u hu]
  constructor
  · rintro ⟨k, hk, rfl⟩
    omega
  · rintro ⟨hau, hul⟩
    exact ⟨u - a, by omega, by omega⟩

/-- A full accepting path cannot contain more consecutive copies of the loop edge
than the original maximal loop block. This is a convenient surgery contradiction. -/
theorem loop_insert_bound (huaw : IsUAWalk x n c) {a r : ℕ}
    (hloop : LoopBlock n c a r) {pre post m : ℕ} {τ₁ τ₂ : ℕ → ℕ}
    (hpre : Seg n c (c 0) (c a) pre τ₁)
    (hpost : Seg n c (c a) (c n) post τ₂)
    (hlen : pre + m + post = n) : m ≤ r := by
  have hr := hloop.1
  have hblockn := hloop.2.1
  by_cases hm : m = 0
  · omega
  have hmid := seg_loop (show a < n by omega) hloop.loop m
  have hall := seg_cat (seg_cat hpre hmid) hpost
  rw [hlen] at hall
  have hfirst := pathTo_edge huaw hall pre (by omega)
  rw [cat_lt (by omega), cat_ge (by omega)] at hfirst
  have hlast := pathTo_edge huaw hall (pre + m - 1) (by omega)
  rw [cat_lt (by omega), cat_ge (by omega)] at hlast
  have hfirst' := (hloop.edge_eq_iff huaw (show pre < n by omega)).1 hfirst.symm
  have hlast' := (hloop.edge_eq_iff huaw (show pre + m - 1 < n by omega)).1 hlast.symm
  omega

end AneVsAn.Generic
