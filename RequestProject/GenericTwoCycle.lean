import RequestProject.GenericLoops

/-! # A confined two-cycle bounds visits to every other state -/

namespace AneVsAn.Generic

set_option autoImplicit false

variable {n : ℕ} {Λ S : Type} {c : ℕ → S} {x : ℕ → Λ}

/-- Suppose an interval uses exactly two states, those states occur nowhere else,
and its first two edges form a two-cycle. Every other state is visited at most twice.
The alternation hypothesis normally used in applications implies these assumptions. -/
theorem two_cycle_other_visits [DecidableEq S] (huaw : IsUAWalk x n c)
    {a E : ℕ} (hE : 2 ≤ E) (hblockn : a + E ≤ n)
    (hdiff : c a ≠ c (a + 1)) (hcycle : c (a + 2) = c a)
    (hinside : ∀ t, a ≤ t → t ≤ a + E → c t = c a ∨ c t = c (a + 1))
    (hconfined : ∀ t, t ≤ n → (c t = c a ∨ c t = c (a + 1)) → a ≤ t ∧ t ≤ a + E)
    (s : S) (hs0 : s ≠ c a) (hs1 : s ≠ c (a + 1)) :
    (visitTimes n c s).card ≤ 2 := by
  classical
  by_contra hn
  have hv : 3 ≤ (visitTimes n c s).card := by omega
  obtain ⟨b, p, hp, hlast, hvis, _, hper⟩ := visits_progression huaw s (by omega)
  have hmul : 2 * p ≤ ((visitTimes n c s).card - 1) * p :=
    Nat.mul_le_mul_right p (by omega)
  have h3n : b + 2 * p ≤ n := by omega
  have hv0 : c b = s := by
    apply (hvis b (by omega)).2
    exact ⟨0, by omega, by simp⟩
  have hv1 : c (b + p) = s := by
    apply (hvis (b + p) (by omega)).2
    exact ⟨1, by omega, by simp⟩
  have hv2 : c (b + 2 * p) = s := by
    apply (hvis (b + 2 * p) h3n).2
    exact ⟨2, hv, rfl⟩
  have hout (t : ℕ) (hct : c t = s) : t < a ∨ a + E < t := by
    by_contra h
    have hh := hinside t (by omega) (by omega)
    rcases hh with hh | hh
    · exact hs0 (hct.symm.trans hh)
    · exact hs1 (hct.symm.trans hh)
  have hdisjoint : a + E < b ∨ b + 2 * p < a := by
    by_contra h
    have hb : b < a := by have := hout b hv0; omega
    have he : a + E < b + 2 * p := by have := hout (b + 2 * p) hv2; omega
    rcases hout (b + p) hv1 with hleft | hright
    · have haper := hper (a - p) (by omega) (by omega)
      rw [show a - p + p = a by omega] at haper
      have hh := hconfined (a - p) (by omega) (Or.inl haper)
      omega
    · have haper := hper a (by omega) (by omega)
      have hh := hconfined (a + p) (by omega) (Or.inl haper.symm)
      omega
  have hloop : Seg n c (c a) (c a) 2 (fun j => a + j) := by
    have hh := segW c (show a ≤ a + 2 by omega) (show a + 2 ≤ n by omega)
    simpa only [hcycle, Nat.add_sub_cancel_left] using hh
  have hC : Seg n c (c a) (c a) (b + 2 * p - b) (repit p 2 (fun j => a + j)) := by
    convert seg_repit hloop p using 1; omega
  have hchord : c b = c (b + 2 * p) := hv0.trans hv2.symm
  have hpos : a ≤ b ∨ b + 2 * p ≤ a := by rcases hdisjoint with h | h <;> omega
  have heq := exchange_one huaw (show b ≤ b + 2 * p by omega) h3n
    (show a ≤ n by omega) hchord hpos hC (edge x c (a + 1))
  have hzero : edgeCount x c (b + 2 * p - b) (fun j => b + j) (edge x c (a + 1)) = 0 := by
    apply edgeCount_eq_zero_iff.mpr
    intro j hj he
    have htail : c (b + j) = c (a + 1) := congrArg Prod.fst he
    have hh := hconfined (b + j) (by omega) (Or.inr htail)
    rcases hdisjoint with h | h <;> omega
  have hdiffedge : edge x c a ≠ edge x c (a + 1) := by
    intro h
    exact hdiff (congrArg Prod.fst h)
  have hcount : edgeCount x c 2 (fun j => a + j) (edge x c (a + 1)) = 1 := by
    simp [edgeCount, Finset.sum_range_succ, hdiffedge]
  have hrepeated : edgeCount x c (b + 2 * p - b)
      (repit p 2 (fun j => a + j)) (edge x c (a + 1)) = p := by
    rw [show b + 2 * p - b = p * 2 by omega, edgeCount_repit, hcount, Nat.mul_one]
  rw [hzero, hrepeated] at heq
  omega

/-- State-count consequence of a confined two-cycle. -/
theorem two_cycle_card [DecidableEq S] (huaw : IsUAWalk x n c)
    {a E : ℕ} (hE : 2 ≤ E) (hblockn : a + E ≤ n)
    (hdiff : c a ≠ c (a + 1)) (hcycle : c (a + 2) = c a)
    (hinside : ∀ t, a ≤ t → t ≤ a + E → c t = c a ∨ c t = c (a + 1))
    (hconfined : ∀ t, t ≤ n → (c t = c a ∨ c t = c (a + 1)) → a ≤ t ∧ t ≤ a + E) :
    n - E + 4 ≤ 2 * (walkStates n c).card := by
  classical
  let Q := walkStates n c
  let z := c a
  let z' := c (a + 1)
  have hz : z ∈ Q := Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr (by omega), rfl⟩
  have hz' : z' ∈ Q := Finset.mem_image.mpr ⟨a + 1, Finset.mem_range.mpr (by omega), rfl⟩
  have hz'e : z' ∈ Q.erase z := Finset.mem_erase.mpr ⟨hdiff.symm, hz'⟩
  have hq2 : 2 ≤ Q.card := Finset.one_lt_card.mpr ⟨z, hz, z', hz', hdiff⟩
  have hsum : ∑ s ∈ Q, (visitTimes n c s).card = n + 1 := by
    have hh := Finset.card_eq_sum_card_fiberwise
      (s := Finset.range (n + 1)) (t := Q) (f := c) (fun t ht => by
        change c t ∈ (Finset.range (n + 1)).image c
        exact Finset.mem_image.mpr ⟨t, ht, rfl⟩)
    simpa only [visitTimes, Finset.card_range] using hh.symm
  have hdisj : Disjoint (visitTimes n c z) (visitTimes n c z') := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact hdiff ((mem_visitTimes.mp ht).2.symm.trans (mem_visitTimes.mp ht').2)
  have hunion : visitTimes n c z ∪ visitTimes n c z' = Finset.Icc a (a + E) := by
    ext t
    simp only [Finset.mem_union, mem_visitTimes, Finset.mem_Icc]
    constructor
    · rintro (⟨ht, hz⟩ | ⟨ht, hz⟩)
      · exact hconfined t ht (Or.inl hz)
      · exact hconfined t ht (Or.inr hz)
    · rintro ⟨hat, hta⟩
      rcases hinside t hat hta with h | h
      · exact Or.inl ⟨by omega, h⟩
      · exact Or.inr ⟨by omega, h⟩
  have htwosum : (visitTimes n c z).card + (visitTimes n c z').card = E + 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Nat.card_Icc]
    omega
  have hsplit := Finset.sum_erase_add Q (fun s => (visitTimes n c s).card) hz
  have hsplit' := Finset.sum_erase_add (Q.erase z) (fun s => (visitTimes n c s).card) hz'e
  have hcard : ((Q.erase z).erase z').card = Q.card - 2 := by
    rw [Finset.card_erase_of_mem hz'e, Finset.card_erase_of_mem hz]
    omega
  have hother : ∑ s ∈ (Q.erase z).erase z', (visitTimes n c s).card ≤
      2 * ((Q.erase z).erase z').card := by
    calc _ ≤ ∑ _s ∈ (Q.erase z).erase z', 2 := by
          apply Finset.sum_le_sum
          intro s hs
          obtain ⟨hsz', hs⟩ := Finset.mem_erase.mp hs
          obtain ⟨hsz, _⟩ := Finset.mem_erase.mp hs
          exact two_cycle_other_visits huaw hE hblockn hdiff hcycle hinside hconfined s hsz hsz'
      _ = _ := by simp [Nat.mul_comm]
  rw [hcard] at hother
  dsimp only [Q, z, z'] at *
  omega

end AneVsAn.Generic
