import RequestProject.ProofImports

/-!
# The finite permutation argument for the central two-cycle

A permutation in which every increasing pair has the same displacement is a
sequence of increasing intervals whose images occur in reverse order. For the
endgame we only need the first four intervals, so we construct successive tails
directly instead of introducing a list of all maximal blocks.
-/

namespace AneVsAn.BinarySeparation

set_option autoImplicit false

structure LayeredTail (L : ℕ) (f : ℕ → ℕ) (start high : ℕ) : Prop where
  balance : start + high = L
  bounded : ∀ i, start ≤ i → i < L → f i < high
  onto : ∀ y, y < high → ∃ i, start ≤ i ∧ i < L ∧ f i = y

theorem LayeredTail.split {L start high : ℕ} {f : ℕ → ℕ}
    (h : LayeredTail L f start high) (hstart : start < L)
    (hinj : ∀ i, i < L → ∀ j, j < L → f i = f j → i = j)
    (hinc : ∀ i j, i < j → j < L → f i < f j → f j + i = f i + j) :
    0 < high - f start ∧ start + (high - f start) ≤ L ∧
      (∀ i, start ≤ i → i < start + (high - f start) →
        f i = f start + (i - start)) ∧
      LayeredTail L f (start + (high - f start)) (f start) := by
  have hfs := h.bounded start le_rfl hstart
  have hbal := h.balance
  have hsize : 0 < high - f start := by omega
  have hend : start + (high - f start) ≤ L := by omega
  have hblock : ∀ i, start ≤ i → i < start + (high - f start) →
      f i = f start + (i - start) := by
    intro i hi hie
    by_cases hieq : i = start
    · subst i
      simp
    obtain ⟨j, hjs, hjL, hfj⟩ := h.onto (f start + (i - start)) (by omega)
    have hj : start < j := by
      by_contra hj
      have hjeq : j = start := by omega
      rw [hjeq] at hfj
      omega
    have hfgt : f start < f j := by omega
    have hc := hinc start j hj hjL hfgt
    have hji : j = i := by omega
    simpa only [hji] using hfj
  refine ⟨hsize, hend, hblock, ?_⟩
  constructor
  · omega
  · intro i hi hiL
    have hib := h.bounded i (by omega) hiL
    by_contra hlt
    by_cases heq : f i = f start
    · have := hinj i hiL start hstart heq
      omega
    · have hc := hinc start i (by omega) hiL (by omega)
      omega
  · intro y hy
    obtain ⟨i, his, hiL, hfi⟩ := h.onto y (by omega)
    refine ⟨i, ?_, hiL, hfi⟩
    by_contra hn
    have hb := hblock i his (by omega)
    omega

/-- The abstract endgame. An increasing block of length `L` is excluded, every
cycle from two adjacent blocks is odd and longer than `L/2`, and odd cross-pair
spans exceed `3L/2`. These requirements are incompatible when `L = 2 mod 4`. -/
theorem layered_permutation_impossible {L : ℕ} {f : ℕ → ℕ}
    (hL : 1 ≤ L) (hmod : L % 4 = 2)
    (hbounds : ∀ i, i < L → f i < L)
    (honto : ∀ y, y < L → ∃ i, i < L ∧ f i = y)
    (hinj : ∀ i, i < L → ∀ j, j < L → f i = f j → i = j)
    (hinc : ∀ i j, i < j → j < L → f i < f j → f j + i = f i + j)
    (hnonid : ¬∀ i, i < L → f i = i)
    (hcycles : ∀ a b, a ≤ b → b < L → f a = f b + 1 →
      (b - a + 1) % 2 = 1 ∧ L < 2 * (b - a + 1))
    (hoddspan : ∀ s, s < L → (2 * L + 2 + f s - s) % 2 = 1 →
      3 * L < 2 * (2 * L + 2 + f s - s)) : False := by
  have htail : LayeredTail L f 0 L := by
    refine ⟨by omega, ?_, ?_⟩
    · intro i _ hi; exact hbounds i hi
    · intro y hy
      obtain ⟨i, hi, hfi⟩ := honto y hy
      exact ⟨i, Nat.zero_le _, hi, hfi⟩
  let a := L - f 0
  obtain ⟨ha, haL, hfirst, ht1⟩ := htail.split (by omega) hinj hinc
  simp only [Nat.zero_add] at haL hfirst ht1
  change 0 < a at ha
  change a ≤ L at haL
  change (∀ i, 0 ≤ i → i < a → f i = f 0 + (i - 0)) at hfirst
  change LayeredTail L f a (f 0) at ht1
  by_cases haeq : a = L
  · have hf0 : f 0 = 0 := by have := ht1.balance; omega
    apply hnonid
    intro i hi
    have hh := hfirst i (Nat.zero_le _) (by omega)
    simpa [hf0] using hh
  have haLt : a < L := by omega
  let b := f 0 - f a
  obtain ⟨hb, habL, hsecond, ht2⟩ := ht1.split haLt hinj hinc
  change 0 < b at hb
  change a + b ≤ L at habL
  change (∀ i, a ≤ i → i < a + b → f i = f a + (i - a)) at hsecond
  change LayeredTail L f (a + b) (f a) at ht2
  have hfirstlast : f 0 = f (a + b - 1) + 1 := by
    have hh := hsecond (a + b - 1) (by omega) (by omega)
    have hbdef : b = f 0 - f a := rfl
    have hfba := ht1.bounded a le_rfl haLt
    omega
  have hc1 := hcycles 0 (a + b - 1) (by omega) (by omega) hfirstlast
  have hc1' : (a + b) % 2 = 1 ∧ L < 2 * (a + b) := by
    simpa only [Nat.sub_zero, show a + b - 1 + 1 = a + b by omega] using hc1
  by_cases hab : a + b = L
  · omega
  have habLt : a + b < L := by omega
  let d := f a - f (a + b)
  obtain ⟨hd, habdL, hthird, ht3⟩ := ht2.split habLt hinj hinc
  change 0 < d at hd
  change a + b + d ≤ L at habdL
  change (∀ i, a + b ≤ i → i < a + b + d →
    f i = f (a + b) + (i - (a + b))) at hthird
  change LayeredTail L f (a + b + d) (f (a + b)) at ht3
  by_cases habd : a + b + d = L
  · have hf : f (a + b) = 0 := by have := ht3.balance; omega
    have hodd : (2 * L + 2 + f (a + b) - (a + b)) % 2 = 1 := by
      rw [hf]
      omega
    have hspan := hoddspan (a + b) habLt hodd
    rw [hf] at hspan
    omega
  have habdLt : a + b + d < L := by omega
  let e := f (a + b) - f (a + b + d)
  obtain ⟨he, habdeL, hfourth, ht4⟩ := ht3.split habdLt hinj hinc
  change 0 < e at he
  change a + b + d + e ≤ L at habdeL
  change (∀ i, a + b + d ≤ i → i < a + b + d + e →
    f i = f (a + b + d) + (i - (a + b + d))) at hfourth
  have hthirdlast : f (a + b) = f (a + b + d + e - 1) + 1 := by
    have hh := hfourth (a + b + d + e - 1) (by omega) (by omega)
    have hedef : e = f (a + b) - f (a + b + d) := rfl
    have hfe := ht3.bounded (a + b + d) le_rfl habdLt
    omega
  have hc2 := hcycles (a + b) (a + b + d + e - 1)
    (by omega) (by omega) hthirdlast
  have hc2' : L < 2 * (d + e) := by
    have hsub : a + b + d + e - 1 - (a + b) + 1 = d + e := by omega
    simpa only [hsub] using hc2.2
  omega

end AneVsAn.BinarySeparation
