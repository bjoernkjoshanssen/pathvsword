import RequestProject.ProofImports

/-!
# Elementary interval permutation facts for the walk classification

All indices in the binary proof are natural numbers. Keeping these facts in
interval form avoids repeated conversions between natural numbers and `Fin`.
-/

namespace AneVsAn.BinarySeparation

set_option autoImplicit false

/-- An increasing integer sequence grows by at least the distance between indices. -/
theorem increasing_interval_distance (f : ℕ → ℕ) {a b i : ℕ}
    (h : ∀ j, a ≤ j → j < b → f j < f (j + 1))
    (hai : a ≤ i) (hib : i ≤ b) : f a + (i - a) ≤ f i := by
  have haux : ∀ k, a + k ≤ b → f a + k ≤ f (a + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hk' : a + k ≤ b := by omega
      have hp := ih hk'
      have hs := h (a + k) (by omega) (by omega)
      simpa only [Nat.add_assoc] using (show f a + (k + 1) ≤ f (a + k + 1) by omega)
  have ht := haux (i - a) (by omega)
  simpa only [Nat.add_sub_of_le hai] using ht

/-- An increasing self-map of a finite integer interval is the identity. -/
theorem increasing_interval_eq (f : ℕ → ℕ) {a b : ℕ}
    (ha : a ≤ f a) (hb : f b ≤ b)
    (h : ∀ j, a ≤ j → j < b → f j < f (j + 1)) :
    ∀ j, a ≤ j → j ≤ b → f j = j := by
  intro j haj hjb
  have hleft := increasing_interval_distance f h haj hjb
  have hright := increasing_interval_distance f
    (a := j) (b := b) (i := b) (fun k hjk hkb => h k (by omega) hkb) hjb le_rfl
  omega

/-- A permutation of `0,…,n`, represented by a total natural-number function. -/
structure IntervalPermutation (n : ℕ) (f : ℕ → ℕ) : Prop where
  bounded : ∀ j, j ≤ n → f j ≤ n
  injective : ∀ j, j ≤ n → ∀ k, k ≤ n → f j = f k → j = k
  surjective : ∀ v, v ≤ n → ∃ j, j ≤ n ∧ f j = v

theorem IntervalPermutation.adjacent_ne {n : ℕ} {f : ℕ → ℕ}
    (h : IntervalPermutation n f) {j : ℕ} (hj : j < n) : f j ≠ f (j + 1) := by
  intro he
  have := h.injective j (by omega) (j + 1) (by omega) he
  omega

theorem IntervalPermutation.eq_id_of_no_descent {n : ℕ} {f : ℕ → ℕ}
    (h : IntervalPermutation n f) (hd : ∀ j, j < n → ¬f (j + 1) < f j) :
    ∀ j, j ≤ n → f j = j := by
  have hinc : ∀ j, 0 ≤ j → j < n → f j < f (j + 1) := by
    intro j _ hj
    have := h.adjacent_ne hj
    have := hd j hj
    omega
  intro j hj
  exact increasing_interval_eq f (Nat.zero_le _) (h.bounded n le_rfl) hinc j
    (Nat.zero_le _) hj

/-- If all decreases start at one of two exceptional values, all other adjacencies increase. -/
theorem IntervalPermutation.increasing_away_from {n : ℕ} {f : ℕ → ℕ}
    (h : IntervalPermutation n f) (hd : ∀ j, j < n → f (j + 1) < f j →
      f j = n - 1 ∨ f j = n) {j : ℕ} (hj : j < n)
    (h1 : f j ≠ n - 1) (h2 : f j ≠ n) : f j < f (j + 1) := by
  have hn := h.adjacent_ne hj
  by_contra hc
  have hlt : f (j + 1) < f j := by omega
  rcases hd j hj hlt with hh | hh
  · exact h1 hh
  · exact h2 hh

end AneVsAn.BinarySeparation
