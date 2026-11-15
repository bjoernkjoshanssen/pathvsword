import RequestProject.Defs

/-!
# The binary family and the condition excluding long repetitions

For `L ≥ 2`, the relevant values of `u` are `u 1, …, u (L - 2)`.
The word is `0 u 1 0^(L+1) 1 u 0`, of length `3 * L + 1`.
These definitions are independent of the automata used to prove separation.
-/

namespace AneVsAn.BinarySeparation

set_option autoImplicit false

/-- The binary word `0 u 1 0^(L+1) 1 u 0`. Values beyond its length are immaterial. -/
def word (L : ℕ) (u : ℕ → Bool) (t : ℕ) : Bool :=
  if t = 0 then false
  else if t < L - 1 then u t
  else if t = L - 1 then true
  else if t < 2 * L + 1 then false
  else if t = 2 * L + 1 then true
  else if t < 3 * L then u (t - (2 * L + 1))
  else false

@[simp] theorem word_zero (L : ℕ) (u : ℕ → Bool) : word L u 0 = false := by
  simp [word]

theorem word_left {L t : ℕ} {u : ℕ → Bool} (ht : 1 ≤ t) (htL : t ≤ L - 2)
    (hL : 2 ≤ L) : word L u t = u t := by
  simp [word, show t ≠ 0 by omega, show t < L - 1 by omega]

theorem word_left_delimiter {L : ℕ} {u : ℕ → Bool} (hL : 2 ≤ L) :
    word L u (L - 1) = true := by
  simp [word, show L - 1 ≠ 0 by omega]

theorem word_run {L t : ℕ} {u : ℕ → Bool} (hL : 2 ≤ L)
    (ht : L ≤ t) (htL : t ≤ 2 * L) : word L u t = false := by
  simp [word, show t ≠ 0 by omega, show ¬t < L - 1 by omega,
    show t ≠ L - 1 by omega, show t < 2 * L + 1 by omega]

theorem word_right_delimiter {L : ℕ} {u : ℕ → Bool} (hL : 2 ≤ L) :
    word L u (2 * L + 1) = true := by
  simp [word, show ¬2 * L + 1 < L - 1 by omega,
    show 2 * L + 1 ≠ L - 1 by omega]

theorem word_right {L t : ℕ} {u : ℕ → Bool} (ht : 1 ≤ t) (htL : t ≤ L - 2)
    (hL : 2 ≤ L) : word L u (2 * L + 1 + t) = u t := by
  simp [word, show t ≠ 0 by omega, show ¬2 * L + 1 + t < L - 1 by omega,
    show 2 * L + 1 + t ≠ L - 1 by omega, show ¬2 * L + 1 + t < 2 * L + 1 by omega,
    show 2 * L + 1 + t < 3 * L by omega]

theorem word_last {L : ℕ} {u : ℕ → Bool} (hL : 2 ≤ L) : word L u (3 * L) = false := by
  simp [word, show 3 * L ≠ 0 by omega, show ¬3 * L < L - 1 by omega,
    show 3 * L ≠ L - 1 by omega, show ¬3 * L < 2 * L + 1 by omega,
    show 3 * L ≠ 2 * L + 1 by omega]

/-- Only the `L - 2` specified seed positions affect the family word. -/
theorem word_congr {L : ℕ} {u v : ℕ → Bool} (hL : 2 ≤ L)
    (huv : ∀ t, 1 ≤ t → t ≤ L - 2 → u t = v t) : word L u = word L v := by
  funext t
  by_cases h0 : t = 0
  · simp [h0]
  by_cases hleft : t < L - 1
  · simp [word, h0, hleft, huv t (by omega) (by omega)]
  by_cases hdel : t = L - 1
  · subst t
    rw [word_left_delimiter hL, word_left_delimiter hL]
  by_cases hrun : t < 2 * L + 1
  · simp [word, h0, hleft, hdel, hrun]
  by_cases hdel' : t = 2 * L + 1
  · subst t
    rw [word_right_delimiter hL, word_right_delimiter hL]
  by_cases hright : t < 3 * L
  · simp [word, h0, hleft, hdel, hrun, hdel', hright,
      huv (t - (2 * L + 1)) (by omega) (by omega)]
  · simp [word, h0, hleft, hdel, hrun, hdel', hright]

/-- The occurrence `[i,j)` has period `p`. -/
def HasPeriod (x : ℕ → Bool) (i j p : ℕ) : Prop :=
  ∀ t, i ≤ t → t + p < j → x t = x (t + p)

/-- Long periodic occurrences must lie inside the designated central zero run. -/
def BGood (L B : ℕ) (u : ℕ → Bool) : Prop :=
  ∀ i j p, 1 ≤ p → i ≤ j → j ≤ 3 * L + 1 → 2 * p ≤ j - i →
    ¬(L ≤ i ∧ j ≤ 2 * L + 1) → HasPeriod (word L u) i j p → j - i < p + B

theorem good_congr {L B : ℕ} {u v : ℕ → Bool} (hL : 2 ≤ L)
    (huv : ∀ t, 1 ≤ t → t ≤ L - 2 → u t = v t) : BGood L B u ↔ BGood L B v := by
  unfold BGood
  rw [word_congr hL huv]

theorem hasPeriod_subinterval {x : ℕ → Bool} {i j i' j' p : ℕ}
    (h : HasPeriod x i j p) (hi : i ≤ i') (hj : j' ≤ j) :
    HasPeriod x i' j' p := by
  intro t ht ht'
  exact h t (by omega) (by omega)

/-- Good words cannot have an entirely zero seed. -/
theorem good_not_all_false {L B : ℕ} {u : ℕ → Bool}
    (hL : 3 ≤ L) (hB : B ≤ L - 2) (hg : BGood L B u) :
    ¬(∀ t, 1 ≤ t → t ≤ L - 2 → u t = false) := by
  intro hu
  have hz : ∀ t, t < L - 1 → word L u t = false := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t; exact word_zero L u
    · rw [word_left (by omega) (by omega) (by omega)]
      exact hu t (by omega) (by omega)
  have hp : HasPeriod (word L u) 0 (L - 1) 1 := by
    intro t _ ht
    rw [hz t (by omega), hz (t + 1) ht]
  have := hg 0 (L - 1) 1 (by omega) (by omega) (by omega) (by omega)
    (by omega) hp
  omega

/-- Good words cannot have an entirely one seed. -/
theorem good_not_all_true {L B : ℕ} {u : ℕ → Bool}
    (hL : 3 ≤ L) (hB : B ≤ L - 2) (hg : BGood L B u) :
    ¬(∀ t, 1 ≤ t → t ≤ L - 2 → u t = true) := by
  intro hu
  have hz : ∀ t, 1 ≤ t → t < L → word L u t = true := by
    intro t ht htL
    by_cases hlast : t = L - 1
    · subst t; exact word_left_delimiter (by omega)
    · rw [word_left ht (by omega) (by omega)]
      exact hu t ht (by omega)
  have hp : HasPeriod (word L u) 1 L 1 := by
    intro t ht ht'
    rw [hz t ht (by omega), hz (t + 1) (by omega) ht']
  have := hg 1 L 1 (by omega) (by omega) (by omega) (by omega)
    (by omega) hp
  omega

end AneVsAn.BinarySeparation
