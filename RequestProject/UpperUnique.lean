import RequestProject.Defs

/-!
# The unique acceptor `D_k`

This file formalizes Section 3.2 of `anevsanseparationv4.tex`, i.e.
Proposition 3.3 (`prop:upper-unique`): the NFA `D_k` with `k+6` states
uniquely accepts `z_k`, whence `A_N(z_k) ≤ k+6`.

States are encoded by natural numbers:
`s_0,…,s_{k-1}` are `0,…,k-1`, `A` is `k`, `x_1,x_2,x_3` are `k+1,k+2,k+3`,
`t_1` is `k+4` and `t_2` is `k+5`.
-/

namespace AneVsAn

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The transition relation of the NFA `D_k` of Proposition 3.3 (`prop:upper-unique`)
of `anevsanseparationv4.tex`, on the numerical encoding of its states. -/
def stepDn (k : ℕ) (i : ℕ) (α : Ltr) (j : ℕ) : Prop :=
    (i + 1 < k ∧ α = Ltr.a (i + 1) ∧ j = i + 1)
  ∨ (i = k - 1 ∧ α = Ltr.a k ∧ j = k)
  ∨ (i = k - 1 ∧ α = Ltr.d ∧ j = k + 4)
  ∨ (i = k + 4 ∧ α = Ltr.e ∧ j = k + 5)
  ∨ (i = k ∧ α = Ltr.b ∧ j = k)
  ∨ (i = k ∧ α = Ltr.b ∧ j = k + 1)
  ∨ (i = k + 1 ∧ α = Ltr.b ∧ j = k + 2)
  ∨ (i = k + 2 ∧ α = Ltr.b ∧ j = k + 3)
  ∨ (i = k + 3 ∧ α = Ltr.c ∧ j = 0)

section Structure

variable {k L : ℕ} {x : ℕ → Ltr} {f : ℕ → ℕ}

private theorem ltD_of_ne_final (hL : f L = k + 5) {u : ℕ} (hu : u ≤ L) (h : f u ≠ k + 5) :
    u < L := by
  rcases lt_or_eq_of_le hu with h' | h'
  · exact h'
  · exact absurd (h' ▸ hL) h

/-- Along the chain `s_0 → ⋯ → s_{k-1}` the automaton `D_k` is deterministic. -/
theorem stepDn_chain (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepDn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 5) {u i : ℕ} (hi : i < k - 1) (hu : u ≤ L) (hfu : f u = i) :
    u < L ∧ x u = Ltr.a (i + 1) ∧ f (u + 1) = i + 1 := by
  have hlt : u < L := ltD_of_ne_final hL hu (by omega)
  refine ⟨hlt, ?_, ?_⟩ <;>
  · have h := hrun u hlt
    rw [hfu] at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      first
        | exact h2
        | exact h3
        | (exfalso; omega)

theorem chainD (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepDn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 5) {u : ℕ} (hu : u ≤ L) (hfu : f u = 0) :
    ∀ j, j ≤ k - 1 → u + j ≤ L ∧ f (u + j) = j ∧ ∀ i, i < j → x (u + i) = Ltr.a (i + 1) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨by simpa using hu, by simpa using hfu, by omega⟩
  | succ j ih =>
    intro hj
    obtain ⟨hle, hfj, hx⟩ := ih (by omega)
    obtain ⟨h1, h2, h3⟩ := stepDn_chain hk hrun hL (i := j) (by omega) hle hfj
    refine ⟨by omega, by rw [show u + (j + 1) = u + j + 1 by ring]; exact h3, ?_⟩
    intro i hi
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
    · exact hx i h
    · subst h; exact h2

theorem stepDn_at_last (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepDn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 5) {u : ℕ} (hu : u ≤ L) (hfu : f u = k - 1) :
    (x u = Ltr.a k ∧ f (u + 1) = k) ∨
      (x u = Ltr.d ∧ x (u + 1) = Ltr.e ∧ u + 2 = L ∧ f (u + 1) = k + 4 ∧ f (u + 2) = k + 5) := by
  have hlt : u < L := ltD_of_ne_final hL hu (by omega)
  have h := hrun u hlt
  rw [hfu] at h
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact absurd h1 (by omega)
  · exact Or.inl ⟨h2, h3⟩
  · right
    have hlt1 : u + 1 < L := ltD_of_ne_final hL (by omega) (by rw [h3]; omega)
    have h' := hrun (u + 1) hlt1
    rw [h3] at h'
    have he : x (u + 1) = Ltr.e ∧ f (u + 2) = k + 5 := by
      rcases h' with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ |
        ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
      · exact absurd g1 (by omega)
      · exact absurd g1 (by omega)
      · exact absurd g1 (by omega)
      · exact ⟨g2, g3⟩
      all_goals exact absurd g1 (by omega)
    refine ⟨h2, he.1, ?_, h3, he.2⟩
    by_contra hcon
    have hlt2 : u + 2 < L := by omega
    have h'' := hrun (u + 2) hlt2
    rw [he.2] at h''
    rcases h'' with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ |
      ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;> exact absurd g1 (by omega)
  all_goals exact absurd h1 (by omega)

/-- The `b`-gadget of `D_k`: from `A` the run loops at `A`, then goes
`A → x_1 → x_2 → x_3` and takes the `c`-edge back to `s_0`.  The set of lengths is
`T' = [3,∞)` and the path of a given length is unique
(proof of Proposition 3.3, `prop:upper-unique`). -/
theorem gadgetD (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepDn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 5) : ∀ N u, L - u ≤ N → u ≤ L → f u = k →
      ∃ t, 3 ≤ t ∧ u + t + 1 ≤ L ∧ (∀ j, j < t → x (u + j) = Ltr.b) ∧
        (∀ j, j ≤ t - 3 → f (u + j) = k) ∧ f (u + (t - 2)) = k + 1 ∧
        f (u + (t - 1)) = k + 2 ∧ f (u + t) = k + 3 ∧ x (u + t) = Ltr.c ∧
        f (u + t + 1) = 0 := by
  intro N
  induction N with
  | zero =>
    intro u hNu hu hfu
    exact absurd (show f L = k by rw [show L = u by omega]; exact hfu) (by omega)
  | succ N ih =>
    intro u hNu hu hfu
    have hlt : u < L := ltD_of_ne_final hL hu (by omega)
    have h := hrun u hlt
    rw [hfu] at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · -- loop `A → A`
      obtain ⟨t, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8⟩ :=
        ih (u + 1) (by omega) (by omega) h3
      refine ⟨t + 1, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        rcases Nat.eq_zero_or_pos j with h' | h'
        · subst h'; simpa using h2
        · have := ht2 (j - 1) (by omega)
          rw [show u + 1 + (j - 1) = u + j by omega] at this
          exact this
      · intro j hj
        rcases Nat.eq_zero_or_pos j with h' | h'
        · subst h'; simpa using hfu
        · have := ht3 (j - 1) (by omega)
          rw [show u + 1 + (j - 1) = u + j by omega] at this
          exact this
      · have := ht4; rw [show u + (t + 1 - 2) = u + 1 + (t - 2) by omega]; exact this
      · have := ht5; rw [show u + (t + 1 - 1) = u + 1 + (t - 1) by omega]; exact this
      · rw [show u + (t + 1) = u + 1 + t by ring]; exact ht6
      · rw [show u + (t + 1) = u + 1 + t by ring]; exact ht7
      · rw [show u + (t + 1) + 1 = u + 1 + t + 1 by ring]; exact ht8
    · -- escape `A → x_1 → x_2 → x_3 → s_0`
      have h1lt : u + 1 < L := ltD_of_ne_final hL (by omega) (by rw [h3]; omega)
      have s1 := hrun (u + 1) h1lt
      rw [h3] at s1
      have g1 : x (u + 1) = Ltr.b ∧ f (u + 2) = k + 2 := by
        rcases s1 with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ |
          ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact ⟨a2, a3⟩
        all_goals exact absurd a1 (by omega)
      have h2lt : u + 2 < L := ltD_of_ne_final hL (by omega) (by rw [g1.2]; omega)
      have s2 := hrun (u + 2) h2lt
      rw [g1.2] at s2
      have g2 : x (u + 2) = Ltr.b ∧ f (u + 3) = k + 3 := by
        rcases s2 with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ |
          ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact ⟨a2, a3⟩
        · exact absurd a1 (by omega)
      have h3lt : u + 3 < L := ltD_of_ne_final hL (by omega) (by rw [g2.2]; omega)
      have s3 := hrun (u + 3) h3lt
      rw [g2.2] at s3
      have g3 : x (u + 3) = Ltr.c ∧ f (u + 4) = 0 := by
        rcases s3 with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ |
          ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact absurd a1 (by omega)
        · exact ⟨a2, a3⟩
      refine ⟨3, le_rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        interval_cases j
        · simpa using h2
        · simpa using g1.1
        · simpa using g2.1
      · intro j hj
        rw [show j = 0 by omega]; simpa using hfu
      · simpa using h3
      · simpa using g1.2
      · simpa using g2.2
      · simpa using g3.1
      · simpa using g3.2
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)

/-- Block decomposition for `D_k` (proof of Proposition 3.3, `prop:upper-unique`). -/
theorem blockD (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepDn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 5) {u : ℕ} (hu : u ≤ L) (hfu : f u = 0) :
    (L = u + (k + 1) ∧ (∀ j, j ≤ k - 1 → f (u + j) = j) ∧
        (∀ j, j < k - 1 → x (u + j) = Ltr.a (j + 1)) ∧
        x (u + (k - 1)) = Ltr.d ∧ x (u + k) = Ltr.e ∧
        f (u + k) = k + 4 ∧ f (u + (k + 1)) = k + 5) ∨
    (∃ t, 3 ≤ t ∧ u + (k + 1 + t) ≤ L ∧
        (∀ j, j ≤ k - 1 → f (u + j) = j) ∧
        (∀ j, j < k → x (u + j) = Ltr.a (j + 1)) ∧
        (∀ j, j < t → x (u + k + j) = Ltr.b) ∧
        (∀ j, j ≤ t - 3 → f (u + k + j) = k) ∧
        f (u + k + (t - 2)) = k + 1 ∧ f (u + k + (t - 1)) = k + 2 ∧
        f (u + k + t) = k + 3 ∧
        x (u + k + t) = Ltr.c ∧ f (u + (k + 1 + t)) = 0) := by
  obtain ⟨hle, hfk, hxs⟩ := chainD hk hrun hL hu hfu (k - 1) le_rfl
  have hfall : ∀ j, j ≤ k - 1 → f (u + j) = j := fun j hj => (chainD hk hrun hL hu hfu j hj).2.1
  rcases stepDn_at_last hk hrun hL hle hfk with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5⟩
  · right
    have hA : f (u + k) = k := by
      rw [show u + k = u + (k - 1) + 1 by omega]; exact h2
    have hlt' : u + (k - 1) < L := ltD_of_ne_final hL hle (by rw [hfk]; omega)
    obtain ⟨t, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8⟩ :=
      gadgetD hk hrun hL (L - (u + k)) (u + k) le_rfl (by omega) hA
    refine ⟨t, ht0, by omega, hfall, ?_, ht2, ht3, ht4, ht5, ht6, ht7, ?_⟩
    · intro j hj
      rcases Nat.lt_or_ge j (k - 1) with h' | h'
      · exact hxs j h'
      · have hjk : j = k - 1 := by omega
        subst hjk
        rw [show k - 1 + 1 = k by omega]
        exact h1
    · rw [show u + (k + 1 + t) = u + k + t + 1 by ring]; exact ht8
  · left
    exact ⟨by omega, hfall, hxs, h1, by rw [show u + k = u + (k - 1) + 1 by omega]; exact h2,
      by rw [show u + k = u + (k - 1) + 1 by omega]; exact h4,
      by rw [show u + (k + 1) = u + (k - 1) + 2 by omega]; exact h5⟩

theorem blockD_len (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepDn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 5) {u : ℕ} (hu : u ≤ L) (hfu : f u = 0) : u + (k + 1) ≤ L := by
  rcases blockD hk hrun hL hu hfu with ⟨h, _⟩ | ⟨t, ht0, ht1, _⟩
  · omega
  · omega

end Structure

/-- The unique accepting path of `D_k` on `z_k` (Proposition 3.3, `prop:upper-unique`). -/
def canD (k t : ℕ) : ℕ :=
  if t < k then t
  else if t ≤ 2 * k + 2 then k
  else if t = 2 * k + 3 then k + 1
  else if t = 2 * k + 4 then k + 2
  else if t = 2 * k + 5 then k + 3
  else if t ≤ 3 * k + 5 then t - (2 * k + 6)
  else if t = 3 * k + 6 then k + 4
  else k + 5

theorem canD_lt (k t : ℕ) : canD k t < k + 6 := by
  unfold canD; split_ifs <;> omega

theorem canD_zero {k : ℕ} (hk : 3 ≤ k) : canD k 0 = 0 := by
  unfold canD; split_ifs <;> omega

theorem canD_end {k : ℕ} (hk : 3 ≤ k) : canD k (wlen k) = k + 5 := by
  show canD k (3 * k + 7) = k + 5
  unfold canD; split_ifs <;> omega

/-- **Proposition 3.3 (`prop:upper-unique`)**, the hard direction: every accepting run
of `D_k` of length `n = 3k+7` spells `z_k` and visits the states `canD k t`. -/
theorem stepDn_unique {k : ℕ} (hk : 3 ≤ k) {x : ℕ → Ltr} {f : ℕ → ℕ}
    (hrun : ∀ t, t < wlen k → stepDn k (f t) (x t) (f (t + 1)))
    (h0 : f 0 = 0) (hL : f (wlen k) = k + 5) :
    (∀ t, t < wlen k → x t = zw k t) ∧ (∀ t, t ≤ wlen k → f t = canD k t) := by
  have hLval : wlen k = 3 * k + 7 := rfl
  rcases blockD hk hrun hL (by omega) h0 with
    ⟨h, _⟩ | ⟨t₁, ht₁0, ht₁1, hF, ht₁2, ht₁3, hG0, hG1, hG2, hG3, ht₁4, ht₁5⟩
  · exact absurd h (by omega)
  rcases blockD hk hrun hL (u := 0 + (k + 1 + t₁)) (by omega) ht₁5 with
    ⟨h, hB0, hB1, hB2, hB3, hB4, hB5⟩ | ⟨t₂, ht₂0, ht₂1, _, _, _, _, _, _, _, _, ht₂5⟩
  · have ht₁ : t₁ = k + 5 := by omega
    subst ht₁
    simp only [zero_add] at hF ht₁2 ht₁3 hG0 hG1 hG2 hG3 ht₁4 ht₁5 hB0 hB1 hB2 hB3 hB4 hB5
    constructor
    · intro s hs
      rw [hLval] at hs
      rcases Nat.lt_or_ge s k with h1 | h1
      · rw [ht₁2 s h1, zw_a h1]
      · rcases Nat.lt_or_ge s (2 * k + 5) with h2 | h2
        · have hb := ht₁3 (s - k) (by omega)
          rw [show k + (s - k) = s by omega] at hb
          rw [hb, zw_b h1 h2]
        · rcases eq_or_lt_of_le h2 with h3 | h3
          · rw [← h3, show (2 * k + 5 : ℕ) = k + (k + 5) by ring, ht₁4,
              zw_c (by omega : k + (k + 5) = 2 * k + 5)]
          · rcases Nat.lt_or_ge s (3 * k + 5) with h4 | h4
            · have hc := hB1 (s - (k + 1 + (k + 5))) (by omega)
              rw [show k + 1 + (k + 5) + (s - (k + 1 + (k + 5))) = s by omega] at hc
              rw [hc, zw_a' (by omega) h4]
              congr 1
              omega
            · rcases eq_or_lt_of_le h4 with h5 | h5
              · rw [← h5, show (3 * k + 5 : ℕ) = k + 1 + (k + 5) + (k - 1) by omega, hB2,
                  zw_d (by omega) (by omega : k + 1 + (k + 5) + (k - 1) = 3 * k + 5)]
              · have hs6 : s = 3 * k + 6 := by omega
                subst hs6
                rw [show (3 * k + 6 : ℕ) = k + 1 + (k + 5) + k by omega, hB3,
                  zw_e (by omega : k + 1 + (k + 5) + k = 3 * k + 6)]
    · intro s hs
      rw [hLval] at hs
      rcases Nat.lt_or_ge s k with h1 | h1
      · rw [hF s (by omega), show canD k s = s by unfold canD; rw [if_pos h1]]
      · rcases Nat.lt_or_ge s (2 * k + 3) with h2 | h2
        · have := hG0 (s - k) (by omega)
          rw [show k + (s - k) = s by omega] at this
          rw [this, show canD k s = k by unfold canD; split_ifs <;> omega]
        · rcases eq_or_lt_of_le h2 with h3 | h3
          · rw [← h3, show canD k (2 * k + 3) = k + 1 by unfold canD; split_ifs <;> omega,
              show (2 * k + 3 : ℕ) = k + (k + 5 - 2) by omega]
            exact hG1
          · rcases eq_or_lt_of_le (show 2 * k + 4 ≤ s by omega) with h4 | h4
            · rw [← h4, show canD k (2 * k + 4) = k + 2 by unfold canD; split_ifs <;> omega,
                show (2 * k + 4 : ℕ) = k + (k + 5 - 1) by omega]
              exact hG2
            · rcases eq_or_lt_of_le (show 2 * k + 5 ≤ s by omega) with h5 | h5
              · rw [← h5, show canD k (2 * k + 5) = k + 3 by unfold canD; split_ifs <;> omega,
                  show (2 * k + 5 : ℕ) = k + (k + 5) by omega]
                exact hG3
              · rcases Nat.lt_or_ge s (3 * k + 6) with h6 | h6
                · have := hB0 (s - (k + 1 + (k + 5))) (by omega)
                  rw [show k + 1 + (k + 5) + (s - (k + 1 + (k + 5))) = s by omega] at this
                  rw [this, show canD k s = s - (2 * k + 6) by unfold canD; split_ifs <;> omega]
                  omega
                · rcases eq_or_lt_of_le h6 with h7 | h7
                  · rw [← h7, show canD k (3 * k + 6) = k + 4 by unfold canD; split_ifs <;> omega,
                      show (3 * k + 6 : ℕ) = k + 1 + (k + 5) + k by omega]
                    exact hB4
                  · have : s = 3 * k + 7 := by omega
                    subst this
                    rw [show canD k (3 * k + 7) = k + 5 by unfold canD; split_ifs <;> omega,
                      show (3 * k + 7 : ℕ) = k + 1 + (k + 5) + (k + 1) by omega]
                    exact hB5
  · exfalso
    rcases blockD hk hrun hL (u := 0 + (k + 1 + t₁) + (k + 1 + t₂)) ht₂1 ht₂5 with
      ⟨h, _⟩ | ⟨t₃, ht₃0, ht₃1, _, _, _, _, _, _, _, _, ht₃5⟩
    · omega
    · have h4 := blockD_len hk hrun hL
        (u := 0 + (k + 1 + t₁) + (k + 1 + t₂) + (k + 1 + t₃)) ht₃1 ht₃5
      omega

/-- The canonical path is a path of `D_k` spelling `z_k`. -/
theorem canD_isRun {k : ℕ} (hk : 3 ≤ k) :
    ∀ t, t < wlen k → stepDn k (canD k t) (zw k t) (canD k (t + 1)) := by
  intro t ht
  have ht' : t < 3 * k + 7 := ht
  have hcase : t + 1 < k ∨ t + 1 = k ∨ (k ≤ t ∧ t ≤ 2 * k + 1) ∨ t = 2 * k + 2 ∨
      t = 2 * k + 3 ∨ t = 2 * k + 4 ∨ t = 2 * k + 5 ∨ (2 * k + 6 ≤ t ∧ t ≤ 3 * k + 4) ∨
      t = 3 * k + 5 ∨ t = 3 * k + 6 := by omega
  rcases hcase with h | h | ⟨h1, h2⟩ | h | h | h | h | ⟨h1, h2⟩ | h | h
  · rw [show canD k t = t by unfold canD; split_ifs <;> omega,
      show canD k (t + 1) = t + 1 by unfold canD; rw [if_pos (show t + 1 < k by omega)],
      zw_a (by omega)]
    exact Or.inl ⟨by omega, rfl, rfl⟩
  · rw [show canD k t = t by unfold canD; split_ifs <;> omega,
      show canD k (t + 1) = k by unfold canD; split_ifs <;> omega, zw_a (by omega)]
    exact Or.inr (Or.inl ⟨by omega, by rw [h], rfl⟩)
  · rw [show canD k t = k by unfold canD; split_ifs <;> omega,
      show canD k (t + 1) = k by unfold canD; split_ifs <;> omega,
      zw_b (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
  · rw [show canD k t = k by unfold canD; split_ifs <;> omega,
      show canD k (t + 1) = k + 1 by unfold canD; split_ifs <;> omega,
      zw_b (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))
  · rw [show canD k t = k + 1 by unfold canD; split_ifs <;> omega,
      show canD k (t + 1) = k + 2 by unfold canD; split_ifs <;> omega,
      zw_b (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))
  · rw [show canD k t = k + 2 by unfold canD; split_ifs <;> omega,
      show canD k (t + 1) = k + 3 by unfold canD; split_ifs <;> omega,
      zw_b (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))))
  · rw [show canD k t = k + 3 by unfold canD; split_ifs <;> omega,
      show canD k (t + 1) = 0 by unfold canD; split_ifs <;> omega, zw_c h]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))))
  · rw [show canD k t = t - (2 * k + 6) by unfold canD; split_ifs <;> omega,
      show canD k (t + 1) = t - (2 * k + 6) + 1 by unfold canD; split_ifs <;> omega,
      zw_a' (by omega) (by omega)]
    refine Or.inl ⟨by omega, ?_, rfl⟩
    congr 1
    omega
  · rw [show canD k t = k - 1 by unfold canD; split_ifs <;> omega,
      show canD k (t + 1) = k + 4 by unfold canD; split_ifs <;> omega, zw_d (by omega) h]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · rw [show canD k t = k + 4 by unfold canD; split_ifs <;> omega,
      show canD k (t + 1) = k + 5 by unfold canD; split_ifs <;> omega, zw_e h]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))

/-- **Proposition 3.3 (`prop:upper-unique`)**: `D_k` uniquely accepts `z_k`, hence
`A_N(z_k) ≤ k+6`. -/
theorem AN_upper {k : ℕ} (hk : 3 ≤ k) : AN (wlen k) (zw k) ≤ k + 6 := by
  refine AN_le (q := k + 6) ⟨fun p α q => stepDn k p.val α q.val, ⟨0, by omega⟩,
    fun q => q.val = k + 5, ⟨⟨fun t => ⟨canD k t, canD_lt k t⟩, ?_, ?_, ?_⟩, ?_⟩⟩
  · exact Fin.ext (by simpa using canD_zero hk)
  · exact canD_end hk
  · intro t ht; exact canD_isRun hk t ht
  · intro y p w q hp hq
    have H1 := stepDn_unique hk (fun s hs => hp.2.2 s hs) (by rw [hp.1]) hp.2.1
    have H2 := stepDn_unique hk (fun s hs => hq.2.2 s hs) (by rw [hq.1]) hq.2.1
    exact ⟨fun t ht => by rw [H1.1 t ht, H2.1 t ht],
      fun t ht => Fin.ext (by rw [H1.2 t ht, H2.2 t ht])⟩

/-- The set of sizes of NFAs uniquely accepting `z_k` is nonempty
(Proposition 3.3, `prop:upper-unique`). -/
theorem uniqueSizes_nonempty {k : ℕ} (hk : 3 ≤ k) : (UniqueSizes (wlen k) (zw k)).Nonempty := by
  refine ⟨k + 6, ⟨fun p α q => stepDn k p.val α q.val, ⟨0, by omega⟩,
    fun q => q.val = k + 5, ⟨⟨fun t => ⟨canD k t, canD_lt k t⟩, ?_, ?_, ?_⟩, ?_⟩⟩⟩
  · exact Fin.ext (by simpa using canD_zero hk)
  · exact canD_end hk
  · intro t ht; exact canD_isRun hk t ht
  · intro y p w q hp hq
    have H1 := stepDn_unique hk (fun s hs => hp.2.2 s hs) (by rw [hp.1]) hp.2.1
    have H2 := stepDn_unique hk (fun s hs => hq.2.2 s hs) (by rw [hq.1]) hq.2.1
    exact ⟨fun t ht => by rw [H1.1 t ht, H2.1 t ht],
      fun t ht => Fin.ext (by rw [H1.2 t ht, H2.2 t ht])⟩

end AneVsAn
