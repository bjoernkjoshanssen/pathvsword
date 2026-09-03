import RequestProject.Defs

/-!
# The exact acceptor `M_k`

This file formalizes Section 3.1 of `anevsanseparationv4.tex`:
the NFA `M_k` with `k+5` states (Figure 1, `fig:M3`), Lemma 3.1 (`lem:gadgetT`)
in the form of the structural analysis of its `b`-gadget, and the hard direction of
Proposition 3.2 (`prop:upper-exact`): every accepting path of `M_k` of length
`n = 3k+7` spells `z_k`.

States are encoded by natural numbers:
`s_0,…,s_{k-1}` are `0,…,k-1`, `A` is `k`, `X` is `k+1`, `B` is `k+2`,
`t_1` is `k+3` and `t_2` is `k+4`.
-/

namespace AneVsAn

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The transition relation of the NFA `M_k` of Figure 1 (`fig:M3`) of
`anevsanseparationv4.tex`, on the numerical encoding of its states. -/
def stepMn (k : ℕ) (i : ℕ) (α : Ltr) (j : ℕ) : Prop :=
    (i + 1 < k ∧ α = Ltr.a (i + 1) ∧ j = i + 1)
  ∨ (i = k - 1 ∧ α = Ltr.a k ∧ j = k)
  ∨ (i = k - 1 ∧ α = Ltr.d ∧ j = k + 3)
  ∨ (i = k + 3 ∧ α = Ltr.e ∧ j = k + 4)
  ∨ (i = k ∧ α = Ltr.b ∧ j = k + 1)
  ∨ (i = k + 1 ∧ α = Ltr.b ∧ j = k + 2)
  ∨ (i = k + 2 ∧ α = Ltr.b ∧ j = k)
  ∨ (i = k + 2 ∧ α = Ltr.b ∧ j = k + 2)
  ∨ (i = k + 1 ∧ α = Ltr.c ∧ j = 0)

section Structure

variable {k L : ℕ} {x : ℕ → Ltr} {f : ℕ → ℕ}

/-- A time strictly before the end of an accepting run, detected by the state visited. -/
private theorem lt_of_ne_final (hL : f L = k + 4) {u : ℕ} (hu : u ≤ L) (h : f u ≠ k + 4) :
    u < L := by
  rcases lt_or_eq_of_le hu with h' | h'
  · exact h'
  · exact absurd (h' ▸ hL) h

/-- Along the chain `s_0 → s_1 → ⋯ → s_{k-1}` the automaton `M_k` is deterministic. -/
theorem stepMn_chain (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepMn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 4) {u i : ℕ} (hi : i < k - 1) (hu : u ≤ L) (hfu : f u = i) :
    u < L ∧ x u = Ltr.a (i + 1) ∧ f (u + 1) = i + 1 := by
  have hlt : u < L := lt_of_ne_final hL hu (by omega)
  refine ⟨hlt, ?_, ?_⟩ <;>
  · have h := hrun u hlt
    rw [hfu] at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      first
        | exact h2
        | exact h3
        | (exfalso; omega)

/-- Riding the chain: from a visit of `s_0` at time `u` the run follows
`s_0, s_1, …, s_{k-1}` reading `a_1 ⋯ a_{k-1}`. -/
theorem chainM (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepMn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 4) {u : ℕ} (hu : u ≤ L) (hfu : f u = 0) :
    ∀ j, j ≤ k - 1 → u + j ≤ L ∧ f (u + j) = j ∧ ∀ i, i < j → x (u + i) = Ltr.a (i + 1) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨by simpa using hu, by simpa using hfu, by omega⟩
  | succ j ih =>
    intro hj
    obtain ⟨hle, hfj, hx⟩ := ih (by omega)
    obtain ⟨h1, h2, h3⟩ := stepMn_chain hk hrun hL (i := j) (by omega) hle hfj
    refine ⟨by omega, by rw [show u + (j + 1) = u + j + 1 by ring]; exact h3, ?_⟩
    intro i hi
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
    · exact hx i h
    · subst h; exact h2

/-- From `s_{k-1}` the run either takes the `a_k`-edge into `A`, or the `d`-edge into
`t_1`, in which case it terminates two steps later. -/
theorem stepMn_at_last (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepMn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 4) {u : ℕ} (hu : u ≤ L) (hfu : f u = k - 1) :
    (x u = Ltr.a k ∧ f (u + 1) = k) ∨
      (x u = Ltr.d ∧ x (u + 1) = Ltr.e ∧ u + 2 = L) := by
  have hlt : u < L := lt_of_ne_final hL hu (by omega)
  have h := hrun u hlt
  rw [hfu] at h
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact absurd h1 (by omega)
  · exact Or.inl ⟨h2, h3⟩
  · right
    have hlt1 : u + 1 < L := lt_of_ne_final hL (by omega) (by rw [h3]; omega)
    have h' := hrun (u + 1) hlt1
    rw [h3] at h'
    have he : x (u + 1) = Ltr.e ∧ f (u + 2) = k + 4 := by
      rcases h' with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ |
        ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
      · exact absurd g1 (by omega)
      · exact absurd g1 (by omega)
      · exact absurd g1 (by omega)
      · exact ⟨g2, g3⟩
      all_goals exact absurd g1 (by omega)
    refine ⟨h2, he.1, ?_⟩
    by_contra hcon
    have hlt2 : u + 2 < L := by omega
    have h'' := hrun (u + 2) hlt2
    rw [he.2] at h''
    rcases h'' with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ |
      ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;> exact absurd g1 (by omega)
  all_goals exact absurd h1 (by omega)

/-- From the state `B` the run stays in `B` for a while and then takes the `b`-edge to `A`. -/
theorem gadgetM_B (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepMn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 4) : ∀ N v, L - v ≤ N → v ≤ L → f v = k + 2 →
      ∃ j, v + j + 1 ≤ L ∧ (∀ i, i ≤ j → x (v + i) = Ltr.b) ∧ f (v + j) = k + 2 ∧
        f (v + j + 1) = k := by
  intro N
  induction N with
  | zero =>
    intro v hNv hv hfv
    exact absurd (show f L = k + 2 by rw [show L = v by omega]; exact hfv) (by omega)
  | succ N ih =>
    intro v hNv hv hfv
    have hlt : v < L := lt_of_ne_final hL hv (by omega)
    have h := hrun v hlt
    rw [hfv] at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact ⟨0, by omega, by intro i hi; simpa [show i = 0 by omega] using h2,
        by simpa using hfv, by simpa using h3⟩
    · obtain ⟨j, hj1, hj2, hj3, hj4⟩ := ih (v + 1) (by omega) (by omega) h3
      refine ⟨j + 1, by omega, ?_, ?_, ?_⟩
      · intro i hi
        rcases Nat.eq_zero_or_pos i with h' | h'
        · subst h'; simpa using h2
        · have := hj2 (i - 1) (by omega)
          rw [show v + 1 + (i - 1) = v + i by omega] at this
          exact this
      · rw [show v + (j + 1) = v + 1 + j by ring]; exact hj3
      · rw [show v + (j + 1) + 1 = v + 1 + j + 1 by ring]; exact hj4
    · exact absurd h1 (by omega)

/-- **Lemma 3.1 (`lem:gadgetT`)**, run form.  From a visit of `X` the run reads a block
of `t'` letters `b` with `t' = 0` or `t' ≥ 3`, returns to `X`, and then takes the
`c`-edge back to `s_0`. -/
theorem gadgetM_X (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepMn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 4) : ∀ N u, L - u ≤ N → u ≤ L → f u = k + 1 →
      ∃ t, (t = 0 ∨ 3 ≤ t) ∧ u + t + 1 ≤ L ∧ (∀ i, i < t → x (u + i) = Ltr.b) ∧
        f (u + t) = k + 1 ∧ x (u + t) = Ltr.c ∧ f (u + t + 1) = 0 := by
  intro N
  induction N with
  | zero =>
    intro u hNu hu hfu
    exact absurd (show f L = k + 1 by rw [show L = u by omega]; exact hfu) (by omega)
  | succ N ih =>
    intro u hNu hu hfu
    have hlt : u < L := lt_of_ne_final hL hu (by omega)
    have h := hrun u hlt
    rw [hfu] at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · -- `X → B`
      obtain ⟨j, hj1, hj2, hj3, hj4⟩ := gadgetM_B hk hrun hL (L - (u + 1)) (u + 1) le_rfl
        (by omega) h3
      have hA : f (u + j + 2) = k := by
        rw [show u + j + 2 = u + 1 + j + 1 by ring]; exact hj4
      have hAlt : u + j + 2 < L := lt_of_ne_final hL (by omega) (by rw [hA]; omega)
      have hstepA := hrun (u + j + 2) hAlt
      rw [hA] at hstepA
      have hAb : x (u + j + 2) = Ltr.b ∧ f (u + j + 3) = k + 1 := by
        rcases hstepA with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ |
          ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
        · exact absurd g1 (by omega)
        · exact absurd g1 (by omega)
        · exact absurd g1 (by omega)
        · exact absurd g1 (by omega)
        · exact ⟨g2, g3⟩
        all_goals exact absurd g1 (by omega)
      obtain ⟨t, ht0, ht1, ht2, ht3, ht4, ht5⟩ :=
        ih (u + j + 3) (by omega) (by omega) hAb.2
      refine ⟨j + 3 + t, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rcases Nat.lt_or_ge i (j + 3) with h' | h'
        · rcases Nat.eq_zero_or_pos i with h'' | h''
          · subst h''; simpa using h2
          · rcases Nat.lt_or_ge i (j + 2) with h3' | h3'
            · have := hj2 (i - 1) (by omega)
              rw [show u + 1 + (i - 1) = u + i by omega] at this
              exact this
            · have hij : i = j + 2 := by omega
              subst hij
              rw [show u + (j + 2) = u + j + 2 by ring]
              exact hAb.1
        · have := ht2 (i - (j + 3)) (by omega)
          rw [show u + j + 3 + (i - (j + 3)) = u + i by omega] at this
          exact this
      · rw [show u + (j + 3 + t) = u + j + 3 + t by ring]; exact ht3
      · rw [show u + (j + 3 + t) = u + j + 3 + t by ring]; exact ht4
      · rw [show u + (j + 3 + t) + 1 = u + j + 3 + t + 1 by ring]; exact ht5
    · exact absurd h1 (by omega)
    · exact absurd h1 (by omega)
    · exact ⟨0, Or.inl rfl, by omega, by omega, by simpa using hfu, by simpa using h2,
        by simpa using h3⟩

/-- **Block decomposition** (the shape analysis in the proof of Proposition 3.2,
`prop:upper-exact`).  From a visit of `s_0` at time `u`, the run either finishes with
`a_1⋯a_{k-1} d e` (case A), or completes a block `a_1⋯a_k b^t c` with `t ∈ T = {1} ∪ [4,∞)`
and returns to `s_0` (case B). -/
theorem blockM (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepMn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 4) {u : ℕ} (hu : u ≤ L) (hfu : f u = 0) :
    (L = u + (k + 1) ∧ (∀ j, j < k - 1 → x (u + j) = Ltr.a (j + 1)) ∧
        x (u + (k - 1)) = Ltr.d ∧ x (u + k) = Ltr.e) ∨
    (∃ t, (t = 1 ∨ 4 ≤ t) ∧ u + (k + 1 + t) ≤ L ∧
        (∀ j, j < k → x (u + j) = Ltr.a (j + 1)) ∧
        (∀ j, j < t → x (u + k + j) = Ltr.b) ∧
        x (u + k + t) = Ltr.c ∧ f (u + (k + 1 + t)) = 0) := by
  obtain ⟨hle, hfk, hxs⟩ := chainM hk hrun hL hu hfu (k - 1) le_rfl
  rcases stepMn_at_last hk hrun hL hle hfk with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · right
    have hlt' : u + (k - 1) < L := lt_of_ne_final hL hle (by rw [hfk]; omega)
    have hA : f (u + k) = k := by
      rw [show u + k = u + (k - 1) + 1 by omega]; exact h2
    have hAlt : u + k < L := lt_of_ne_final hL (by omega) (by rw [hA]; omega)
    have hstepA := hrun (u + k) hAlt
    rw [hA] at hstepA
    have hAb : x (u + k) = Ltr.b ∧ f (u + k + 1) = k + 1 := by
      rcases hstepA with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ |
        ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
      · exact absurd g1 (by omega)
      · exact absurd g1 (by omega)
      · exact absurd g1 (by omega)
      · exact absurd g1 (by omega)
      · exact ⟨g2, g3⟩
      all_goals exact absurd g1 (by omega)
    obtain ⟨t', ht0, ht1, ht2, ht3, ht4, ht5⟩ :=
      gadgetM_X hk hrun hL (L - (u + k + 1)) (u + k + 1) le_rfl (by omega) hAb.2
    refine ⟨t' + 1, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_or_ge j (k - 1) with h' | h'
      · exact hxs j h'
      · have hjk : j = k - 1 := by omega
        subst hjk
        rw [show k - 1 + 1 = k by omega]
        exact h1
    · intro j hj
      rcases Nat.eq_zero_or_pos j with h' | h'
      · subst h'; simpa using hAb.1
      · have := ht2 (j - 1) (by omega)
        rw [show u + k + 1 + (j - 1) = u + k + j by omega] at this
        exact this
    · rw [show u + k + (t' + 1) = u + k + 1 + t' by ring]; exact ht4
    · rw [show u + (k + 1 + (t' + 1)) = u + k + 1 + t' + 1 by ring]; exact ht5
  · left
    refine ⟨by omega, hxs, h1, ?_⟩
    rw [show u + k = u + (k - 1) + 1 by omega]; exact h2

/-- Any run of `M_k` from `s_0` to `t_2` has length at least `k+1`. -/
theorem blockM_len (hk : 3 ≤ k) (hrun : ∀ t, t < L → stepMn k (f t) (x t) (f (t + 1)))
    (hL : f L = k + 4) {u : ℕ} (hu : u ≤ L) (hfu : f u = 0) : u + (k + 1) ≤ L := by
  rcases blockM hk hrun hL hu hfu with ⟨h, _⟩ | ⟨t, ht0, ht1, _⟩
  · omega
  · omega

end Structure

/-- **Proposition 3.2 (`prop:upper-exact`)**, the hard direction:
every accepting run of `M_k` of length `n = 3k+7` spells `z_k`. -/
theorem stepMn_exact {k : ℕ} (hk : 3 ≤ k) {x : ℕ → Ltr} {f : ℕ → ℕ}
    (hrun : ∀ t, t < wlen k → stepMn k (f t) (x t) (f (t + 1)))
    (h0 : f 0 = 0) (hL : f (wlen k) = k + 4) :
    ∀ t, t < wlen k → x t = zw k t := by
  have hLval : wlen k = 3 * k + 7 := rfl
  rcases blockM hk hrun hL (by omega) h0 with ⟨h, _⟩ | ⟨t₁, ht₁0, ht₁1, ht₁2, ht₁3, ht₁4, ht₁5⟩
  · exact absurd h (by omega)
  rcases blockM hk hrun hL (u := 0 + (k + 1 + t₁)) (by omega) ht₁5 with
    ⟨h, hA1, hA2, hA3⟩ | ⟨t₂, ht₂0, ht₂1, ht₂2, ht₂3, ht₂4, ht₂5⟩
  · have ht₁ : t₁ = k + 5 := by omega
    subst ht₁
    simp only [zero_add] at ht₁2 ht₁3 ht₁4 hA1 hA2 hA3
    intro s hs
    rw [hLval] at hs
    rcases Nat.lt_or_ge s k with h1 | h1
    · rw [ht₁2 s h1]
      simp only [zw, if_pos h1]
    · rcases Nat.lt_or_ge s (2 * k + 5) with h2 | h2
      · have hb := ht₁3 (s - k) (by omega)
        rw [show k + (s - k) = s by omega] at hb
        rw [hb]
        simp only [zw, if_neg (by omega : ¬ s < k), if_pos h2]
      · rcases eq_or_lt_of_le h2 with h3 | h3
        · rw [← h3, show (2 * k + 5 : ℕ) = k + (k + 5) by ring, ht₁4]
          simp only [zw, if_neg (by omega : ¬ (k + (k + 5) : ℕ) < k),
            if_neg (by omega : ¬ (k + (k + 5) : ℕ) < 2 * k + 5),
            if_pos (by omega : (k + (k + 5) : ℕ) = 2 * k + 5)]
        · rcases Nat.lt_or_ge s (3 * k + 5) with h4 | h4
          · have hc := hA1 (s - (k + 1 + (k + 5))) (by omega)
            rw [show k + 1 + (k + 5) + (s - (k + 1 + (k + 5))) = s by omega] at hc
            rw [hc]
            simp only [zw, if_neg (by omega : ¬ s < k), if_neg (by omega : ¬ s < 2 * k + 5),
              if_neg (by omega : ¬ s = 2 * k + 5), if_pos h4]
            congr 1
            omega
          · rcases eq_or_lt_of_le h4 with h5 | h5
            · rw [← h5, show (3 * k + 5 : ℕ) = k + 1 + (k + 5) + (k - 1) by omega, hA2]
              simp only [zw, if_neg (by omega : ¬ (k + 1 + (k + 5) + (k - 1) : ℕ) < k),
                if_neg (by omega : ¬ (k + 1 + (k + 5) + (k - 1) : ℕ) < 2 * k + 5),
                if_neg (by omega : ¬ (k + 1 + (k + 5) + (k - 1) : ℕ) = 2 * k + 5),
                if_neg (by omega : ¬ (k + 1 + (k + 5) + (k - 1) : ℕ) < 3 * k + 5),
                if_pos (by omega : (k + 1 + (k + 5) + (k - 1) : ℕ) = 3 * k + 5)]
            · have hs6 : s = 3 * k + 6 := by omega
              subst hs6
              rw [show (3 * k + 6 : ℕ) = k + 1 + (k + 5) + k by omega, hA3]
              simp only [zw, if_neg (by omega : ¬ (k + 1 + (k + 5) + k : ℕ) < k),
                if_neg (by omega : ¬ (k + 1 + (k + 5) + k : ℕ) < 2 * k + 5),
                if_neg (by omega : ¬ (k + 1 + (k + 5) + k : ℕ) = 2 * k + 5),
                if_neg (by omega : ¬ (k + 1 + (k + 5) + k : ℕ) < 3 * k + 5),
                if_neg (by omega : ¬ (k + 1 + (k + 5) + k : ℕ) = 3 * k + 5)]
  · exfalso
    rcases blockM hk hrun hL (u := 0 + (k + 1 + t₁) + (k + 1 + t₂)) ht₂1 ht₂5 with
      ⟨h, _⟩ | ⟨t₃, ht₃0, ht₃1, _, _, _, ht₃5⟩
    · rcases ht₁0 with h' | h' <;> rcases ht₂0 with h'' | h'' <;> omega
    · have h4 := blockM_len hk hrun hL
        (u := 0 + (k + 1 + t₁) + (k + 1 + t₂) + (k + 1 + t₃)) ht₃1 ht₃5
      omega

/-- The accepting path of `M_k` on `z_k` used in the proof of Proposition 3.2
(`prop:upper-exact`): it rides the chain `s_0 ⋯ s_{k-1}`, goes to `A`, then takes the
`b`-path `A X B^{k+2} A X` of length `m = k+5`, the `c`-edge back to `s_0`, the chain
again, and finally `d`, `e`. -/
def canM (k t : ℕ) : ℕ :=
  if t < k then t
  else if t = k then k
  else if t = k + 1 then k + 1
  else if t ≤ 2 * k + 3 then k + 2
  else if t = 2 * k + 4 then k
  else if t = 2 * k + 5 then k + 1
  else if t ≤ 3 * k + 5 then t - (2 * k + 6)
  else if t = 3 * k + 6 then k + 3
  else k + 4

theorem canM_lt (k t : ℕ) : canM k t < k + 5 := by
  unfold canM; split_ifs <;> omega

theorem canM_zero {k : ℕ} (hk : 3 ≤ k) : canM k 0 = 0 := by
  unfold canM; split_ifs <;> omega

theorem canM_end {k : ℕ} (hk : 3 ≤ k) : canM k (wlen k) = k + 4 := by
  show canM k (3 * k + 7) = k + 4
  unfold canM; split_ifs <;> omega

/-- The canonical path is indeed a path of `M_k` spelling `z_k`
(the first half of Proposition 3.2, `prop:upper-exact`). -/
theorem canM_isRun {k : ℕ} (hk : 3 ≤ k) :
    ∀ t, t < wlen k → stepMn k (canM k t) (zw k t) (canM k (t + 1)) := by
  intro t ht
  have ht' : t < 3 * k + 7 := ht
  have hcase : t + 1 < k ∨ t + 1 = k ∨ t = k ∨ t = k + 1 ∨ (k + 2 ≤ t ∧ t ≤ 2 * k + 2) ∨
      t = 2 * k + 3 ∨ t = 2 * k + 4 ∨ t = 2 * k + 5 ∨ (2 * k + 6 ≤ t ∧ t ≤ 3 * k + 4) ∨
      t = 3 * k + 5 ∨ t = 3 * k + 6 := by omega
  rcases hcase with h | h | h | h | ⟨h1, h2⟩ | h | h | h | ⟨h1, h2⟩ | h | h
  · rw [show canM k t = t by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = t + 1 by unfold canM; rw [if_pos (show t + 1 < k by omega)],
      zw_a (by omega)]
    exact Or.inl ⟨by omega, rfl, rfl⟩
  · rw [show canM k t = t by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = k by unfold canM; split_ifs <;> omega,
      zw_a (by omega)]
    exact Or.inr (Or.inl ⟨by omega, by rw [h], rfl⟩)
  · rw [show canM k t = k by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = k + 1 by unfold canM; split_ifs <;> omega,
      zw_b (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
  · rw [show canM k t = k + 1 by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = k + 2 by unfold canM; split_ifs <;> omega,
      zw_b (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))
  · rw [show canM k t = k + 2 by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = k + 2 by unfold canM; split_ifs <;> omega,
      zw_b (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))))
  · rw [show canM k t = k + 2 by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = k by unfold canM; split_ifs <;> omega,
      zw_b (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))
  · rw [show canM k t = k by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = k + 1 by unfold canM; split_ifs <;> omega,
      zw_b (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
  · rw [show canM k t = k + 1 by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = 0 by unfold canM; split_ifs <;> omega, zw_c h]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))))
  · rw [show canM k t = t - (2 * k + 6) by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = t - (2 * k + 6) + 1 by unfold canM; split_ifs <;> omega,
      zw_a' (by omega) (by omega)]
    refine Or.inl ⟨by omega, ?_, rfl⟩
    congr 1
    omega
  · rw [show canM k t = k - 1 by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = k + 3 by unfold canM; split_ifs <;> omega, zw_d (by omega) h]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · rw [show canM k t = k + 3 by unfold canM; split_ifs <;> omega,
      show canM k (t + 1) = k + 4 by unfold canM; split_ifs <;> omega, zw_e h]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))

/-- **Proposition 3.2 (`prop:upper-exact`)**: `M_k` exactly accepts `z_k`, hence
`A_{Ne}(z_k) ≤ k+5`. -/
theorem ANe_upper {k : ℕ} (hk : 3 ≤ k) : ANe (wlen k) (zw k) ≤ k + 5 := by
  refine ANe_le (q := k + 5) ⟨fun p α q => stepMn k p.val α q.val, ⟨0, by omega⟩,
    fun q => q.val = k + 4, ⟨⟨fun t => ⟨canM k t, canM_lt k t⟩, ?_, ?_, ?_⟩, ?_⟩⟩
  · exact Fin.ext (by simpa using canM_zero hk)
  · exact canM_end hk
  · intro t ht; exact canM_isRun hk t ht
  · intro x p hp t ht
    exact stepMn_exact hk (fun s hs => hp.2.2 s hs) (by rw [hp.1]) hp.2.1 t ht

end AneVsAn
