import RequestProject.GenericSegments

/-! # Word-independent surgeries on uniquely accepting walks -/

namespace AneVsAn.Generic

set_option autoImplicit false

variable {n : ℕ} {Λ S : Type} {c : ℕ → S} {x : ℕ → Λ}

theorem rotation (huaw : IsUAWalk x n c)
    {i p δ : ℕ} (hip : i < p) (hδ : 1 ≤ δ) (hpn : p + δ ≤ n)
    (h1 : c i = c (i + δ)) (h2 : c p = c (p + δ)) :
    (∀ t, i ≤ t → t < p → x t = x (t + δ)) ∧
      (∀ t, i ≤ t → t ≤ p → c t = c (t + δ)) := by
  have hnil := pathTo_nil n c (fun _ => 0)
  have hs3 := pathTo_cons (a := p) (b := n) (by omega) (by omega) hnil
  rw [h2] at hs3
  have hs2 := pathTo_cons (a := i + δ) (b := p + δ) (by omega) (by omega) hs3
  rw [← h1] at hs2
  have hs1 := pathTo_cons (a := 0) (b := i) (by omega) (by omega) hs2
  rw [show 0 + (n - p) + (p + δ - (i + δ)) + (i - 0) = n by omega] at hs1
  obtain ⟨hz, hcc⟩ := pathTo_spec huaw hs1
  have hτ : ∀ t, i ≤ t → t < p →
      segcat 0 i (segcat (i + δ) (p + δ) (segcat p (n) (fun _ => 0))) t = t + δ := by
    intro t hti htp
    rw [segcat_ge (by omega), segcat_lt (by omega)]
    omega
  refine ⟨fun t hti htp => ?_, fun t hti htp => ?_⟩
  · have := hz t (by omega)
    rw [hτ t hti htp] at this
    exact this.symm
  · rcases eq_or_lt_of_le htp with rfl | htp'
    · exact h2
    · have := hcc t (by omega)
      rw [hτ t hti htp'] at this
      exact this.symm


theorem exchange (huaw : IsUAWalk x n c)
    {t₁ t₂ t₃ : ℕ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h3n : t₃ ≤ n)
    (e1 : c t₁ = c t₂) (e2 : c t₂ = c t₃) :
    (∀ u, u < t₃ - t₂ → x (t₂ + u) = x (t₁ + u) ∧ c (t₂ + u) = c (t₁ + u)) ∧
      (∀ v, v < t₂ - t₁ → x (t₁ + v) = x (t₁ + (t₃ - t₂) + v) ∧
        c (t₁ + v) = c (t₁ + (t₃ - t₂) + v)) := by
  have hnil := pathTo_nil n c (fun _ => 0)
  have hs4 := pathTo_cons (a := t₃) (b := n) (by omega) (by omega) hnil
  rw [← e2] at hs4
  have hs3 := pathTo_cons (a := t₁) (b := t₂) (by omega) (by omega) hs4
  rw [e1, e2] at hs3
  have hs2 := pathTo_cons (a := t₂) (b := t₃) (by omega) (by omega) hs3
  rw [← e1] at hs2
  have hs1 := pathTo_cons (a := 0) (b := t₁) (by omega) (by omega) hs2
  rw [show 0 + (n - t₃) + (t₂ - t₁) + (t₃ - t₂) + (t₁ - 0) = n by omega] at hs1
  obtain ⟨hz, hcc⟩ := pathTo_spec huaw hs1
  set τ := segcat 0 t₁ (segcat t₂ t₃ (segcat t₁ t₂ (segcat t₃ (n) (fun _ => 0)))) with hτdef
  have hA : ∀ u, u < t₃ - t₂ → τ (t₁ + u) = t₂ + u := by
    intro u hu
    rw [hτdef, segcat_ge (by omega), segcat_lt (by omega)]
    omega
  have hB : ∀ v, v < t₂ - t₁ → τ (t₁ + (t₃ - t₂) + v) = t₁ + v := by
    intro v hv
    rw [hτdef, segcat_ge (by omega), segcat_ge (by omega), segcat_lt (by omega)]
    omega
  refine ⟨fun u hu => ?_, fun v hv => ?_⟩
  · have h1 := hz (t₁ + u) (by omega)
    have h2 := hcc (t₁ + u) (by omega)
    rw [hA u hu] at h1 h2
    exact ⟨h1, h2⟩
  · have h1 := hz (t₁ + (t₃ - t₂) + v) (by omega)
    have h2 := hcc (t₁ + (t₃ - t₂) + v) (by omega)
    rw [hB v hv] at h1 h2
    exact ⟨h1, h2⟩


theorem twovisit_period (huaw : IsUAWalk x n c)
    {t₁ t₂ t₃ : ℕ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h3n : t₃ ≤ n)
    (e1 : c t₁ = c t₂) (e2 : c t₂ = c t₃) :
    ∃ q, 1 ≤ q ∧ q ≤ t₂ - t₁ ∧ q ≤ t₃ - t₂ ∧
      ∀ t, t₁ ≤ t → t < t₃ - q → x t = x (t + q) ∧ c t = c (t + q) := by
  obtain ⟨hA, hB⟩ := exchange huaw h12 h23 h3n e1 e2
  rcases (by omega : t₂ - t₁ ≤ t₃ - t₂ ∨ t₃ - t₂ < t₂ - t₁) with hle | hlt
  · refine ⟨t₂ - t₁, by omega, le_rfl, hle, ?_⟩
    intro t hx1 hx2
    obtain ⟨u, rfl⟩ : ∃ u, t = t₁ + u := ⟨t - t₁, by omega⟩
    obtain ⟨p1, p2⟩ := hA u (by omega)
    rw [show t₁ + u + (t₂ - t₁) = t₂ + u by omega]
    exact ⟨p1.symm, p2.symm⟩
  · refine ⟨t₃ - t₂, by omega, by omega, le_rfl, ?_⟩
    intro t hx1 hx2
    obtain ⟨v, rfl⟩ : ∃ v, t = t₁ + v := ⟨t - t₁, by omega⟩
    obtain ⟨p1, p2⟩ := hB v (by omega)
    rw [show t₁ + v + (t₃ - t₂) = t₁ + (t₃ - t₂) + v by omega]
    exact ⟨p1, p2⟩


theorem equal_gaps (huaw : IsUAWalk x n c)
    {t₁ t₂ t₃ : ℕ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h3n : t₃ ≤ n)
    (e1 : c t₁ = c t₂) (e2 : c t₂ = c t₃)
    (hmid1 : ∀ u, t₁ < u → u < t₂ → c u ≠ c t₁)
    (hmid2 : ∀ u, t₂ < u → u < t₃ → c u ≠ c t₂) :
    t₂ - t₁ = t₃ - t₂ := by
  obtain ⟨hA, hB⟩ := exchange huaw h12 h23 h3n e1 e2
  by_contra hne
  rcases Nat.lt_or_ge (t₃ - t₂) (t₂ - t₁) with hlt | hge
  · have hh := (hB 0 (by omega)).2
    rw [Nat.add_zero, Nat.add_zero] at hh
    exact hmid1 (t₁ + (t₃ - t₂)) (by omega) (by omega) hh.symm
  · have hh := (hA (t₂ - t₁) (by omega)).2
    rw [show t₁ + (t₂ - t₁) = t₂ by omega] at hh
    exact hmid2 (t₂ + (t₂ - t₁)) (by omega) (by omega) hh


theorem crossing (huaw : IsUAWalk x n c)
    {a₁ b₁ a₂ b₂ : ℕ} (h1 : a₁ < b₁) (h2 : b₁ < a₂) (h3 : a₂ < b₂) (h4 : b₂ ≤ n)
    (ea : c a₁ = c a₂) (eb : c b₁ = c b₂) :
    x a₂ = x a₁ ∧ x (b₁ - 1) = x (b₂ - 1) := by
  have hnil := pathTo_nil n c (fun _ => 0)
  have hs5 := pathTo_cons (a := b₂) (b := n) (by omega) (by omega) hnil
  rw [← eb] at hs5
  have hs4 := pathTo_cons (a := a₁) (b := b₁) (by omega) (by omega) hs5
  rw [ea] at hs4
  have hs3 := pathTo_cons (a := b₁) (b := a₂) (by omega) (by omega) hs4
  rw [eb] at hs3
  have hs2 := pathTo_cons (a := a₂) (b := b₂) (by omega) (by omega) hs3
  rw [← ea] at hs2
  have hs1 := pathTo_cons (a := 0) (b := a₁) (by omega) (by omega) hs2
  rw [show 0 + (n - b₂) + (b₁ - a₁) + (a₂ - b₁) + (b₂ - a₂) + (a₁ - 0) = n
    by omega] at hs1
  obtain ⟨hz, _⟩ := pathTo_spec huaw hs1
  set τ := segcat 0 a₁ (segcat a₂ b₂ (segcat b₁ a₂ (segcat a₁ b₁
    (segcat b₂ (n) (fun _ => 0))))) with hτdef
  have hfirst : τ a₁ = a₂ := by
    rw [hτdef, segcat_ge (by omega), segcat_lt (by omega)]
    omega
  have hlast : τ (b₂ - 1) = b₁ - 1 := by
    rw [hτdef, segcat_ge (by omega), segcat_ge (by omega), segcat_ge (by omega),
      segcat_lt (by omega)]
    omega
  constructor
  · have := hz a₁ (by omega)
    rwa [hfirst] at this
  · have := hz (b₂ - 1) (by omega)
    rwa [hlast] at this


/-- The complete crossing surgery, including its interior positions. -/
theorem crossing_itinerary
    {a₁ b₁ a₂ b₂ : ℕ} (h1 : a₁ < b₁) (h2 : b₁ < a₂) (h3 : a₂ < b₂) (h4 : b₂ ≤ n)
    (ea : c a₁ = c a₂) (eb : c b₁ = c b₂) :
    PathTo n c (c 0) n (segcat 0 a₁ (segcat a₂ b₂ (segcat b₁ a₂
      (segcat a₁ b₁ (segcat b₂ n (fun _ => 0)))))) := by
  have hnil := pathTo_nil n c (fun _ => 0)
  have hs5 := pathTo_cons (a := b₂) (b := n) (by omega) (by omega) hnil
  rw [← eb] at hs5
  have hs4 := pathTo_cons (a := a₁) (b := b₁) (by omega) (by omega) hs5
  rw [ea] at hs4
  have hs3 := pathTo_cons (a := b₁) (b := a₂) (by omega) (by omega) hs4
  rw [eb] at hs3
  have hs2 := pathTo_cons (a := a₂) (b := b₂) (by omega) (by omega) hs3
  rw [← ea] at hs2
  have hs1 := pathTo_cons (a := 0) (b := a₁) (by omega) (by omega) hs2
  rwa [show 0 + (n - b₂) + (b₁ - a₁) + (a₂ - b₁) + (b₂ - a₂) + (a₁ - 0) = n
    by omega] at hs1

/-- Crossing chords identify the entire first and last blocks after swapping. -/
theorem crossing_edges (huaw : IsUAWalk x n c)
    {a₁ b₁ a₂ b₂ : ℕ} (h1 : a₁ < b₁) (h2 : b₁ < a₂) (h3 : a₂ < b₂) (h4 : b₂ ≤ n)
    (ea : c a₁ = c a₂) (eb : c b₁ = c b₂) :
    (∀ j, j < b₂ - a₂ → edge x c (a₂ + j) = edge x c (a₁ + j)) ∧
    (∀ j, j < b₁ - a₁ → edge x c (a₁ + j) = edge x c (b₂ - (b₁ - a₁) + j)) := by
  have hpath := crossing_itinerary h1 h2 h3 h4 ea eb
  constructor
  · intro j hj
    have heq := pathTo_edge huaw hpath (a₁ + j) (by omega)
    rw [segcat_ge (by omega), segcat_lt (by omega),
      show a₁ + j - (a₁ - 0) = j by omega] at heq
    exact heq
  · intro j hj
    have heq := pathTo_edge huaw hpath (b₂ - (b₁ - a₁) + j) (by omega)
    rw [segcat_ge (by omega), segcat_ge (by omega), segcat_ge (by omega),
      segcat_lt (by omega)] at heq
    convert heq using 2; omega

/-- If one endpoint state of two crossing chords has only its two indicated visits,
the two outside blocks must have the same length. -/
theorem crossing_equal_lengths (huaw : IsUAWalk x n c)
    {a₁ b₁ a₂ b₂ : ℕ} (h1 : a₁ < b₁) (h2 : b₁ < a₂) (h3 : a₂ < b₂) (h4 : b₂ ≤ n)
    (ea : c a₁ = c a₂) (eb : c b₁ = c b₂)
    (hvis : ∀ t, t ≤ n → c t = c b₁ → t = b₁ ∨ t = b₂) :
    b₁ - a₁ = b₂ - a₂ := by
  have hpath := crossing_itinerary h1 h2 h3 h4 ea eb
  have hcc := (pathTo_spec huaw hpath).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have heq := hcc b₁ (by omega)
    rw [segcat_ge (by omega), segcat_lt (by omega)] at heq
    have hv := hvis (a₂ + (b₁ - (a₁ - 0))) (by omega) heq
    omega
  · have heq := hcc (a₁ + (b₂ - a₂)) (by omega)
    rw [segcat_ge (by omega), segcat_ge (by omega), segcat_lt (by omega)] at heq
    have hh : c b₁ = c (a₁ + (b₂ - a₂)) := by
      convert heq using 1; congr 1; omega
    have hv := hvis (a₁ + (b₂ - a₂)) (by omega) hh.symm
    omega

end AneVsAn.Generic
