import RequestProject.Seg

/-!
# Master tools for the lower bound (Section 4 of `anevsanseparationv4.tex`)

Throughout, `c₀,…,c_n` is a uniquely accepting walk for `z = z_k`, `n = 3k+7`.

Every edge of the walk graph is `e_t = (c_t, z_t, c_{t+1})` for some `t < n`, so a path of
length `n` in the walk graph is described by an *itinerary*: a sequence `τ 0,…,τ (n-1)` of
edge indices whose endpoints match.  This gives a uniform way of performing the surgeries
of the paper: `Lemma 4.1` (Splicing, `lem:splice`), `Lemma 4.2` (Rotation, `lem:rotation`),
`Lemma 4.7` (Crossing, `lem:cross`) and all the ad-hoc surgeries of Sections 5 and 6 are
instances of "build an itinerary and read off one position".
-/

namespace AneVsAn

set_option autoImplicit false

/-- The letter of `z_k` at a position `u < n`, together with the range of `u`
(Section 2, `sec:prelim`, "We record the position structure of `z_k`"). -/
theorem zw_class {k : ℕ} (hk : 3 ≤ k) {u : ℕ} (hu : u < 3 * k + 7) :
    (u < k ∧ zw k u = Ltr.a (u + 1)) ∨
    ((k ≤ u ∧ u < 2 * k + 5) ∧ zw k u = Ltr.b) ∨
    (u = 2 * k + 5 ∧ zw k u = Ltr.c) ∨
    ((2 * k + 6 ≤ u ∧ u < 3 * k + 5) ∧ zw k u = Ltr.a (u - (2 * k + 5))) ∨
    (u = 3 * k + 5 ∧ zw k u = Ltr.d) ∨
    (u = 3 * k + 6 ∧ zw k u = Ltr.e) := by
  rcases (by omega : u < k ∨ (k ≤ u ∧ u < 2 * k + 5) ∨ u = 2 * k + 5 ∨
      (2 * k + 6 ≤ u ∧ u < 3 * k + 5) ∨ u = 3 * k + 5 ∨ u = 3 * k + 6) with
    h | h | h | h | h | h
  · exact Or.inl ⟨h, zw_a h⟩
  · exact Or.inr (Or.inl ⟨h, zw_b h.1 h.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, zw_c h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, zw_a' h.1 h.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, zw_d (by omega) h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, zw_e h⟩))))

/-- The letter `b` occupies exactly the positions `[k, 2k+4]` of `z_k`. -/
theorem zw_b_range {k : ℕ} (hk : 3 ≤ k) {u : ℕ} (hu : u < 3 * k + 7) (h : zw k u = Ltr.b) :
    k ≤ u ∧ u < 2 * k + 5 := by
  rcases zw_class hk hu with ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩
  · exact absurd (p2 ▸ h) (by simp)
  · exact p1
  · exact absurd (p2 ▸ h) (by simp)
  · exact absurd (p2 ▸ h) (by simp)
  · exact absurd (p2 ▸ h) (by simp)
  · exact absurd (p2 ▸ h) (by simp)

/-- **Lemma 4.3 (Pair table, `lem:pairs`)**.  Two positions of `z_k` carrying the same
letter, that letter not being `b`, are equal or are the two occurrences of some `a_i`
(`i ≤ k-1`), which are at distance `δ₀ = 2k+6`. -/
theorem zw_eq_pair {k : ℕ} (hk : 3 ≤ k) {s t : ℕ} (hs : s < 3 * k + 7) (ht : t < 3 * k + 7)
    (hb : zw k s ≠ Ltr.b) (heq : zw k s = zw k t) :
    s = t ∨ (t = s + (2 * k + 6) ∧ s + 1 < k) ∨ (s = t + (2 * k + 6) ∧ t + 1 < k) := by
  rcases zw_class hk hs with ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ <;>
    rcases zw_class hk ht with ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ | ⟨q1, q2⟩ <;>
    rw [p2, q2] at heq <;>
    first
      | exact absurd p2 hb
      | (simp only [Ltr.a.injEq] at heq; omega)
      | omega
      | exact absurd heq (by simp)

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-- **Lemma 4.2 (Rotation, `lem:rotation`)**.  If `c_i = c_{i+δ}` and `c_p = c_{p+δ}` with
`i < p`, then the walk is `δ`-periodic on `[i,p]`. -/
theorem rotation (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i p δ : ℕ} (hip : i < p) (hδ : 1 ≤ δ) (hpn : p + δ ≤ 3 * k + 7)
    (h1 : c i = c (i + δ)) (h2 : c p = c (p + δ)) :
    (∀ t, i ≤ t → t < p → zw k t = zw k (t + δ)) ∧
      (∀ t, i ≤ t → t ≤ p → c t = c (t + δ)) := by
  have hnil := pathTo_nil k c (fun _ => 0)
  have hs3 := pathTo_cons (a := p) (b := 3 * k + 7) (by omega) (by omega) hnil
  rw [h2] at hs3
  have hs2 := pathTo_cons (a := i + δ) (b := p + δ) (by omega) (by omega) hs3
  rw [← h1] at hs2
  have hs1 := pathTo_cons (a := 0) (b := i) (by omega) (by omega) hs2
  rw [show 0 + (3 * k + 7 - p) + (p + δ - (i + δ)) + (i - 0) = 3 * k + 7 by omega] at hs1
  obtain ⟨hz, hcc⟩ := pathTo_spec hk huaw hs1
  have hτ : ∀ t, i ≤ t → t < p →
      segcat 0 i (segcat (i + δ) (p + δ) (segcat p (3 * k + 7) (fun _ => 0))) t = t + δ := by
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

/-- The exchange surgery `W[0,t₁] W[t₂,t₃] W[t₁,t₂] W[t₃,n]` of the Two-visit Lemma 4.5
(`lem:twovisit`), for a state visited at the three times `t₁ < t₂ < t₃`. -/
theorem exchange (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {t₁ t₂ t₃ : ℕ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h3n : t₃ ≤ 3 * k + 7)
    (e1 : c t₁ = c t₂) (e2 : c t₂ = c t₃) :
    (∀ u, u < t₃ - t₂ → zw k (t₂ + u) = zw k (t₁ + u) ∧ c (t₂ + u) = c (t₁ + u)) ∧
      (∀ v, v < t₂ - t₁ → zw k (t₁ + v) = zw k (t₁ + (t₃ - t₂) + v) ∧
        c (t₁ + v) = c (t₁ + (t₃ - t₂) + v)) := by
  have hnil := pathTo_nil k c (fun _ => 0)
  have hs4 := pathTo_cons (a := t₃) (b := 3 * k + 7) (by omega) (by omega) hnil
  rw [← e2] at hs4
  have hs3 := pathTo_cons (a := t₁) (b := t₂) (by omega) (by omega) hs4
  rw [e1, e2] at hs3
  have hs2 := pathTo_cons (a := t₂) (b := t₃) (by omega) (by omega) hs3
  rw [← e1] at hs2
  have hs1 := pathTo_cons (a := 0) (b := t₁) (by omega) (by omega) hs2
  rw [show 0 + (3 * k + 7 - t₃) + (t₂ - t₁) + (t₃ - t₂) + (t₁ - 0) = 3 * k + 7 by omega] at hs1
  obtain ⟨hz, hcc⟩ := pathTo_spec hk huaw hs1
  set τ := segcat 0 t₁ (segcat t₂ t₃ (segcat t₁ t₂ (segcat t₃ (3 * k + 7) (fun _ => 0)))) with hτdef
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

/-- **Lemma 4.4 (Square structure of `z_k`, `lem:squarefree`)**, in positional form:
if `z_k` has a square of period `q ≥ 1` starting at position `t₀`, then the whole square
consists of the letter `b`. -/
theorem no_square {k q t₀ : ℕ} (hk : 3 ≤ k) (hq : 1 ≤ q) (hn : t₀ + 2 * q ≤ 3 * k + 7)
    (h : ∀ s, t₀ ≤ s → s < t₀ + q → zw k s = zw k (s + q)) :
    ∀ s, t₀ ≤ s → s < t₀ + 2 * q → zw k s = Ltr.b := by
  have hfirst : ∀ s, t₀ ≤ s → s < t₀ + q → zw k s = Ltr.b := by
    intro s hs1 hs2
    by_contra hb
    rcases zw_eq_pair hk (show s < 3 * k + 7 by omega) (show s + q < 3 * k + 7 by omega) hb
      (h s hs1 hs2) with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  intro s hs1 hs2
  rcases Nat.lt_or_ge s (t₀ + q) with hlt | hge
  · exact hfirst s hs1 hlt
  · have hh := h (s - q) (by omega) (by omega)
    rw [show s - q + q = s by omega] at hh
    rw [← hh]
    exact hfirst (s - q) (by omega) (by omega)

/-- The period extracted from three visits `t₁ < t₂ < t₃` of one state, in the proof of the
Two-visit Lemma 4.5 (`lem:twovisit`): the exchange surgery makes both `z_k` and the walk
`q`-periodic on `[t₁, t₃)`, where `q = min (t₂-t₁) (t₃-t₂)`. -/
theorem twovisit_period (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {t₁ t₂ t₃ : ℕ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h3n : t₃ ≤ 3 * k + 7)
    (e1 : c t₁ = c t₂) (e2 : c t₂ = c t₃) :
    ∃ q, 1 ≤ q ∧ q ≤ t₂ - t₁ ∧ q ≤ t₃ - t₂ ∧
      ∀ x, t₁ ≤ x → x < t₃ - q → zw k x = zw k (x + q) ∧ c x = c (x + q) := by
  obtain ⟨hA, hB⟩ := exchange hk huaw h12 h23 h3n e1 e2
  rcases (by omega : t₂ - t₁ ≤ t₃ - t₂ ∨ t₃ - t₂ < t₂ - t₁) with hle | hlt
  · refine ⟨t₂ - t₁, by omega, le_rfl, hle, ?_⟩
    intro x hx1 hx2
    obtain ⟨u, rfl⟩ : ∃ u, x = t₁ + u := ⟨x - t₁, by omega⟩
    obtain ⟨p1, p2⟩ := hA u (by omega)
    rw [show t₁ + u + (t₂ - t₁) = t₂ + u by omega]
    exact ⟨p1.symm, p2.symm⟩
  · refine ⟨t₃ - t₂, by omega, by omega, le_rfl, ?_⟩
    intro x hx1 hx2
    obtain ⟨v, rfl⟩ : ∃ v, x = t₁ + v := ⟨x - t₁, by omega⟩
    obtain ⟨p1, p2⟩ := hB v (by omega)
    rw [show t₁ + v + (t₃ - t₂) = t₁ + (t₃ - t₂) + v by omega]
    exact ⟨p1, p2⟩

/-- **Lemma 4.5 (Two-visit lemma, `lem:twovisit`)**: if a state of the walk is visited at
three times `t₁ < t₂ < t₃`, then every position of `z_k` in `[t₁, t₃)` carries the letter
`b`. -/
theorem twovisit_b (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {t₁ t₂ t₃ : ℕ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h3n : t₃ ≤ 3 * k + 7)
    (e1 : c t₁ = c t₂) (e2 : c t₂ = c t₃) :
    ∀ s, t₁ ≤ s → s < t₃ → zw k s = Ltr.b := by
  obtain ⟨q, hq1, hq2, hq3, hper⟩ := twovisit_period hk huaw h12 h23 h3n e1 e2
  have hsq : ∀ s, t₁ ≤ s → s < t₁ + 2 * q → zw k s = Ltr.b := by
    refine no_square hk hq1 (by omega) ?_
    intro s hs1 hs2
    exact (hper s hs1 (by omega)).1
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs1 hs3
    rcases Nat.lt_or_ge s (t₁ + 2 * q) with hlt | hge
    · exact hsq s hs1 hlt
    · have hh := (hper (s - q) (by omega) (by omega)).1
      rw [show s - q + q = s by omega] at hh
      rw [← hh]
      exact ih (s - q) (by omega) (by omega) (by omega)

/-- **Lemma 4.5 (Two-visit lemma, `lem:twovisit`)**: a state with three visits
`t₁ < t₂ < t₃` has all of them at run times, i.e. `[t₁,t₃] ⊆ [k, 2k+5]`. -/
theorem twovisit_run (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {t₁ t₂ t₃ : ℕ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h3n : t₃ ≤ 3 * k + 7)
    (e1 : c t₁ = c t₂) (e2 : c t₂ = c t₃) :
    k ≤ t₁ ∧ t₃ ≤ 2 * k + 5 := by
  have hb := twovisit_b hk huaw h12 h23 h3n e1 e2
  have h1 := zw_b_range hk (show t₁ < 3 * k + 7 by omega) (hb t₁ le_rfl (by omega))
  have h2 := zw_b_range hk (show t₃ - 1 < 3 * k + 7 by omega) (hb (t₃ - 1) (by omega) (by omega))
  omega

/-- Consecutive visits of a state are equally spaced: this is the form in which the
"common primitive closed edge-walk" statement of Lemma 4.5 (`lem:twovisit`) is used.  If
`t₁ < t₂ < t₃` are three visits of a state with no further visit of it strictly inside
`(t₁,t₂)` or `(t₂,t₃)`, then `t₂-t₁ = t₃-t₂`. -/
theorem equal_gaps (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {t₁ t₂ t₃ : ℕ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h3n : t₃ ≤ 3 * k + 7)
    (e1 : c t₁ = c t₂) (e2 : c t₂ = c t₃)
    (hmid1 : ∀ u, t₁ < u → u < t₂ → c u ≠ c t₁)
    (hmid2 : ∀ u, t₂ < u → u < t₃ → c u ≠ c t₂) :
    t₂ - t₁ = t₃ - t₂ := by
  obtain ⟨hA, hB⟩ := exchange hk huaw h12 h23 h3n e1 e2
  by_contra hne
  rcases Nat.lt_or_ge (t₃ - t₂) (t₂ - t₁) with hlt | hge
  · have hh := (hB 0 (by omega)).2
    rw [Nat.add_zero, Nat.add_zero] at hh
    exact hmid1 (t₁ + (t₃ - t₂)) (by omega) (by omega) hh.symm
  · have hh := (hA (t₂ - t₁) (by omega)).2
    rw [show t₁ + (t₂ - t₁) = t₂ by omega] at hh
    exact hmid2 (t₂ + (t₂ - t₁)) (by omega) (by omega) hh

/-- **Lemma 4.7 (Crossing lemma, `lem:cross`)**.  For crossing chords
`(α₁,α₂)` and `(β₁,β₂)`, `α₁ < β₁ < α₂ < β₂`, the surgery
`W[0,α₁] Z Y X W[β₂,n]` is a second accepting path unless
`z_{α₁} = z_{α₂}` and `z_{β₁-1} = z_{β₂-1}`. -/
theorem crossing (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {a₁ b₁ a₂ b₂ : ℕ} (h1 : a₁ < b₁) (h2 : b₁ < a₂) (h3 : a₂ < b₂) (h4 : b₂ ≤ 3 * k + 7)
    (ea : c a₁ = c a₂) (eb : c b₁ = c b₂) :
    zw k a₂ = zw k a₁ ∧ zw k (b₁ - 1) = zw k (b₂ - 1) := by
  have hnil := pathTo_nil k c (fun _ => 0)
  have hs5 := pathTo_cons (a := b₂) (b := 3 * k + 7) (by omega) (by omega) hnil
  rw [← eb] at hs5
  have hs4 := pathTo_cons (a := a₁) (b := b₁) (by omega) (by omega) hs5
  rw [ea] at hs4
  have hs3 := pathTo_cons (a := b₁) (b := a₂) (by omega) (by omega) hs4
  rw [eb] at hs3
  have hs2 := pathTo_cons (a := a₂) (b := b₂) (by omega) (by omega) hs3
  rw [← ea] at hs2
  have hs1 := pathTo_cons (a := 0) (b := a₁) (by omega) (by omega) hs2
  rw [show 0 + (3 * k + 7 - b₂) + (b₁ - a₁) + (a₂ - b₁) + (b₂ - a₂) + (a₁ - 0) = 3 * k + 7
    by omega] at hs1
  obtain ⟨hz, _⟩ := pathTo_spec hk huaw hs1
  set τ := segcat 0 a₁ (segcat a₂ b₂ (segcat b₁ a₂ (segcat a₁ b₁
    (segcat b₂ (3 * k + 7) (fun _ => 0))))) with hτdef
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

/-- The letters of `z_k` at two distinct positions agree only inside the run window or for
the two occurrences of one `a_i`, `i ≤ k-1`, at distance `δ₀ = 2k+6` (Lemma 4.3,
`lem:pairs`). -/
theorem zw_eq_cases {k x y : ℕ} (hk : 3 ≤ k) (hxy : x < y) (hy : y < 3 * k + 7)
    (h : zw k x = zw k y) :
    (k ≤ x ∧ y < 2 * k + 5) ∨ (y = x + (2 * k + 6) ∧ x + 1 < k) := by
  by_cases hb : zw k x = Ltr.b
  · have h1 := zw_b_range hk (show x < 3 * k + 7 by omega) hb
    have h2 := zw_b_range hk hy (by rw [← h]; exact hb)
    exact Or.inl ⟨h1.1, h2.2⟩
  · rcases zw_eq_pair hk (show x < 3 * k + 7 by omega) hy hb h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · exact Or.inr ⟨h1, h2⟩
    · omega

/-- **The crossing restriction.**  Combining the Crossing Lemma 4.7 (`lem:cross`) with the
Pair table (Lemma 4.3, `lem:pairs`): if two chords cross, then the letters at the two
endpoints of the first chord agree and the letters just before the two endpoints of the
second chord agree, and each of these coincidences is only possible inside the run window
or at distance `δ₀ = 2k+6` in the prefix.  This is the tool behind Lemma 5.9
(`lem:positions`). -/
theorem crossing_restrict (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {a₁ b₁ a₂ b₂ : ℕ} (h1 : a₁ < b₁) (h2 : b₁ < a₂) (h3 : a₂ < b₂) (h4 : b₂ ≤ 3 * k + 7)
    (ea : c a₁ = c a₂) (eb : c b₁ = c b₂) :
    ((k ≤ a₁ ∧ a₂ < 2 * k + 5) ∨ (a₂ = a₁ + (2 * k + 6) ∧ a₁ + 1 < k)) ∧
      ((k ≤ b₁ - 1 ∧ b₂ - 1 < 2 * k + 5) ∨
        (b₂ - 1 = (b₁ - 1) + (2 * k + 6) ∧ b₁ < k)) := by
  obtain ⟨hh, hl⟩ := crossing hk huaw h1 h2 h3 h4 ea eb
  refine ⟨zw_eq_cases hk (by omega) (by omega) hh.symm, ?_⟩
  have := zw_eq_cases hk (show b₁ - 1 < b₂ - 1 by omega) (by omega) hl
  rcases this with h | ⟨p, q⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, by omega⟩

/-- **Corollary 4.4 (Shift classification, `cor:shifts`)**.  If two distinct `δ`-chords
exist for the same `δ`, with earlier starting points `i < p`, then either `δ = δ₀ = 2k+6`
and `[i,p] ⊆ [0,k-1]`, or both chords lie in the run window `[k,2k+5]`. -/
theorem shift_classification (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i p δ : ℕ} (hip : i < p) (hδ : 1 ≤ δ) (hpn : p + δ ≤ 3 * k + 7)
    (h1 : c i = c (i + δ)) (h2 : c p = c (p + δ)) :
    (δ = 2 * k + 6 ∧ p + 1 ≤ k) ∨ (k ≤ i ∧ p + δ ≤ 2 * k + 5) := by
  have hz := (rotation hk huaw hip hδ hpn h1 h2).1
  have hzi := zw_eq_cases hk (show i < i + δ by omega) (by omega) (hz i le_rfl hip)
  have hzp := zw_eq_cases hk (show p - 1 < p - 1 + δ by omega) (by omega)
    (hz (p - 1) (by omega) (by omega))
  rcases hzi with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases hzp with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · exact Or.inr ⟨ha, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
  · rcases hzp with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩

/-- **Corollary 4.4 (Shift classification, `cor:shifts`)** applied to *narrow* chords
(both endpoints non-run times on the same side): two distinct narrow chords cannot have
the same length.  This is the remark opening the proof of Lemma 5.6(c),(d)
(`lem:narrow`). -/
theorem narrow_lengths_distinct (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i p lam : ℕ} (hip : i < p) (hlam : 1 ≤ lam)
    (hn1 : i + lam < k ∨ (2 * k + 6 ≤ i ∧ i + lam ≤ 3 * k + 7))
    (hn2 : p + lam < k ∨ (2 * k + 6 ≤ p ∧ p + lam ≤ 3 * k + 7))
    (h1 : c i = c (i + lam)) (h2 : c p = c (p + lam)) : False := by
  have hpn : p + lam ≤ 3 * k + 7 := by rcases hn2 with h | h <;> omega
  rcases shift_classification hk huaw hip hlam hpn h1 h2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases hn2 with h | h <;> omega
  · rcases hn1 with h | h <;> omega

/-- **Lemma 4.6 (Aligned block, `lem:block`)**.  The set of *aligned* indices
`I = {i ≤ k-1 : c_i = c_{i+δ₀}}` (`δ₀ = 2k+6`) is an interval. -/
theorem aligned_block (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i p : ℕ} (hip : i < p) (hpk : p ≤ k - 1)
    (h1 : c i = c (i + (2 * k + 6))) (h2 : c p = c (p + (2 * k + 6))) :
    ∀ t, i ≤ t → t ≤ p → c t = c (t + (2 * k + 6)) :=
  (rotation hk huaw hip (by omega) (by omega) h1 h2).2

end

end AneVsAn
