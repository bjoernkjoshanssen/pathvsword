import RequestProject.Walk

/-!
# Itineraries: paths in the walk graph

Throughout Sections 4–6 of `anevsanseparationv4.tex` the same construction recurs: one
assembles a *second* accepting path of length `n` out of segments `W[i,j]` of the walk
`W = (c_0,…,c_n)`, joined at chords, and out of runs `R⟨t'⟩` around a cycle of the walk
graph.  Since every edge of the walk graph is `e_t = (c_t, z_t, c_{t+1})` for some `t < n`,
such a path is completely described by an *itinerary*: a sequence `τ 0, τ 1, …` of edge
indices whose endpoints match.

This file develops that machinery:

* `Seg k c s s' L τ` — `τ` is a path of length `L` from `s` to `s'` in the walk graph;
* `segW` — the walk segment `W[a,b]`;
* `seg_cat` — concatenation of paths;
* `seg_repit` — repeating a closed path (used for the *spin adjustment* of
  Section 5 of `anevsanseparationv4.tex`);
* `runPath` — the paths `R_{τ₁}^{τ₂}⟨t'⟩` of Lemma 5.3(iii) (`lem:gamma`), obtained by
  going around the cycle a different number of times;
* `pathTo_spec` and `no_second_path` — the Splicing Lemma 4.1 (`lem:splice`) in the form
  in which it is used: a full itinerary must read the same letters and visit the same
  states as `W`.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-- Concatenation of itineraries: the first `L₁` steps follow `τ₁`, the rest follow `τ₂`. -/
def cat (L₁ : ℕ) (τ₁ τ₂ : ℕ → ℕ) : ℕ → ℕ :=
  fun t => if t < L₁ then τ₁ t else τ₂ (t - L₁)

theorem cat_lt {L₁ : ℕ} {τ₁ τ₂ : ℕ → ℕ} {t : ℕ} (h : t < L₁) : cat L₁ τ₁ τ₂ t = τ₁ t :=
  if_pos h

theorem cat_ge {L₁ : ℕ} {τ₁ τ₂ : ℕ → ℕ} {t : ℕ} (h : ¬ t < L₁) :
    cat L₁ τ₁ τ₂ t = τ₂ (t - L₁) :=
  if_neg h

/-- `Seg k c s s' L τ` says that the itinerary `τ` describes a path of length `L` in the
walk graph of `c` (as a walk for a word of length `n = 3k+7`), from the state `s` to the
state `s'`. -/
def Seg (k : ℕ) (c : ℕ → S) (s s' : S) (L : ℕ) (τ : ℕ → ℕ) : Prop :=
  (∀ t, t < L → τ t < 3 * k + 7) ∧
  (∀ t, t + 1 < L → c (τ t + 1) = c (τ (t + 1))) ∧
  (0 < L → c (τ 0) = s) ∧
  (0 < L → c (τ (L - 1) + 1) = s') ∧
  (L = 0 → s = s')

/-- The empty path. -/
theorem seg_nil (k : ℕ) (c : ℕ → S) (s : S) (τ : ℕ → ℕ) : Seg k c s s 0 τ :=
  ⟨fun t ht => absurd ht (by omega), fun t ht => absurd ht (by omega),
    fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ => rfl⟩

/-- The walk segment `W[a,b]`. -/
theorem segW (c : ℕ → S) {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ 3 * k + 7) :
    Seg k c (c a) (c b) (b - a) (fun t => a + t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; show a + t < 3 * k + 7; omega
  · intro t _; rfl
  · intro _; rfl
  · intro h; show c (a + (b - a - 1) + 1) = c b; congr 1; omega
  · intro h; congr 1; omega

/-- Concatenation of two paths of the walk graph. -/
theorem seg_cat {s s' s'' : S} {L₁ L₂ : ℕ} {τ₁ τ₂ : ℕ → ℕ}
    (h1 : Seg k c s s'' L₁ τ₁) (h2 : Seg k c s'' s' L₂ τ₂) :
    Seg k c s s' (L₁ + L₂) (cat L₁ τ₁ τ₂) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    by_cases hc : t < L₁
    · rw [cat_lt hc]; exact a1 t hc
    · rw [cat_ge hc]; exact b1 (t - L₁) (by omega)
  · intro t ht
    by_cases hc : t + 1 < L₁
    · rw [cat_lt (by omega), cat_lt hc]; exact a2 t hc
    · rcases Nat.lt_or_ge t L₁ with hc' | hc'
      · rw [cat_lt hc', cat_ge (by omega), show t + 1 - L₁ = 0 by omega,
          show t = L₁ - 1 by omega]
        rw [a4 (by omega)]
        exact (b3 (by omega)).symm
      · rw [cat_ge (by omega), cat_ge (by omega), show t + 1 - L₁ = (t - L₁) + 1 by omega]
        exact b2 (t - L₁) (by omega)
  · intro hL
    rcases Nat.eq_zero_or_pos L₁ with h0 | h0
    · subst h0
      rw [cat_ge (by omega), Nat.sub_zero]
      exact (b3 (by omega)).trans (a5 rfl).symm
    · rw [cat_lt h0]; exact a3 h0
  · intro hL
    rcases Nat.eq_zero_or_pos L₂ with h0 | h0
    · subst h0
      rw [cat_lt (by omega), Nat.add_zero]
      exact (a4 (by omega)).trans (b5 rfl)
    · rw [cat_ge (by omega), show L₁ + L₂ - 1 - L₁ = L₂ - 1 by omega]
      exact b4 h0
  · intro hL
    exact (a5 (by omega)).trans (b5 (by omega))

/-- Repeat a closed path `σ` times. -/
def repit : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0, _, _ => fun _ => 0
  | (σ + 1), L, τ => cat L τ (repit σ L τ)

/-- Repeating a closed path of the walk graph: this is the *spin adjustment* of
Section 5 of `anevsanseparationv4.tex`. -/
theorem seg_repit {v : S} {L : ℕ} {τ : ℕ → ℕ} (h : Seg k c v v L τ) (σ : ℕ) :
    Seg k c v v (σ * L) (repit σ L τ) := by
  induction σ with
  | zero => simpa using seg_nil k c v (repit 0 L τ)
  | succ σ ih =>
    have := seg_cat h ih
    rw [show (σ + 1) * L = L + σ * L by ring]
    exact this

theorem repit_zero {σ L : ℕ} {f : ℕ → ℕ} (hσ : 1 ≤ σ) (hL : 1 ≤ L) :
    repit σ L f 0 = f 0 := by
  obtain ⟨σ, rfl⟩ : ∃ m, σ = m + 1 := ⟨σ - 1, by omega⟩
  rw [repit, cat_lt (by omega)]

theorem repit_at_period {σ L : ℕ} {f : ℕ → ℕ} :
    repit (σ + 1) L f L = repit σ L f 0 := by
  rw [repit, cat_ge (by omega), Nat.sub_self]

/-- Iterated periodicity of the walk on the stretch. -/
theorem period_iter {p q ell : ℕ} (hper : ∀ t, p ≤ t → t + ell ≤ q → c t = c (t + ell)) :
    ∀ (i x : ℕ), p ≤ x → x + i * ell ≤ q → c x = c (x + i * ell) := by
  intro i
  induction i with
  | zero => intro x _ _; simp
  | succ i ih =>
    intro x hx hxq
    rw [show (i + 1) * ell = i * ell + ell by ring] at hxq
    have h1 : c x = c (x + ell) := hper x hx (by omega)
    have h2 : c (x + ell) = c (x + ell + i * ell) := ih (x + ell) (by omega) (by omega)
    rw [h1, h2, show x + ell + i * ell = x + (i + 1) * ell by ring]

/-- **Lemma 5.3(iii) (`lem:gamma`)**: the paths `R_{τ₁}^{τ₂}⟨t'⟩`.  If the walk is
`ell`-periodic on the stretch `[p,q]`, which consists of `tt` full turns plus `roff`
extra steps, then for every number `u` of turns there is a path in the walk graph from
`c τ₁` to `c τ₂` of length `(p - τ₁) + (u * ell + roff) + (τ₂ - q)`.  For `u = tt` this
is the walk segment `W[τ₁,τ₂]` itself. -/
theorem runPath {p q ell tt roff τ₁ τ₂ : ℕ} (hell : 0 < ell)
    (hper : ∀ t, p ≤ t → t + ell ≤ q → c t = c (t + ell))
    (hq : p + tt * ell + roff = q) (htt : 1 ≤ tt)
    (h1 : τ₁ ≤ p) (h2 : q ≤ τ₂) (h3 : τ₂ ≤ 3 * k + 7) (u : ℕ) :
    ∃ τ, Seg k c (c τ₁) (c τ₂) ((p - τ₁) + (u * ell + roff) + (τ₂ - q)) τ := by
  have hmul : ell ≤ tt * ell := Nat.le_mul_of_pos_left ell htt
  have hpq : p + ell ≤ q := by omega
  have hqn : q ≤ 3 * k + 7 := by omega
  -- the loop `W[p, p+ell]`
  have hloopEnd : c (p + ell) = c p := (hper p le_rfl (by omega)).symm
  have hloop : Seg k c (c p) (c p) ell (fun t => p + t) := by
    have h := segW (k := k) c (show p ≤ p + ell by omega) (by omega)
    rw [hloopEnd, show p + ell - p = ell by omega] at h
    exact h
  -- the leftover `W[p, p+roff]`, whose endpoint is `c q`
  have hroffEnd : c (p + roff) = c q := by
    have h := period_iter hper tt (p + roff) (by omega) (by omega)
    rw [show p + roff + tt * ell = q by omega] at h
    exact h
  have hleft : Seg k c (c τ₁) (c p) (p - τ₁) (fun t => τ₁ + t) := segW c h1 (by omega)
  have hmid : Seg k c (c p) (c p) (u * ell) (repit u ell (fun t => p + t)) :=
    seg_repit hloop u
  have hoff : Seg k c (c p) (c q) roff (fun t => p + t) := by
    have h := segW (k := k) c (show p ≤ p + roff by omega) (by omega)
    rw [hroffEnd, show p + roff - p = roff by omega] at h
    exact h
  have hright : Seg k c (c q) (c τ₂) (τ₂ - q) (fun t => q + t) := segW c h2 h3
  have hall := seg_cat (seg_cat (seg_cat hleft hmid) hoff) hright
  rw [show p - τ₁ + u * ell + roff + (τ₂ - q) = p - τ₁ + (u * ell + roff) + (τ₂ - q)
    by ring] at hall
  exact ⟨_, hall⟩

/-- `PathTo k c s L τ` says that `τ` describes a path of length `L` in the walk graph,
starting at the state `s` and ending at `c n`. -/
def PathTo (k : ℕ) (c : ℕ → S) (s : S) (L : ℕ) (τ : ℕ → ℕ) : Prop :=
  Seg k c s (c (3 * k + 7)) L τ

theorem pathTo_nil (k : ℕ) (c : ℕ → S) (τ : ℕ → ℕ) : PathTo k c (c (3 * k + 7)) 0 τ :=
  seg_nil k c _ τ

/-- Prepend the walk segment `W[a,b]` to the itinerary `τ`. -/
def segcat (a b : ℕ) (τ : ℕ → ℕ) : ℕ → ℕ :=
  cat (b - a) (fun t => a + t) τ

theorem segcat_lt {a b : ℕ} {τ : ℕ → ℕ} {j : ℕ} (h : j < b - a) :
    segcat a b τ j = a + j := if_pos h

theorem segcat_ge {a b : ℕ} {τ : ℕ → ℕ} {j : ℕ} (h : ¬ j < b - a) :
    segcat a b τ j = τ (j - (b - a)) := if_neg h

/-- Prepending the walk segment `W[a,b]`. -/
theorem pathTo_cons {a b L : ℕ} {τ : ℕ → ℕ} (hab : a ≤ b) (hbn : b ≤ 3 * k + 7)
    (h : PathTo k c (c b) L τ) :
    PathTo k c (c a) (L + (b - a)) (segcat a b τ) := by
  have := seg_cat (segW (k := k) c hab hbn) h
  rw [show b - a + L = L + (b - a) by omega] at this
  exact this

/-- A full itinerary yields a path of the walk graph of length `n` from `c₀` to `c_n`;
by unique acceptance it must read the same letters and visit the same states as the walk.
This is the systematic form of the Splicing Lemma 4.1 (`lem:splice`). -/
theorem pathTo_spec (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {τ : ℕ → ℕ} (h : PathTo k c (c 0) (3 * k + 7) τ) :
    (∀ t, t < 3 * k + 7 → zw k (τ t) = zw k t) ∧ (∀ t, t < 3 * k + 7 → c (τ t) = c t) := by
  classical
  obtain ⟨h1, h2, h3, h4, _⟩ := h
  set n := 3 * k + 7 with hn
  have hnpos : 0 < n := by omega
  set p : ℕ → S := fun t => if t < n then c (τ t) else c n with hp
  have h0 : p 0 = c 0 := by
    simp only [hp, if_pos hnpos]
    exact h3 hnpos
  have hend : p n = c n := by simp only [hp, if_neg (lt_irrefl n)]
  have hrun : IsRun (walkStep (zw k) n c) n (fun t => zw k (τ t)) p := by
    intro t ht
    refine ⟨τ t, h1 t ht, ?_, rfl, ?_⟩
    · simp only [hp, if_pos ht]
    · rcases Nat.lt_or_ge (t + 1) n with h' | h'
      · simp only [hp, if_pos h']
        exact h2 t h'
      · have htn : t + 1 = n := by omega
        rw [htn]
        simp only [hp, if_neg (lt_irrefl n)]
        rw [show t = n - 1 by omega]
        exact h4 hnpos
  obtain ⟨hx, hpp⟩ := huaw (fun t => zw k (τ t)) p h0 hend hrun
  refine ⟨hx, fun t ht => ?_⟩
  have := hpp t (le_of_lt ht)
  simpa only [hp, if_pos ht] using this

/-- **The contradiction principle.**  If an itinerary sends the position `j` to a position
`v` carrying a different letter, the walk is not uniquely accepting.  All the surgeries of
Sections 4–6 of `anevsanseparationv4.tex` are applications of this principle. -/
theorem no_second_path (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {τ : ℕ → ℕ} (h : PathTo k c (c 0) (3 * k + 7) τ) {j : ℕ} (hj : j < 3 * k + 7)
    (hne : zw k (τ j) ≠ zw k j) : False :=
  hne ((pathTo_spec hk huaw h).1 j hj)

end

end AneVsAn
