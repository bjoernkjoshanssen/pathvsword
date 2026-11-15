import RequestProject.GenericWalk

/-!
# Itineraries: paths in the walk graph

Throughout Sections 4–6 of `anevsanseparationv4.tex` the same construction recurs: one
assembles a *second* accepting path of length `n` out of segments `W[i,j]` of the walk
`W = (c_0,…,c_n)`, joined at chords, and out of runs `R⟨t'⟩` around a cycle of the walk
graph.  Since every edge of the walk graph is `e_t = (c_t, z_t, c_{t+1})` for some `t < n`,
such a path is completely described by an *itinerary*: a sequence `τ 0, τ 1, …` of edge
indices whose endpoints match.

This file develops that machinery:

* `Seg n c s s' L τ` — `τ` is a path of length `L` from `s` to `s'` in the walk graph;
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

namespace AneVsAn.Generic

set_option autoImplicit false

section

variable {n : ℕ} {Λ S : Type} {c : ℕ → S} {x : ℕ → Λ}

/-- Concatenation of itineraries: the first `L₁` steps follow `τ₁`, the rest follow `τ₂`. -/
def cat (L₁ : ℕ) (τ₁ τ₂ : ℕ → ℕ) : ℕ → ℕ :=
  fun t => if t < L₁ then τ₁ t else τ₂ (t - L₁)

theorem cat_lt {L₁ : ℕ} {τ₁ τ₂ : ℕ → ℕ} {t : ℕ} (h : t < L₁) : cat L₁ τ₁ τ₂ t = τ₁ t :=
  if_pos h

theorem cat_ge {L₁ : ℕ} {τ₁ τ₂ : ℕ → ℕ} {t : ℕ} (h : ¬ t < L₁) :
    cat L₁ τ₁ τ₂ t = τ₂ (t - L₁) :=
  if_neg h

/-- `Seg n c s s' L τ` says that the itinerary `τ` describes a path of length `L` in the
walk graph of `c` (as a walk for a word of length `n`), from the state `s` to the
state `s'`. -/
def Seg (n : ℕ) (c : ℕ → S) (s s' : S) (L : ℕ) (τ : ℕ → ℕ) : Prop :=
  (∀ t, t < L → τ t < n) ∧
  (∀ t, t + 1 < L → c (τ t + 1) = c (τ (t + 1))) ∧
  (0 < L → c (τ 0) = s) ∧
  (0 < L → c (τ (L - 1) + 1) = s') ∧
  (L = 0 → s = s')

/-- The empty path. -/
theorem seg_nil (n : ℕ) (c : ℕ → S) (s : S) (τ : ℕ → ℕ) : Seg n c s s 0 τ :=
  ⟨fun t ht => absurd ht (by omega), fun t ht => absurd ht (by omega),
    fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ => rfl⟩

/-- The walk segment `W[a,b]`. -/
theorem segW (c : ℕ → S) {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    Seg n c (c a) (c b) (b - a) (fun t => a + t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; show a + t < n; omega
  · intro t _; rfl
  · intro _; rfl
  · intro h; show c (a + (b - a - 1) + 1) = c b; congr 1; omega
  · intro h; congr 1; omega

/-- Concatenation of two paths of the walk graph. -/
theorem seg_cat {s s' s'' : S} {L₁ L₂ : ℕ} {τ₁ τ₂ : ℕ → ℕ}
    (h1 : Seg n c s s'' L₁ τ₁) (h2 : Seg n c s'' s' L₂ τ₂) :
    Seg n c s s' (L₁ + L₂) (cat L₁ τ₁ τ₂) := by
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
theorem seg_repit {v : S} {L : ℕ} {τ : ℕ → ℕ} (h : Seg n c v v L τ) (σ : ℕ) :
    Seg n c v v (σ * L) (repit σ L τ) := by
  induction σ with
  | zero => simpa using seg_nil n c v (repit 0 L τ)
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
    (h1 : τ₁ ≤ p) (h2 : q ≤ τ₂) (h3 : τ₂ ≤ n) (u : ℕ) :
    ∃ τ, Seg n c (c τ₁) (c τ₂) ((p - τ₁) + (u * ell + roff) + (τ₂ - q)) τ := by
  have hmul : ell ≤ tt * ell := Nat.le_mul_of_pos_left ell htt
  have hpq : p + ell ≤ q := by omega
  have hqn : q ≤ n := by omega
  -- the loop `W[p, p+ell]`
  have hloopEnd : c (p + ell) = c p := (hper p le_rfl (by omega)).symm
  have hloop : Seg n c (c p) (c p) ell (fun t => p + t) := by
    have h := segW (n := n) c (show p ≤ p + ell by omega) (by omega)
    rw [hloopEnd, show p + ell - p = ell by omega] at h
    exact h
  -- the leftover `W[p, p+roff]`, whose endpoint is `c q`
  have hroffEnd : c (p + roff) = c q := by
    have h := period_iter hper tt (p + roff) (by omega) (by omega)
    rw [show p + roff + tt * ell = q by omega] at h
    exact h
  have hleft : Seg n c (c τ₁) (c p) (p - τ₁) (fun t => τ₁ + t) := segW c h1 (by omega)
  have hmid : Seg n c (c p) (c p) (u * ell) (repit u ell (fun t => p + t)) :=
    seg_repit hloop u
  have hoff : Seg n c (c p) (c q) roff (fun t => p + t) := by
    have h := segW (n := n) c (show p ≤ p + roff by omega) (by omega)
    rw [hroffEnd, show p + roff - p = roff by omega] at h
    exact h
  have hright : Seg n c (c q) (c τ₂) (τ₂ - q) (fun t => q + t) := segW c h2 h3
  have hall := seg_cat (seg_cat (seg_cat hleft hmid) hoff) hright
  rw [show p - τ₁ + u * ell + roff + (τ₂ - q) = p - τ₁ + (u * ell + roff) + (τ₂ - q)
    by ring] at hall
  exact ⟨_, hall⟩

/-- `PathTo n c s L τ` says that `τ` describes a path of length `L` in the walk graph,
starting at the state `s` and ending at `c n`. -/
def PathTo (n : ℕ) (c : ℕ → S) (s : S) (L : ℕ) (τ : ℕ → ℕ) : Prop :=
  Seg n c s (c (n)) L τ

theorem pathTo_nil (n : ℕ) (c : ℕ → S) (τ : ℕ → ℕ) : PathTo n c (c (n)) 0 τ :=
  seg_nil n c _ τ

/-- Prepend the walk segment `W[a,b]` to the itinerary `τ`. -/
def segcat (a b : ℕ) (τ : ℕ → ℕ) : ℕ → ℕ :=
  cat (b - a) (fun t => a + t) τ

theorem segcat_lt {a b : ℕ} {τ : ℕ → ℕ} {j : ℕ} (h : j < b - a) :
    segcat a b τ j = a + j := if_pos h

theorem segcat_ge {a b : ℕ} {τ : ℕ → ℕ} {j : ℕ} (h : ¬ j < b - a) :
    segcat a b τ j = τ (j - (b - a)) := if_neg h

/-- Prepending the walk segment `W[a,b]`. -/
theorem pathTo_cons {a b L : ℕ} {τ : ℕ → ℕ} (hab : a ≤ b) (hbn : b ≤ n)
    (h : PathTo n c (c b) L τ) :
    PathTo n c (c a) (L + (b - a)) (segcat a b τ) := by
  have := seg_cat (segW (n := n) c hab hbn) h
  rw [show b - a + L = L + (b - a) by omega] at this
  exact this

/-- A full itinerary yields a path of the walk graph of length `n` from `c₀` to `c_n`;
by unique acceptance it must read the same letters and visit the same states as the walk.
This is the systematic form of the Splicing Lemma 4.1 (`lem:splice`). -/
theorem pathTo_spec (huaw : IsUAWalk x n c)
    {τ : ℕ → ℕ} (h : PathTo n c (c 0) (n) τ) :
    (∀ t, t < n → x (τ t) = x t) ∧ (∀ t, t < n → c (τ t) = c t) := by
  classical
  obtain ⟨h1, h2, h3, h4, _⟩ := h
  by_cases hnzero : n = 0
  · subst n
    exact ⟨fun t ht => by omega, fun t ht => by omega⟩
  have hnpos : 0 < n := by omega
  set p : ℕ → S := fun t => if t < n then c (τ t) else c n with hp
  have h0 : p 0 = c 0 := by
    simp only [hp, if_pos hnpos]
    exact h3 hnpos
  have hend : p n = c n := by simp only [hp, if_neg (lt_irrefl n)]
  have hrun : IsRun (walkStep (x) n c) n (fun t => x (τ t)) p := by
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
  obtain ⟨hx, hpp⟩ := huaw (fun t => x (τ t)) p h0 hend hrun
  refine ⟨hx, fun t ht => ?_⟩
  have := hpp t (le_of_lt ht)
  simpa only [hp, if_pos ht] using this

/-- **The contradiction principle.**  If an itinerary sends the position `j` to a position
`v` carrying a different letter, the walk is not uniquely accepting.  All the surgeries of
Sections 4–6 of `anevsanseparationv4.tex` are applications of this principle. -/
theorem no_second_path (huaw : IsUAWalk x n c)
    {τ : ℕ → ℕ} (h : PathTo n c (c 0) (n) τ) {j : ℕ} (hj : j < n)
    (hne : x (τ j) ≠ x j) : False :=
  hne ((pathTo_spec huaw h).1 j hj)

end

end AneVsAn.Generic

namespace AneVsAn.Generic

variable {n : ℕ} {Λ S : Type} {c : ℕ → S} {x : ℕ → Λ}

/-- The complete labeled transition at an index of the original walk. -/
def edge (x : ℕ → Λ) (c : ℕ → S) (t : ℕ) : S × Λ × S :=
  (c t, x t, c (t + 1))

/-- A full itinerary agrees with the walk on complete labeled edges. -/
theorem pathTo_edge (huaw : IsUAWalk x n c) {τ : ℕ → ℕ}
    (h : PathTo n c (c 0) n τ) (t : ℕ) (ht : t < n) :
    edge x c (τ t) = edge x c t := by
  obtain ⟨hx, hc⟩ := pathTo_spec huaw h
  have hend : c (τ t + 1) = c (t + 1) := by
    by_cases htn : t + 1 < n
    · exact (h.2.1 t htn).trans (hc (t + 1) htn)
    · have htlast : t = n - 1 := by omega
      have htn' : t + 1 = n := by omega
      rw [htlast]
      simpa only [show n - 1 + 1 = n by omega] using h.2.2.2.1 (by omega)
  exact Prod.ext (hc t ht) (Prod.ext (hx t ht) hend)

/-- Splicing: every path of the prescribed length between two walk times agrees
with the original segment, including both its letters and states. -/
theorem seg_spec (huaw : IsUAWalk x n c) {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n)
    {τ : ℕ → ℕ} (h : Seg n c (c a) (c b) (b - a) τ) :
    ∀ t, t < b - a → edge x c (τ t) = edge x c (a + t) := by
  have hleft := segW c (show 0 ≤ a by omega) (show a ≤ n by omega)
  have hright := segW c hbn (show n ≤ n by rfl)
  have hall := seg_cat (seg_cat hleft h) hright
  have hlen : a - 0 + (b - a) + (n - b) = n := by omega
  rw [hlen] at hall
  intro t ht
  have heq := pathTo_edge huaw hall (a + t) (by omega)
  rw [cat_lt (show a + t < a - 0 + (b - a) by omega),
    cat_ge (show ¬ a + t < a - 0 by omega), show a + t - (a - 0) = t by omega] at heq
  exact heq

/-- Parallel transitions between the same ordered pair of states have the same label. -/
theorem single_label (huaw : IsUAWalk x n c) {s t : ℕ} (hs : s < n) (ht : t < n)
    (h0 : c s = c t) (h1 : c (s + 1) = c (t + 1)) : x s = x t := by
  have hseg : Seg n c (c t) (c (t + 1)) (t + 1 - t) (fun _ => s) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; exact hs
    · intro i hi; omega
    · intro _; exact h0
    · intro _; exact h1
    · omega
  have hh := seg_spec huaw (show t ≤ t + 1 by omega) (show t + 1 ≤ n by omega) hseg 0 (by omega)
  exact congrArg (fun e : S × Λ × S => e.2.1) hh

section EdgeCounts

variable [DecidableEq Λ] [DecidableEq S]

/-- Number of occurrences of an edge in an itinerary of length `len`. -/
def edgeCount (x : ℕ → Λ) (c : ℕ → S) (len : ℕ) (τ : ℕ → ℕ)
    (e : S × Λ × S) : ℕ :=
  ∑ t ∈ Finset.range len, if edge x c (τ t) = e then 1 else 0

@[simp] theorem edgeCount_zero (τ : ℕ → ℕ) (e : S × Λ × S) :
    edgeCount x c 0 τ e = 0 := by simp [edgeCount]

theorem edgeCount_cat (l₁ l₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (e : S × Λ × S) :
    edgeCount x c (l₁ + l₂) (cat l₁ τ₁ τ₂) e =
      edgeCount x c l₁ τ₁ e + edgeCount x c l₂ τ₂ e := by
  simp only [edgeCount, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [cat_lt (Finset.mem_range.mp ht)]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [cat_ge (by omega : ¬ l₁ + t < l₁), Nat.add_sub_cancel_left]

theorem edgeCount_repit (σ len : ℕ) (τ : ℕ → ℕ) (e : S × Λ × S) :
    edgeCount x c (σ * len) (repit σ len τ) e = σ * edgeCount x c len τ e := by
  induction σ with
  | zero => simp
  | succ σ ih =>
    rw [show (σ + 1) * len = len + σ * len by ring, repit, edgeCount_cat, ih]
    ring

theorem edgeCount_walk_add (a l₁ l₂ : ℕ) (e : S × Λ × S) :
    edgeCount x c (l₁ + l₂) (fun t => a + t) e =
      edgeCount x c l₁ (fun t => a + t) e +
      edgeCount x c l₂ (fun t => a + l₁ + t) e := by
  simp only [edgeCount, Finset.sum_range_add, Nat.add_assoc]

theorem pathTo_edgeCount (huaw : IsUAWalk x n c) {τ : ℕ → ℕ}
    (h : PathTo n c (c 0) n τ) (e : S × Λ × S) :
    edgeCount x c n τ e = edgeCount x c n id e := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [pathTo_edge huaw h t (Finset.mem_range.mp ht)]
  rfl

end EdgeCounts
end AneVsAn.Generic

namespace AneVsAn.Generic

variable {n : ℕ} {Λ S : Type} {c : ℕ → S} {x : ℕ → Λ}
variable [DecidableEq Λ] [DecidableEq S]

theorem edgeCount_walk_split {a b d : ℕ} (hab : a ≤ b) (hbd : b ≤ d)
    (e : S × Λ × S) :
    edgeCount x c (d - a) (fun t => a + t) e =
      edgeCount x c (b - a) (fun t => a + t) e +
      edgeCount x c (d - b) (fun t => b + t) e := by
  rw [show d - a = (b - a) + (d - b) by omega, edgeCount_walk_add]
  simp only [show a + (b - a) = b by omega]

/-- Delete a chord and insert an equal-length closed path at a surviving visit.
Unique acceptance forces equality of every labeled edge count. -/
theorem exchange_one (huaw : IsUAWalk x n c)
    {a b t : ℕ} (hab : a ≤ b) (hbn : b ≤ n) (htn : t ≤ n)
    (hchord : c a = c b) (hpos : t ≤ a ∨ b ≤ t)
    {τ : ℕ → ℕ} (hC : Seg n c (c t) (c t) (b - a) τ)
    (e : S × Λ × S) :
    edgeCount x c (b - a) (fun j => a + j) e = edgeCount x c (b - a) τ e := by
  rcases hpos with hta | hbt
  · have hleft := segW c (show 0 ≤ t by omega) htn
    have hmid := segW c hta (show a ≤ n by omega)
    rw [hchord] at hmid
    have hright := segW c hbn (show n ≤ n by rfl)
    have hall := seg_cat (seg_cat (seg_cat hleft hC) hmid) hright
    have hlen : t - 0 + (b - a) + (a - t) + (n - b) = n := by omega
    have hfull : PathTo n c (c 0) n
        (cat (t - 0 + (b - a) + (a - t))
          (cat (t - 0 + (b - a)) (cat (t - 0) (fun j => 0 + j) τ)
            (fun j => t + j)) (fun j => b + j)) := by
      rwa [hlen] at hall
    have heq := pathTo_edgeCount huaw hfull e
    have hnew := edgeCount_cat (x := x) (c := c)
      (t - 0 + (b - a) + (a - t)) (n - b)
      (cat (t - 0 + (b - a)) (cat (t - 0) (fun j => 0 + j) τ)
        (fun j => t + j)) (fun j => b + j) e
    rw [hlen, edgeCount_cat, edgeCount_cat] at hnew
    have hsplit1 := edgeCount_walk_split (x := x) (c := c) (show 0 ≤ t by omega) htn e
    have hsplit2 := edgeCount_walk_split (x := x) (c := c) hta (show a ≤ n by omega) e
    have hsplit3 := edgeCount_walk_split (x := x) (c := c) hab hbn e
    simp only [Nat.sub_zero, Nat.zero_add] at hnew hsplit1 heq
    change edgeCount x c n _ e = edgeCount x c n (fun j => j) e at heq
    omega
  · have hleft := segW c (show 0 ≤ a by omega) (show a ≤ n by omega)
    rw [hchord] at hleft
    have hmid := segW c hbt htn
    have hright := segW c htn (show n ≤ n by rfl)
    have hall := seg_cat (seg_cat (seg_cat hleft hmid) hC) hright
    have hlen : a - 0 + (t - b) + (b - a) + (n - t) = n := by omega
    have hfull : PathTo n c (c 0) n
        (cat (a - 0 + (t - b) + (b - a))
          (cat (a - 0 + (t - b)) (cat (a - 0) (fun j => 0 + j) (fun j => b + j)) τ)
          (fun j => t + j)) := by
      rwa [hlen] at hall
    have heq := pathTo_edgeCount huaw hfull e
    have hnew := edgeCount_cat (x := x) (c := c)
      (a - 0 + (t - b) + (b - a)) (n - t)
      (cat (a - 0 + (t - b)) (cat (a - 0) (fun j => 0 + j) (fun j => b + j)) τ)
      (fun j => t + j) e
    rw [hlen, edgeCount_cat, edgeCount_cat] at hnew
    have hsplit1 := edgeCount_walk_split (x := x) (c := c) (show 0 ≤ a by omega) (show a ≤ n by omega) e
    have hsplit2 := edgeCount_walk_split (x := x) (c := c) hab hbn e
    have hsplit3 := edgeCount_walk_split (x := x) (c := c) hbt htn e
    simp only [Nat.sub_zero, Nat.zero_add] at hnew hsplit1 heq
    change edgeCount x c n _ e = edgeCount x c n (fun j => j) e at heq
    omega

end AneVsAn.Generic

namespace AneVsAn.Generic

variable {n : ℕ} {Λ S : Type} {c : ℕ → S} {x : ℕ → Λ}
variable [DecidableEq Λ] [DecidableEq S]

theorem edgeCount_eq_len_iff {len : ℕ} {τ : ℕ → ℕ} {e : S × Λ × S} :
    edgeCount x c len τ e = len ↔ ∀ t, t < len → edge x c (τ t) = e := by
  simp only [edgeCount, ← Finset.card_filter]
  simpa only [Finset.card_range, Finset.mem_range] using
    (Finset.card_filter_eq_iff (s := Finset.range len) (p := fun t => edge x c (τ t) = e))

theorem edgeCount_eq_zero_iff {len : ℕ} {τ : ℕ → ℕ} {e : S × Λ × S} :
    edgeCount x c len τ e = 0 ↔ ∀ t, t < len → edge x c (τ t) ≠ e := by
  simp only [edgeCount, ← Finset.card_filter]
  simpa only [Finset.mem_range] using
    (Finset.card_filter_eq_zero_iff (s := Finset.range len) (p := fun t => edge x c (τ t) = e))

@[simp] theorem edgeCount_const (a len : ℕ) :
    edgeCount x c len (fun _ => a) (edge x c a) = len := by
  simp [edgeCount]

omit [DecidableEq S] in
/-- An itinerary consisting entirely of one self-loop. -/
theorem seg_loop {a : ℕ} (ha : a < n) (hloop : c a = c (a + 1)) (len : ℕ) :
    Seg n c (c a) (c a) len (fun _ => a) := by
  refine ⟨fun _ _ => ha, fun _ _ => hloop.symm, fun _ => rfl,
    fun _ => hloop.symm, fun _ => rfl⟩

end AneVsAn.Generic

namespace AneVsAn.Generic

variable {n : ℕ} {Λ S : Type} {c : ℕ → S} {x : ℕ → Λ}
variable [DecidableEq Λ] [DecidableEq S]

/-- Remove two disjoint chords and insert an equal-length closed path between them. -/
theorem exchange_two_between (huaw : IsUAWalk x n c)
    {a b u s t : ℕ} (hab : a ≤ b) (hbu : b ≤ u) (hus : u ≤ s) (hst : s ≤ t) (htn : t ≤ n)
    (habc : c a = c b) (hstc : c s = c t)
    {τ : ℕ → ℕ} (hC : Seg n c (c u) (c u) ((b - a) + (t - s)) τ)
    (e : S × Λ × S) :
    edgeCount x c (b - a) (fun j => a + j) e +
      edgeCount x c (t - s) (fun j => s + j) e =
      edgeCount x c ((b - a) + (t - s)) τ e := by
  have h0 := segW c (show 0 ≤ a by omega) (show a ≤ n by omega)
  rw [habc] at h0
  have h1 := segW c hbu (show u ≤ n by omega)
  have h2 := segW c hus (show s ≤ n by omega)
  rw [hstc] at h2
  have h3 := segW c htn (show n ≤ n by rfl)
  have hall := seg_cat (seg_cat (seg_cat (seg_cat h0 h1) hC) h2) h3
  have hlen : a - 0 + (u - b) + (b - a + (t - s)) + (s - u) + (n - t) = n := by omega
  have hfull : PathTo n c (c 0) n
      (cat (a - 0 + (u - b) + (b - a + (t - s)) + (s - u))
        (cat (a - 0 + (u - b) + (b - a + (t - s)))
          (cat (a - 0 + (u - b)) (cat (a - 0) (fun j => 0 + j) (fun j => b + j)) τ)
          (fun j => u + j)) (fun j => t + j)) := by
    rwa [hlen] at hall
  have heq := pathTo_edgeCount huaw hfull e
  have hnew := edgeCount_cat (x := x) (c := c)
    (a - 0 + (u - b) + (b - a + (t - s)) + (s - u)) (n - t)
    (cat (a - 0 + (u - b) + (b - a + (t - s)))
      (cat (a - 0 + (u - b)) (cat (a - 0) (fun j => 0 + j) (fun j => b + j)) τ)
      (fun j => u + j)) (fun j => t + j) e
  rw [hlen, edgeCount_cat, edgeCount_cat, edgeCount_cat] at hnew
  have hsplit0 := edgeCount_walk_split (x := x) (c := c) (show 0 ≤ a by omega) (show a ≤ n by omega) e
  have hsplit1 := edgeCount_walk_split (x := x) (c := c) hab (show b ≤ n by omega) e
  have hsplit2 := edgeCount_walk_split (x := x) (c := c) hbu (show u ≤ n by omega) e
  have hsplit3 := edgeCount_walk_split (x := x) (c := c) hus (show s ≤ n by omega) e
  have hsplit4 := edgeCount_walk_split (x := x) (c := c) hst htn e
  simp only [Nat.sub_zero, Nat.zero_add] at hnew hsplit0 heq
  change edgeCount x c n _ e = edgeCount x c n (fun j => j) e at heq
  omega

end AneVsAn.Generic
