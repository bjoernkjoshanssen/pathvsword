import RequestProject.WalkOffCycle
import RequestProject.WalkBridgeParity

/-!
# Two odd chords (Lemma 5.14, `lem:twoodd`) — the candidate paths

This file formalizes the surgery machinery behind Lemma 5.14 (`lem:twoodd`) of
`ane-vs-an-separation-v4_1.tex`: given two chords `a = (α₁,α₂)` and `b = (β₁,β₂)` whose
lengths `L_a, L_b` differ by an even number, one of the candidate concatenations
```
π_A = W[0,α₁] W[α₂,β₂] W[β₁,n],      π_D = W[0,α₂] W[α₁,β₁] W[β₂,n]
```
becomes, after a *spin adjustment* (Section 5.2) inside the segments containing the
stretch `S`, a second accepting path of length `n`.

The file provides:

* `chord_path_plain`, `chord_path_spin`, `chord_path_cedge` — the three *non-triviality
  tests* used in the proof of Lemma 5.14: the first junction of the candidate compares
  the two endpoint letters of a chord (`chord_path_plain`); when the first segment
  contains `S`, the junction is compared with a letter of the run window
  (`chord_path_spin`); and when the first segment also contains the `c`-edge, the moved
  `c`-edge does the job (`chord_path_cedge`).
* `Stretch.slen_eq`, `exists_turn_up`, `exists_turn_down`, `exists_turns_down` — the
  arithmetic of the spin adjustment.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-! ### The arithmetic of the spin adjustment (Section 5.2) -/

namespace Stretch

/-- The length of the spin adjusted segment `W[x,y]⟨u⟩` differs from `y-x` by
`(u-t)·ℓ`.  This is the bookkeeping identity behind every length computation of
Section 5 of `ane-vs-an-separation-v4_1.tex`. -/
theorem slen_eq (Str : Stretch k c) {x y : ℕ} (hx : x ≤ Str.p) (hy : Str.q ≤ y) (u : ℕ) :
    Str.slen x y u + Str.tt * Str.ell = (y - x) + u * Str.ell := by
  have h := Str.hlen
  simp only [slen]
  omega

end Stretch

/-- Spin adjustment upwards: `u·ℓ = t·ℓ + D` is solvable when `ℓ ∣ D`. -/
theorem exists_turn_up (Str : Stretch k c) {D : ℕ} (hdvd : Str.ell ∣ D) :
    ∃ u, u * Str.ell = Str.tt * Str.ell + D := by
  obtain ⟨d, rfl⟩ := hdvd
  exact ⟨Str.tt + d, by ring⟩

/-- Spin adjustment downwards: `u·ℓ + D = t·ℓ` is solvable when `ℓ ∣ D` and `D ≤ t·ℓ`. -/
theorem exists_turn_down (Str : Stretch k c) {D : ℕ} (hdvd : Str.ell ∣ D)
    (hD : D ≤ Str.tt * Str.ell) : ∃ u, u * Str.ell + D = Str.tt * Str.ell := by
  obtain ⟨d, rfl⟩ := hdvd
  have hell := Str.hell
  have hcomm : Str.ell * d = d * Str.ell := Nat.mul_comm _ _
  have hd : d ≤ Str.tt := by
    by_contra hcon
    push_neg at hcon
    have hle : (Str.tt + 1) * Str.ell ≤ d * Str.ell := Nat.mul_le_mul (by omega) (le_refl _)
    have hex : (Str.tt + 1) * Str.ell = Str.tt * Str.ell + Str.ell := by ring
    omega
  refine ⟨Str.tt - d, ?_⟩
  have h1 : (Str.tt - d) * Str.ell + d * Str.ell = Str.tt * Str.ell := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hd]
  omega

/-- Spin adjustment downwards spread over **two** traversals of the stretch: this is the
case `N = 2` of the proof of Lemma 5.14 (`lem:twoodd`).  The first number of turns can be
taken `≤ t`, and `< t` as soon as `D > 0`. -/
theorem exists_turns_down (Str : Stretch k c) {D : ℕ} (hdvd : Str.ell ∣ D)
    (hD : D ≤ 2 * (Str.tt * Str.ell)) :
    ∃ u1 u2, u1 * Str.ell + u2 * Str.ell + D = 2 * (Str.tt * Str.ell) ∧
      u1 ≤ Str.tt ∧ (0 < D → u1 < Str.tt) := by
  obtain ⟨d, rfl⟩ := hdvd
  have hell := Str.hell
  have htt := Str.htt
  have hcomm : Str.ell * d = d * Str.ell := Nat.mul_comm _ _
  have hd2 : d ≤ 2 * Str.tt := by
    by_contra hcon
    push_neg at hcon
    have hle : (2 * Str.tt + 1) * Str.ell ≤ d * Str.ell := Nat.mul_le_mul (by omega) (le_refl _)
    have hex : (2 * Str.tt + 1) * Str.ell = 2 * (Str.tt * Str.ell) + Str.ell := by ring
    omega
  rcases Nat.le_total d Str.tt with h | h
  · refine ⟨Str.tt - d, Str.tt, ?_, by omega, ?_⟩
    · have h1 : (Str.tt - d) * Str.ell + d * Str.ell = Str.tt * Str.ell := by
        rw [← Nat.add_mul, Nat.sub_add_cancel h]
      omega
    · intro hpos
      have hd0 : 0 < d := by
        rcases Nat.eq_zero_or_pos d with rfl | hh
        · simp at hpos
        · exact hh
      omega
  · refine ⟨0, 2 * Str.tt - d, ?_, by omega, fun _ => by omega⟩
    have h1 : (2 * Str.tt - d) * Str.ell + d * Str.ell = 2 * Str.tt * Str.ell := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hd2]
    have h2 : 2 * Str.tt * Str.ell = 2 * (Str.tt * Str.ell) := by ring
    simp only [Nat.zero_mul, Nat.zero_add]
    omega

/-! ### The letters compared at the junctions -/

/-- A letter read at a position outside the run window `[k,2k+5]` differs from a letter
read inside it.  This is the non-triviality remark of Section 4 of
`ane-vs-an-separation-v4_1.tex` in the form used in Lemma 5.14 (`lem:twoodd`). -/
theorem zw_run_ne (hk : 3 ≤ k) {B t : ℕ} (hB : B < k ∨ 2 * k + 6 ≤ B)
    (h1 : k ≤ t) (h2 : t ≤ 2 * k + 5) : zw k B ≠ zw k t := by
  rcases hB with h | h
  · rw [zw_a h]
    rcases (by omega : t < 2 * k + 5 ∨ t = 2 * k + 5) with ht | ht
    · rw [zw_b h1 ht]; simp
    · rw [zw_c ht]; simp
  · have hBl : zw k B = Ltr.a (B - (2 * k + 5)) ∨ zw k B = Ltr.d ∨ zw k B = Ltr.e := by
      rcases (by omega : B < 3 * k + 5 ∨ B = 3 * k + 5 ∨ 3 * k + 6 ≤ B) with h' | h' | h'
      · exact Or.inl (zw_a' h h')
      · exact Or.inr (Or.inl (zw_d (by omega) h'))
      · refine Or.inr (Or.inr ?_)
        simp only [zw]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]
    rcases (by omega : t < 2 * k + 5 ∨ t = 2 * k + 5) with ht | ht
    · rw [zw_b h1 ht]
      rcases hBl with h' | h' | h' <;> rw [h'] <;> simp
    · rw [zw_c ht]
      rcases hBl with h' | h' | h' <;> rw [h'] <;> simp

/-! ### The three non-triviality tests -/

/-- **Lemma 5.14 (`lem:twoodd`), first non-triviality test.**  A candidate path
`W[0,A] · σ · ρ` whose first segment is a genuine walk segment differs from `W` as soon
as the first edge of `σ` carries a letter different from `z_A`: this is the comparison
"the first junction of `π_A` compares the letters `z_{α₁}, z_{α₂}`". -/
theorem chord_path_plain (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {A B L2 L3 : ℕ} {τ2 τ3 : ℕ → ℕ} {s : S} (hAn : A ≤ 3 * k + 7)
    (h2 : Seg k c (c A) s L2 τ2) (h3 : Seg k c s (c (3 * k + 7)) L3 τ3)
    (hL2 : 0 < L2) (hτ2 : τ2 0 = B) (hlen : A + (L2 + L3) = 3 * k + 7)
    (hne : zw k B ≠ zw k A) : False := by
  have s0 : Seg k c (c 0) (c A) A (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ A by omega) hAn
    simpa using h
  have hall := seg_cat s0 (seg_cat h2 h3)
  rw [hlen] at hall
  refine no_second_path hk huaw hall (j := A) (by omega) ?_
  have hv : cat A (fun t => 0 + t) (cat L2 τ2 τ3) A = B := by
    rw [cat_ge (by omega), Nat.sub_self, cat_lt hL2, hτ2]
  rw [hv]
  exact hne

/-- **Lemma 5.14 (`lem:twoodd`), second non-triviality test.**  If the first segment of
the candidate is a spin adjusted traversal `W[0,A]⟨u⟩` ending inside the run window, the
junction sits at a position of the run window, where `W` reads `b` or `c`; so the
candidate differs from `W` as soon as the next edge is a prefix or tail edge. -/
theorem chord_path_spin (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {A B L2 L3 u : ℕ} {τ2 τ3 : ℕ → ℕ} {s : S}
    (hqA : Str.q ≤ A) (hAn : A ≤ 2 * k + 5)
    (h2 : Seg k c (c A) s L2 τ2) (h3 : Seg k c s (c (3 * k + 7)) L3 τ3)
    (hL2 : 0 < L2) (hτ2 : τ2 0 = B) (hB : B < k ∨ 2 * k + 6 ≤ B)
    (hlen : Str.slen 0 A u + (L2 + L3) = 3 * k + 7)
    (hJ : Str.slen 0 A u ≤ 2 * k + 5) : False := by
  obtain ⟨τ1, h1, -, -, -⟩ := spanSegI Str (Nat.zero_le _) hqA (by omega) u
  have hall := seg_cat h1 (seg_cat h2 h3)
  rw [hlen] at hall
  have hJk : k ≤ Str.slen 0 A u := by
    have := Str.hp
    simp only [Stretch.slen]
    omega
  refine no_second_path hk huaw hall (j := Str.slen 0 A u) (by omega) ?_
  have hv : cat (Str.slen 0 A u) τ1 (cat L2 τ2 τ3) (Str.slen 0 A u) = B := by
    rw [cat_ge (by omega), Nat.sub_self, cat_lt hL2, hτ2]
  rw [hv]
  exact zw_run_ne hk hB hJk hJ

/-- **Lemma 5.14 (`lem:twoodd`), third non-triviality test.**  If the first segment of the
candidate is a spin adjusted traversal `W[0,A]⟨u⟩` reaching into the tail, it contains the
`c`-edge `e_{2k+5}`, whose position has been moved by the spin adjustment; so the
candidate reads `c` where `W` does not. -/
theorem chord_path_cedge (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {A L2 L3 u : ℕ} {τ2 τ3 : ℕ → ℕ} {s : S}
    (hA6 : 2 * k + 6 ≤ A) (hAn : A ≤ 3 * k + 7)
    (h2 : Seg k c (c A) s L2 τ2) (h3 : Seg k c s (c (3 * k + 7)) L3 τ3)
    (hlen : Str.slen 0 A u + (L2 + L3) = 3 * k + 7)
    (hne : Str.p + (u * Str.ell + Str.roff) ≠ Str.q) : False := by
  have hq := Str.hq
  obtain ⟨τ1, h1, -, -, hlast⟩ := spanSegI Str (Nat.zero_le _) (by omega) hAn u
  have hall := seg_cat h1 (seg_cat h2 h3)
  rw [hlen] at hall
  set P := Str.p + (u * Str.ell + Str.roff) + (2 * k + 5 - Str.q) with hP
  have hPval : τ1 P = 2 * k + 5 := by
    have h := hlast (2 * k + 5 - Str.q) (by omega)
    rw [Nat.sub_zero] at h
    rw [hP]
    rw [h]
    omega
  have hPlt : P < Str.slen 0 A u := by
    simp only [Stretch.slen]
    omega
  refine no_second_path hk huaw hall (j := P) (by omega) ?_
  have hv : cat (Str.slen 0 A u) τ1 (cat L2 τ2 τ3) P = 2 * k + 5 := by
    rw [cat_lt hPlt, hPval]
  rw [hv, zw_c rfl]
  have hPne : P ≠ 2 * k + 5 := by omega
  intro hcon
  rcases (by omega : P < k ∨ (k ≤ P ∧ P < 2 * k + 5) ∨ 2 * k + 6 ≤ P) with h | h | h
  · rw [zw_a h] at hcon; simp at hcon
  · rw [zw_b h.1 h.2] at hcon; simp at hcon
  · rcases (by omega : P < 3 * k + 5 ∨ P = 3 * k + 5 ∨ 3 * k + 6 ≤ P) with h' | h' | h'
    · rw [zw_a' h h'] at hcon; simp at hcon
    · rw [zw_d (by omega) h'] at hcon; simp at hcon
    · rw [show zw k P = Ltr.e by
        simp only [zw]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]] at hcon
      simp at hcon

/-! ### The seven shapes of the candidate paths of Lemma 5.14 (`lem:twoodd`)

Throughout, `a = (a₁,a₂)` and `b = (b₁,b₂)` are the two chords, and the candidate is
either `π_A = W[0,a₁] W[a₂,b₂] W[b₁,n]` or `π_D = W[0,a₂] W[a₁,b₁] W[b₂,n]`.  The seven
lemmas below differ only in which of the three segments contain the stretch `S` (and hence
carry a spin adjustment) and in which non-triviality test is used. -/

/-- **Lemma 5.14 (`lem:twoodd`)**, the candidate `π_A` with a spin adjustment in the last
segment only (`N = 1`).  Used when the interval of `b` starts before the stretch and the
interval `[a₂,b₂]` misses it. -/
theorem chord_pair_A1 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ b₁ b₂ : ℕ}
    (ha : a₁ < a₂) (hb : b₁ < b₂) (hab : a₂ < b₂) (hb2 : b₂ ≤ 3 * k + 7)
    (hb1 : b₁ ≤ Str.p) (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂)
    (hltr : zw k a₂ ≠ zw k a₁)
    (hd1 : Str.ell ∣ ((a₂ - a₁) - (b₂ - b₁))) (hd2 : Str.ell ∣ ((b₂ - b₁) - (a₂ - a₁)))
    (hcap : (b₂ - b₁) - (a₂ - a₁) ≤ Str.tt * Str.ell) : False := by
  have hq := Str.hq
  have hp := Str.hp
  have hqn : Str.q ≤ 3 * k + 7 := by omega
  obtain ⟨u, hu⟩ : ∃ u, u * Str.ell + (b₂ - b₁) = Str.tt * Str.ell + (a₂ - a₁) := by
    rcases Nat.le_total (b₂ - b₁) (a₂ - a₁) with h | h
    · obtain ⟨u, hu⟩ := exists_turn_up Str hd1
      exact ⟨u, by omega⟩
    · obtain ⟨u, hu⟩ := exists_turn_down Str hd2 hcap
      exact ⟨u, by omega⟩
  have hs := Str.slen_eq hb1 hqn u
  have hlen : a₁ + ((b₂ - a₂) + Str.slen b₁ (3 * k + 7) u) = 3 * k + 7 := by omega
  have h2 : Seg k c (c a₂) (c b₂) (b₂ - a₂) (fun t => a₂ + t) := segW c (by omega) hb2
  rw [← hca] at h2
  obtain ⟨τ3, h3⟩ := Str.spanSeg hb1 hqn (le_refl _) u
  rw [hcb] at h3
  exact chord_path_plain hk huaw (by omega) h2 h3 (by omega) rfl hlen hltr

/-- **Lemma 5.14 (`lem:twoodd`)**, the candidate `π_A` with a spin adjustment in the two
last segments (`N = 2`).  Used when `a` is early and `b` is wide. -/
theorem chord_pair_A2 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ b₁ b₂ : ℕ}
    (ha : a₁ < a₂) (hb : b₁ < b₂) (ha2p : a₂ < Str.p) (hqb2 : Str.q ≤ b₂)
    (hb2 : b₂ ≤ 3 * k + 7) (hb1 : b₁ ≤ Str.p) (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂)
    (hltr : zw k a₂ ≠ zw k a₁) (hle : a₂ - a₁ ≤ b₂ - b₁)
    (hdvd : Str.ell ∣ ((b₂ - b₁) - (a₂ - a₁)))
    (hcap : (b₂ - b₁) - (a₂ - a₁) ≤ 2 * (Str.tt * Str.ell)) : False := by
  have hq := Str.hq
  have hp := Str.hp
  have hqn : Str.q ≤ 3 * k + 7 := by omega
  have hpq : Str.p ≤ Str.q := by have := Str.hlen; omega
  obtain ⟨u2, u3, hu, -, -⟩ := exists_turns_down Str hdvd hcap
  have hs2 := Str.slen_eq (le_of_lt ha2p) hqb2 u2
  have hs3 := Str.slen_eq hb1 hqn u3
  have hlen : a₁ + (Str.slen a₂ b₂ u2 + Str.slen b₁ (3 * k + 7) u3) = 3 * k + 7 := by omega
  obtain ⟨τ2, h2, hτ20, -, -⟩ := spanSegI Str (le_of_lt ha2p) hqb2 hb2 u2
  rw [← hca] at h2
  obtain ⟨τ3, h3⟩ := Str.spanSeg hb1 hqn (le_refl _) u3
  rw [hcb] at h3
  refine chord_path_plain hk huaw (by omega) h2 h3 ?_ ?_ hlen hltr
  · simp only [Stretch.slen]; omega
  · simpa using hτ20 0 (by omega)

/-- **Lemma 5.14 (`lem:twoodd`)**, the candidate `π_A` with a spin adjustment in the
middle segment only.  Used when `a` is early and `b` is late. -/
theorem chord_pair_A3 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ b₁ b₂ : ℕ}
    (ha : a₁ < a₂) (hb : b₁ < b₂) (ha2p : a₂ < Str.p) (hqb2 : Str.q ≤ b₂)
    (hab : a₂ ≤ b₂) (hb2 : b₂ ≤ 3 * k + 7) (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂)
    (hltr : zw k a₂ ≠ zw k a₁)
    (hd1 : Str.ell ∣ ((a₂ - a₁) - (b₂ - b₁))) (hd2 : Str.ell ∣ ((b₂ - b₁) - (a₂ - a₁)))
    (hcap : (b₂ - b₁) - (a₂ - a₁) ≤ Str.tt * Str.ell) : False := by
  have hq := Str.hq
  have hp := Str.hp
  obtain ⟨u, hu⟩ : ∃ u, u * Str.ell + (b₂ - b₁) = Str.tt * Str.ell + (a₂ - a₁) := by
    rcases Nat.le_total (b₂ - b₁) (a₂ - a₁) with h | h
    · obtain ⟨u, hu⟩ := exists_turn_up Str hd1
      exact ⟨u, by omega⟩
    · obtain ⟨u, hu⟩ := exists_turn_down Str hd2 hcap
      exact ⟨u, by omega⟩
  have hs := Str.slen_eq (le_of_lt ha2p) hqb2 u
  have hlen : a₁ + (Str.slen a₂ b₂ u + (3 * k + 7 - b₁)) = 3 * k + 7 := by omega
  obtain ⟨τ2, h2, hτ20, -, -⟩ := spanSegI Str (le_of_lt ha2p) hqb2 hb2 u
  rw [← hca] at h2
  have h3 : Seg k c (c b₁) (c (3 * k + 7)) (3 * k + 7 - b₁) (fun t => b₁ + t) :=
    segW c (by omega) (by omega)
  rw [hcb] at h3
  refine chord_path_plain hk huaw (by omega) h2 h3 ?_ ?_ hlen hltr
  · simp only [Stretch.slen]; omega
  · simpa using hτ20 0 (by omega)

/-- **Lemma 5.14 (`lem:twoodd`)**, the candidate `π_A` whose first segment already
contains the stretch (`a` is late), with a spin adjustment in the first and the last
segment (`N = 2`).  Used when `a` is late and `b` is a wide tail chord. -/
theorem chord_pair_A4 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ b₁ b₂ : ℕ}
    (hqa1 : Str.q ≤ a₁) (ha1 : a₁ ≤ 2 * k + 5) (ha : a₁ < a₂) (ha2 : 2 * k + 6 ≤ a₂)
    (hb : b₁ < b₂) (hab : a₂ < b₂) (hb2 : b₂ ≤ 3 * k + 7) (hb1 : b₁ ≤ Str.p)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂) (hle : a₂ - a₁ ≤ b₂ - b₁)
    (hdvd : Str.ell ∣ ((b₂ - b₁) - (a₂ - a₁)))
    (hcap : (b₂ - b₁) - (a₂ - a₁) ≤ 2 * (Str.tt * Str.ell)) : False := by
  have hq := Str.hq
  have hp := Str.hp
  have hqn : Str.q ≤ 3 * k + 7 := by omega
  obtain ⟨u1, u3, hu, hu1, -⟩ := exists_turns_down Str hdvd hcap
  have hmul : u1 * Str.ell ≤ Str.tt * Str.ell := Nat.mul_le_mul hu1 (le_refl _)
  have hs1 := Str.slen_eq (Nat.zero_le _) hqa1 u1
  have hs3 := Str.slen_eq hb1 hqn u3
  have hlen : Str.slen 0 a₁ u1 + ((b₂ - a₂) + Str.slen b₁ (3 * k + 7) u3) = 3 * k + 7 := by
    omega
  have h2 : Seg k c (c a₂) (c b₂) (b₂ - a₂) (fun t => a₂ + t) := segW c (by omega) hb2
  rw [← hca] at h2
  obtain ⟨τ3, h3⟩ := Str.spanSeg hb1 hqn (le_refl _) u3
  rw [hcb] at h3
  exact chord_path_spin hk huaw Str hqa1 ha1 h2 h3 (by omega) rfl (Or.inr ha2) hlen
    (by omega)

/-- **Lemma 5.14 (`lem:twoodd`)**, the candidate `π_A` with a spin adjustment in the first
segment only.  Used when both chords are late. -/
theorem chord_pair_A5 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ b₁ b₂ : ℕ}
    (hqa1 : Str.q ≤ a₁) (ha1 : a₁ ≤ 2 * k + 5) (ha : a₁ < a₂) (ha2 : 2 * k + 6 ≤ a₂)
    (hb : b₁ < b₂) (hab : a₂ < b₂) (hb2 : b₂ ≤ 3 * k + 7) (hb1 : b₁ ≤ 2 * k + 5)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂)
    (hd1 : Str.ell ∣ ((a₂ - a₁) - (b₂ - b₁))) (hd2 : Str.ell ∣ ((b₂ - b₁) - (a₂ - a₁)))
    (hcap : (b₂ - b₁) - (a₂ - a₁) ≤ Str.tt * Str.ell) : False := by
  have hq := Str.hq
  have hp := Str.hp
  obtain ⟨u, hu⟩ : ∃ u, u * Str.ell + (b₂ - b₁) = Str.tt * Str.ell + (a₂ - a₁) := by
    rcases Nat.le_total (b₂ - b₁) (a₂ - a₁) with h | h
    · obtain ⟨u, hu⟩ := exists_turn_up Str hd1
      exact ⟨u, by omega⟩
    · obtain ⟨u, hu⟩ := exists_turn_down Str hd2 hcap
      exact ⟨u, by omega⟩
  have hs1 := Str.slen_eq (Nat.zero_le _) hqa1 u
  have hlen : Str.slen 0 a₁ u + ((b₂ - a₂) + (3 * k + 7 - b₁)) = 3 * k + 7 := by omega
  have h2 : Seg k c (c a₂) (c b₂) (b₂ - a₂) (fun t => a₂ + t) := segW c (by omega) hb2
  rw [← hca] at h2
  have h3 : Seg k c (c b₁) (c (3 * k + 7)) (3 * k + 7 - b₁) (fun t => b₁ + t) :=
    segW c (by omega) (by omega)
  rw [hcb] at h3
  exact chord_path_spin hk huaw Str hqa1 ha1 h2 h3 (by omega) rfl (Or.inr ha2) hlen
    (by omega)

/-- **Lemma 5.14 (`lem:twoodd`)**, the candidate `π_D` whose first segment ends inside the
run window (`a` is a wide prefix chord), with a spin adjustment in the first two segments
(`N = 2`).  Used when `a` is a wide prefix chord and `b` is late. -/
theorem chord_pair_D1 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ b₁ b₂ : ℕ}
    (ha1k : a₁ < k) (hqa2 : Str.q ≤ a₂) (ha2 : a₂ ≤ 2 * k + 5) (ha : a₁ < a₂)
    (hqb1 : Str.q ≤ b₁) (hb : b₁ < b₂) (hb2 : b₂ ≤ 3 * k + 7)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂) (hge : b₂ - b₁ ≤ a₂ - a₁)
    (hdvd : Str.ell ∣ ((a₂ - a₁) - (b₂ - b₁)))
    (hcap : (a₂ - a₁) - (b₂ - b₁) ≤ 2 * (Str.tt * Str.ell)) : False := by
  have hq := Str.hq
  have hp := Str.hp
  have ha1p : a₁ ≤ Str.p := by omega
  have hpq : Str.p ≤ Str.q := by have := Str.hlen; omega
  obtain ⟨u1, u2, hu, hu1, -⟩ := exists_turns_down Str hdvd hcap
  have hmul : u1 * Str.ell ≤ Str.tt * Str.ell := Nat.mul_le_mul hu1 (le_refl _)
  have hs1 := Str.slen_eq (Nat.zero_le _) hqa2 u1
  have hs2 := Str.slen_eq ha1p hqb1 u2
  have hlen : Str.slen 0 a₂ u1 + (Str.slen a₁ b₁ u2 + (3 * k + 7 - b₂)) = 3 * k + 7 := by
    omega
  obtain ⟨τ2, h2, hτ20, -, -⟩ := spanSegI Str ha1p hqb1 (by omega) u2
  rw [hca] at h2
  have h3 : Seg k c (c b₂) (c (3 * k + 7)) (3 * k + 7 - b₂) (fun t => b₂ + t) :=
    segW c (by omega) (by omega)
  rw [← hcb] at h3
  refine chord_path_spin hk huaw Str hqa2 ha2 h2 h3 ?_ ?_ (Or.inl ha1k) hlen (by omega)
  · simp only [Stretch.slen]; omega
  · simpa using hτ20 0 (by omega)

/-- **Lemma 5.14 (`lem:twoodd`)**, the candidate `π_D` whose first segment reaches into the
tail (`a` is a wide tail chord), so that the moved `c`-edge provides the non-triviality.
Used when `a` is a wide tail chord and `b` is late. -/
theorem chord_pair_D2 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ b₁ b₂ : ℕ}
    (ha1p : a₁ ≤ Str.p) (ha26 : 2 * k + 6 ≤ a₂) (ha2 : a₂ ≤ 3 * k + 7)
    (hqb1 : Str.q ≤ b₁) (hb : b₁ < b₂) (hb2 : b₂ ≤ 3 * k + 7)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂)
    (hdvd : Str.ell ∣ ((a₂ - a₁) - (b₂ - b₁)))
    (hpos : 0 < (a₂ - a₁) - (b₂ - b₁))
    (hcap : (a₂ - a₁) - (b₂ - b₁) ≤ 2 * (Str.tt * Str.ell)) : False := by
  have hq := Str.hq
  have hp := Str.hp
  have hlenS := Str.hlen
  have hell := Str.hell
  obtain ⟨u1, u2, hu, hu1, hu1'⟩ := exists_turns_down Str hdvd hcap
  have hu1lt := hu1' hpos
  have hmul : (u1 + 1) * Str.ell ≤ Str.tt * Str.ell := Nat.mul_le_mul (by omega) (le_refl _)
  have hexp : (u1 + 1) * Str.ell = u1 * Str.ell + Str.ell := by ring
  have hs1 := Str.slen_eq (Nat.zero_le _) (show Str.q ≤ a₂ by omega) u1
  have hs2 := Str.slen_eq ha1p hqb1 u2
  have hlen : Str.slen 0 a₂ u1 + (Str.slen a₁ b₁ u2 + (3 * k + 7 - b₂)) = 3 * k + 7 := by
    omega
  obtain ⟨τ2, h2, -, -, -⟩ := spanSegI Str ha1p hqb1 (by omega) u2
  rw [hca] at h2
  have h3 : Seg k c (c b₂) (c (3 * k + 7)) (3 * k + 7 - b₂) (fun t => b₂ + t) :=
    segW c (by omega) (by omega)
  rw [← hcb] at h3
  exact chord_path_cedge hk huaw Str ha26 ha2 h2 h3 hlen (by omega)

/-! ### Lemma 5.14 (`lem:twoodd`): two chords of odd length -/

/-- The position of a bridge chord `(x,y)` relative to the stretch `S = [p,q]`
(Section 5.5, `sec:bridges`): it is *early* (a prefix bridge whose run visit lies on the
approach), *wide* (a prefix bridge whose run visit lies on the departure, or a tail bridge
whose run visit lies on the approach) or *late* (a tail bridge whose run visit lies on the
departure).  The length bounds are `eq:bridgelen`, in the numerical form available for
`ℓ = 2`: `L ≤ 10` for an early or late chord and `k+2 ≤ L ≤ k+11` for a wide one. -/
def BridgeChordKind (Str : Stretch k c) (x y : ℕ) : Prop :=
  (x < k ∧ k ≤ y ∧ y < Str.p ∧ y - x ≤ 10) ∨
  (x < k ∧ Str.q < y ∧ y ≤ 2 * k + 5 ∧ k + 2 ≤ y - x ∧ y - x ≤ k + 11) ∨
  (k ≤ x ∧ x < Str.p ∧ 2 * k + 6 ≤ y ∧ y ≤ 3 * k + 5 ∧ k + 2 ≤ y - x ∧ y - x ≤ k + 11) ∨
  (Str.q < x ∧ x ≤ 2 * k + 5 ∧ 2 * k + 6 ≤ y ∧ y ≤ 3 * k + 5 ∧ y - x ≤ 10)

/-- **Lemma 5.14 (Two odd chords, `lem:twoodd`)**, the ordered form: the case analysis of
the source, after the chords have been named so that `a₂ < b₂`.  Six positions of the two
chords are possible, and in each of them one of the candidate paths `π_A`, `π_D` of the
source, completed by a spin adjustment, is a second accepting path of length `n`. -/
theorem two_bridge_chords_ordered (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hT : k ≤ Str.tt * Str.ell)
    {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ < a₂) (hb : b₁ < b₂)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂) (hltr : zw k a₂ ≠ zw k a₁)
    (hoa : (a₂ - a₁) % 2 = 1) (hob : (b₂ - b₁) % 2 = 1)
    (ka : BridgeChordKind Str a₁ a₂) (kb : BridgeChordKind Str b₁ b₂)
    (hord : a₂ < b₂) : False := by
  have hp := Str.hp
  have hq := Str.hq
  have hlenS := Str.hlen
  have hpq : Str.p ≤ Str.q := by omega
  simp only [BridgeChordKind] at ka kb
  rcases ka with ka | ka | ka | ka
  · -- `a` is early
    rcases kb with kb | kb | kb | kb
    · exact chord_pair_A1 (by omega) huaw Str ha hb hord (by omega) (by omega) hca hcb
        hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A2 (by omega) huaw Str ha hb (by omega) (by omega) (by omega)
        (by omega) hca hcb hltr (by omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A2 (by omega) huaw Str ha hb (by omega) (by omega) (by omega)
        (by omega) hca hcb hltr (by omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A3 (by omega) huaw Str ha hb (by omega) (by omega) (by omega)
        (by omega) hca hcb hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
  · -- `a` is a wide prefix chord
    rcases kb with kb | kb | kb | kb
    · exact absurd hord (by omega)
    · exact chord_pair_A1 (by omega) huaw Str ha hb hord (by omega) (by omega) hca hcb
        hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A1 (by omega) huaw Str ha hb hord (by omega) (by omega) hca hcb
        hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_D1 (by omega) huaw Str (by omega) (by omega) (by omega) ha
        (by omega) hb (by omega) hca hcb (by omega) (by rw [hell]; omega) (by omega)
  · -- `a` is a wide tail chord
    rcases kb with kb | kb | kb | kb
    · exact absurd hord (by omega)
    · exact absurd hord (by omega)
    · exact chord_pair_A1 (by omega) huaw Str ha hb hord (by omega) (by omega) hca hcb
        hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_D2 (by omega) huaw Str (by omega) (by omega) (by omega)
        (by omega) hb (by omega) hca hcb (by rw [hell]; omega) (by omega) (by omega)
  · -- `a` is late
    rcases kb with kb | kb | kb | kb
    · exact absurd hord (by omega)
    · exact absurd hord (by omega)
    · exact chord_pair_A4 (by omega) huaw Str (by omega) (by omega) ha (by omega) hb
        hord (by omega) (by omega) hca hcb (by omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A5 (by omega) huaw Str (by omega) (by omega) ha (by omega) hb
        hord (by omega) (by omega) hca hcb (by rw [hell]; omega) (by rw [hell]; omega)
        (by omega)

/-- **Lemma 5.14 (Two odd chords, `lem:twoodd`)**: for `ℓ = 2`, two chords of odd length
whose right endpoints differ and whose lengths differ make `W` non uniquely accepting.
This is the form in which parts (a) and (b) of the source are used. -/
theorem two_bridge_chords (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hT : k ≤ Str.tt * Str.ell)
    {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ < a₂) (hb : b₁ < b₂)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂)
    (hltra : zw k a₂ ≠ zw k a₁) (hltrb : zw k b₂ ≠ zw k b₁)
    (hoa : (a₂ - a₁) % 2 = 1) (hob : (b₂ - b₁) % 2 = 1) (hne : a₂ ≠ b₂)
    (ka : BridgeChordKind Str a₁ a₂) (kb : BridgeChordKind Str b₁ b₂) : False := by
  rcases Nat.lt_or_ge a₂ b₂ with h | h
  · exact two_bridge_chords_ordered hk huaw Str hell hT ha hb hca hcb hltra hoa hob ka kb h
  · exact two_bridge_chords_ordered hk huaw Str hell hT hb ha hcb hca hltrb hob hoa kb ka
      (by omega)

end

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- **The chord of a bridge**, for `ℓ = 2`.  By Lemma 5.10(e) (`lem:positions`) the chord
of a bridge is `(j,τ)` with `j ∈ J_R` (prefix bridge) or `(τ, 2k+6+j')` with `j' ∈ J_L`
(tail bridge), the run visit `τ` lying outside the stretch by the maximality of the
stretch (Step 1 of Lemma 5.3, `lem:gamma`).  Its position relative to the stretch and its
length are as recorded in `BridgeChordKind` (`eq:bridgelen`), its length is odd by
Lemma 5.13 (Bridge parity, `lem:bridgeparity`), and its two endpoint letters differ (a
run letter `b` or `c` against a prefix or tail letter). -/
theorem bridge_chord_data (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hd0le : Str.d0 + Str.ell ≤ 7)
    (hbs : bridgeCount k c + singleCount k c + 2 * Str.ell ≤ 8)
    (hmax : ∀ u, u ≤ 3 * k + 7 →
      (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) → Str.p ≤ u ∧ u ≤ Str.q)
    {y : S} (hyo : y ∈ onceSet k c) (hyr : (rvis k c y).card = 1) :
    ∃ x z, x < z ∧ c x = y ∧ c z = y ∧ (z - x) % 2 = 1 ∧ zw k z ≠ zw k x ∧
      BridgeChordKind Str x z := by
  classical
  rw [onceSet, Finset.mem_filter] at hyo
  obtain ⟨-, hnv1⟩ := hyo
  obtain ⟨j, hjset⟩ := Finset.card_eq_one.1 hnv1
  obtain ⟨tau, htset⟩ := Finset.card_eq_one.1 hyr
  have hjmem : j ∈ nvis k c y := by rw [hjset]; exact Finset.mem_singleton_self j
  have htmem : tau ∈ rvis k c y := by rw [htset]; exact Finset.mem_singleton_self tau
  rw [mem_nvis_iff] at hjmem
  obtain ⟨⟨hjn, hjr⟩, hcj⟩ := hjmem
  simp only [rvis, Finset.mem_filter, runTimes, Finset.mem_Icc] at htmem
  obtain ⟨⟨htau1, htau2⟩, hct⟩ := htmem
  have honly : ∀ t, t < 3 * k + 8 → ¬ (k ≤ t ∧ t ≤ 2 * k + 5) → c t = y → t = j := by
    intro t h1 h2 h3
    have ht : t ∈ nvis k c y := mem_nvis_iff.2 ⟨⟨h1, h2⟩, h3⟩
    rw [hjset, Finset.mem_singleton] at ht
    exact ht
  obtain ⟨i0, hi0k, halign0⟩ := exists_aligned_index hk huaw Str (by omega) hd0le hbs
  have hAne : (alignedSet k c).Nonempty := ⟨i0, mem_alignedSet.2 ⟨hi0k, halign0⟩⟩
  have hI := alignedSet_interval (by omega : 3 ≤ k) huaw hAne
  have hi1a := mem_alignedSet.1 (Finset.min'_mem (alignedSet k c) hAne)
  have hi2a := mem_alignedSet.1 (Finset.max'_mem (alignedSet k c) hAne)
  have hbc := blockCount_bound hk huaw Str hd0le hi0k halign0
  have hmx := alignedSet_card_le_max (k := k) (c := c) hAne
  have hmn := alignedSet_card_add_min_le (k := k) (c := c) hAne
  have hdd := Str.d0_add
  have hpk := Str.hp
  have hqk := Str.hq
  have hd0p : Str.p - k ≤ Str.d0 := by simp only [Stretch.d0]; omega
  have hd0q : 2 * k + 5 - Str.q ≤ Str.d0 := by simp only [Stretch.d0]; omega
  rw [hell] at hbc hbs hd0le
  have hchord : c j = c tau := by rw [hcj, hct]
  -- the run visit lies outside the stretch (maximality of the stretch)
  have houts : tau < Str.p ∨ Str.q < tau := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hcp, hcq⟩ := hcon
    obtain ⟨x, hx1, hx2, hx3⟩ := stretch_state Str hcp hcq
    have hj2 := hmax j (by omega) ⟨x, hx1, hx2, by rw [hx3, hct, hcj]⟩
    omega
  rcases (by omega : j < k ∨ 2 * k + 6 ≤ j) with hjcase | hjcase
  · -- prefix bridge
    have hjgt : (alignedSet k c).max' hAne < j := by
      rcases Nat.lt_or_ge j ((alignedSet k c).min' hAne) with h | h
      · exact (positions_prefix_bridge (by omega) huaw hi1a.1 hi1a.2 h htau1 htau2
          hchord).elim
      · rcases Nat.lt_or_ge ((alignedSet k c).max' hAne) j with h2 | h2
        · exact h2
        · exfalso
          have heq := (mem_alignedSet.1 (hI j h h2)).2
          have := honly (2 * k + 6 + j) (by omega) (by omega) (by rw [← heq, hcj])
          omega
    refine ⟨j, tau, by omega, hcj, hct, ?_, ?_, ?_⟩
    · by_contra hcon
      have hdvd : Str.ell ∣ (tau - j) := by rw [hell]; omega
      rcases houts with h | h
      · exact bridge_short_prefix (by omega) huaw Str hjcase htau1 htau2 hchord hdvd
          (by omega)
      · exact bridge_span_prefix (by omega) huaw Str hjcase (by omega) htau2 hchord hdvd
          (by omega)
    · exact (zw_run_ne (by omega) (Or.inl hjcase) htau1 htau2).symm
    · rcases houts with h | h
      · exact Or.inl ⟨hjcase, htau1, h, by omega⟩
      · exact Or.inr (Or.inl ⟨hjcase, h, htau2, by omega, by omega⟩)
  · -- tail bridge
    have hjeq : 2 * k + 6 + (j - (2 * k + 6)) = j := by omega
    have hnotu : j - (2 * k + 6) < k := by
      by_contra hcon
      exact positions_u_not_bridge (by omega) huaw hi1a.1 hi1a.2 htau1 htau2
        (show j = 3 * k + 6 ∨ j = 3 * k + 7 by omega) hchord.symm
    have hjlt : j - (2 * k + 6) < (alignedSet k c).min' hAne := by
      rcases Nat.lt_or_ge ((alignedSet k c).max' hAne) (j - (2 * k + 6)) with h | h
      · exact (positions_tail_bridge (by omega) huaw hi2a.1 hi2a.2 h hnotu htau1 htau2
          (by rw [hjeq]; exact hchord.symm)).elim
      · rcases Nat.lt_or_ge (j - (2 * k + 6)) ((alignedSet k c).min' hAne) with h2 | h2
        · exact h2
        · exfalso
          have heq := (mem_alignedSet.1 (hI _ h2 h)).2
          have := honly (j - (2 * k + 6)) (by omega) (by omega) (by rw [heq, hjeq, hcj])
          omega
    refine ⟨tau, j, by omega, hct, hcj, ?_, ?_, ?_⟩
    · by_contra hcon
      have hdvd : Str.ell ∣ (2 * k + 6 + (j - (2 * k + 6)) - tau) := by
        rw [hell, hjeq]; omega
      rcases houts with h | h
      · exact bridge_span_tail (by omega) huaw Str (by omega) (by omega)
          (by rw [hjeq]; exact hchord.symm) hdvd (by rw [hjeq]; omega)
      · exact bridge_short_tail (by omega) huaw Str (by omega) htau2
          (by rw [hjeq]; exact hchord.symm) hdvd (by rw [hjeq]; omega)
    · exact zw_run_ne (by omega) (Or.inr hjcase) htau1 htau2
    · rcases houts with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨htau1, h, hjcase, by omega, by omega, by omega⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h, htau2, hjcase, by omega, by omega⟩))

/-- **Lemma 5.14(a) (Two odd chords, `lem:twoodd`)**: for `ℓ = 2` there is at most one
bridge.  Two bridges are two distinct states, so their chords have four distinct
endpoints; both chords have odd length by Lemma 5.13 (`lem:bridgeparity`), and
`two_bridge_chords` then produces a second accepting path. -/
theorem bridgeCount_le_one_of_two (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hd0le : Str.d0 + Str.ell ≤ 7)
    (hbs : bridgeCount k c + singleCount k c + 2 * Str.ell ≤ 8)
    (hmax : ∀ u, u ≤ 3 * k + 7 →
      (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) → Str.p ≤ u ∧ u ≤ Str.q) :
    bridgeCount k c ≤ 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨ya, hya, yb, hyb, hyab⟩ := Finset.one_lt_card.1 hcon
  rw [Finset.mem_filter] at hya hyb
  obtain ⟨a₁, a₂, ha, hca1, hca2, hoa, hltra, ka⟩ :=
    bridge_chord_data hk huaw Str hell hd0le hbs hmax hya.1 hya.2
  obtain ⟨b₁, b₂, hb, hcb1, hcb2, hob, hltrb, kb⟩ :=
    bridge_chord_data hk huaw Str hell hd0le hbs hmax hyb.1 hyb.2
  have hdd := Str.d0_add
  have hT : k ≤ Str.tt * Str.ell := by omega
  refine two_bridge_chords hk huaw Str hell hT ha hb (by rw [hca1, hca2])
    (by rw [hcb1, hcb2]) hltra hltrb hoa hob ?_ ka kb
  intro hne
  exact hyab (by rw [← hca2, hne, hcb2])

end

end AneVsAn
