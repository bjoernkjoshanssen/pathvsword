import RequestProject.WalkGamma

/-!
# Chord surgeries (Section 5.3 of `anevsanseparationv4.tex`)

Given the cycle `γ` and its stretch `S` (Lemma 5.3, `lem:gamma`), the *run-length set*
`T = d₀ + ℓ·ℤ≥0` records the lengths of the `b`-labelled paths `R⟨t'⟩` from `c_k` to
`c_{2k+5}` available in the walk graph.  Combining such a path with a skip or an insertion
of a chord produces a second accepting path of length `n`, which contradicts unique
acceptance.  This file formalizes the resulting surgeries: Lemma 5.6 (Narrow surgeries,
`lem:narrow`), Lemma 5.7 (Wide chords, `lem:wide`), Corollary 5.8 (`cor:foldloop`) and
Lemma 5.9 (Lassos, `lem:lasso`).
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-- The data of the cycle `γ` and its stretch `S = [p,q]` produced by Lemma 5.3
(`lem:gamma`): the walk is `ell`-periodic on `S`, and `S` consists of `tt` full turns of
`γ` plus `roff` further steps. -/
structure Stretch (k : ℕ) (c : ℕ → S) where
  /-- the length `ℓ = |γ|` of the cycle -/
  ell : ℕ
  /-- the left endpoint `k + α` of the stretch -/
  p : ℕ
  /-- the right endpoint `2k+5 - ω` of the stretch -/
  q : ℕ
  /-- the number `t` of full turns of `γ` inside the stretch -/
  tt : ℕ
  /-- the offset `r_off` -/
  roff : ℕ
  hell : 1 ≤ ell
  hp : k ≤ p
  hq : q ≤ 2 * k + 5
  htt : 1 ≤ tt
  hlen : p + tt * ell + roff = q
  hper : ∀ x, p ≤ x → x + ell ≤ q → c x = c (x + ell)

namespace Stretch

variable (Str : Stretch k c)

/-- The quantity `d₀ = α + ω + r_off` of Lemma 5.3 (`lem:gamma`). -/
def d0 : ℕ := (Str.p - k) + Str.roff + (2 * k + 5 - Str.q)

/-- `d₀ + t·ℓ = m = k+5` (Lemma 5.3, `lem:gamma`). -/
theorem d0_add : Str.d0 + Str.tt * Str.ell = k + 5 := by
  have h1 := Str.hlen
  have h2 := Str.hp
  have h3 := Str.hq
  simp only [d0]
  omega

/-- **Lemma 5.3(iii) (`lem:gamma`)**: for every `u`, a `b`-labelled path `R⟨d₀ + u·ℓ⟩`
from `c_k` to `c_{2k+5}` exists in the walk graph.  For `u = t` it is the run itself. -/
theorem runSeg (hk : 3 ≤ k) (u : ℕ) :
    ∃ τ, Seg k c (c k) (c (2 * k + 5)) (Str.d0 + u * Str.ell) τ := by
  obtain ⟨τ, hτ⟩ := runPath (k := k) (c := c) (p := Str.p) (q := Str.q) (ell := Str.ell)
    (tt := Str.tt) (roff := Str.roff) (τ₁ := k) (τ₂ := 2 * k + 5)
    Str.hell Str.hper Str.hlen Str.htt Str.hp Str.hq (by omega) u
  refine ⟨τ, ?_⟩
  have h1 := Str.hp
  have h2 := Str.hq
  have : Str.p - k + (u * Str.ell + Str.roff) + (2 * k + 5 - Str.q) = Str.d0 + u * Str.ell := by
    simp only [d0]; omega
  rwa [this] at hτ

/-- The length of the *spin adjusted* segment `W[x,y]` (for `x ≤ k+α` and `2k+5-ω ≤ y`)
in which the `t` turns around `γ` have been replaced by `u` turns.  This is the *spin
adjustment* of Section 5.2 of `anevsanseparationv4.tex`. -/
def slen (x y u : ℕ) : ℕ := (Str.p - x) + (u * Str.ell + Str.roff) + (y - Str.q)

/-- **Spin adjustment (Section 5.2 of `anevsanseparationv4.tex`)**: a walk segment
`W[x,y]` containing the stretch may be replaced by a path with any number `u` of turns
around `γ`. -/
theorem spanSeg {x y : ℕ} (hx : x ≤ Str.p) (hy : Str.q ≤ y)
    (hyn : y ≤ 3 * k + 7) (u : ℕ) : ∃ τ, Seg k c (c x) (c y) (Str.slen x y u) τ :=
  runPath Str.hell Str.hper Str.hlen Str.htt hx hy hyn u

/-- With `u = t` turns the spin adjusted segment is the walk segment `W[x,y]` itself. -/
theorem slen_tt {x y : ℕ} (hx : x ≤ Str.p) (hy : Str.q ≤ y) :
    Str.slen x y Str.tt = y - x := by
  have h := Str.hlen
  simp only [slen]
  omega

/-- `d₀ ≤ k+4`, since the stretch contains at least one turn. -/
theorem d0_le : Str.d0 ≤ k + 4 := by
  have h1 := Str.d0_add
  have ht := Str.htt
  have he := Str.hell
  have h2 : 1 ≤ Str.tt * Str.ell := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  omega

end Stretch

/-- **The moved `c`-edge test.**  This is the argument used over and over in Section 5.3
of `anevsanseparationv4.tex` ("its `c`-edge sits at position `2k+5+λ`, respectively
`2k+5-σλ`, whereas `W` reads `b` or a letter of the tail there").  If a second path has
the shape `W[0,k] · R⟨t'⟩ · π` with `π` beginning with the `c`-edge `e_{2k+5}` and
`t' ≠ m = k+5`, then it reads `c` at a position where `W` does not, so `W` is not
uniquely accepting. -/
theorem c_edge_moves (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (u L : ℕ) {τ₂ : ℕ → ℕ}
    (hrest : Seg k c (c (2 * k + 5)) (c (3 * k + 7)) L τ₂)
    (hL : 0 < L) (hτ₂0 : τ₂ 0 = 2 * k + 5)
    (hlen : k + (Str.d0 + u * Str.ell) + L = 3 * k + 7)
    (hne : Str.d0 + u * Str.ell ≠ k + 5) : False := by
  obtain ⟨τr, hτr⟩ := Str.runSeg hk u
  have s0 : Seg k c (c 0) (c k) k (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ k by omega) (by omega)
    simpa using h
  set r := Str.d0 + u * Str.ell with hr
  have hall := seg_cat s0 (seg_cat hτr hrest)
  rw [show k + (r + L) = 3 * k + 7 by omega] at hall
  refine no_second_path hk huaw hall (j := k + r) (by omega) ?_
  have hval : cat k (fun t => 0 + t) (cat r τr τ₂) (k + r) = 2 * k + 5 := by
    rw [cat_ge (by omega), show k + r - k = r by omega, cat_ge (by omega), Nat.sub_self,
      hτ₂0]
  rw [hval, zw_c rfl]
  rcases (by omega : k + r < 2 * k + 5 ∨ 2 * k + 6 ≤ k + r) with h | h
  · rw [zw_b (by omega) h]; simp
  · rcases (by omega : k + r < 3 * k + 5 ∨ k + r = 3 * k + 5 ∨ k + r = 3 * k + 6)
      with h' | h' | h'
    · rw [zw_a' h h']; simp
    · rw [zw_d (by omega) h']; simp
    · rw [zw_e h']; simp

/-- **Lemma 5.6(a) (Narrow surgeries, `lem:narrow`)** for a chord on the prefix side.
If `(i,j)` is a chord with `i < j ≤ k-1` whose length is divisible by `ℓ`, then skipping
it and lengthening the run by `j-i` produces a second accepting path: the walk is not
uniquely accepting. -/
theorem narrow_prefix_skip (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {i j : ℕ} (hij : i < j) (hjk : j < k) (heq : c i = c j)
    (hdvd : Str.ell ∣ (j - i)) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : j - i = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  obtain ⟨τr, hτr⟩ := Str.runSeg hk (Str.tt + u₀)
  have hlenR : Str.d0 + (Str.tt + u₀) * Str.ell = k + 5 + (j - i) := by
    have h1 := Str.d0_add
    rw [Nat.add_mul]
    omega
  have s1 : Seg k c (c 0) (c i) (i - 0) (fun t => 0 + t) := segW c (by omega) (by omega)
  rw [heq] at s1
  have s2 : Seg k c (c j) (c k) (k - j) (fun t => j + t) := segW c (by omega) (by omega)
  have s4 : Seg k c (c (2 * k + 5)) (c (3 * k + 7)) (3 * k + 7 - (2 * k + 5))
      (fun t => 2 * k + 5 + t) := segW c (by omega) (by omega)
  have hall := seg_cat s1 (seg_cat s2 (seg_cat hτr s4))
  have hL : i - 0 + (k - j + (Str.d0 + (Str.tt + u₀) * Str.ell + (3 * k + 7 - (2 * k + 5))))
      = 3 * k + 7 := by omega
  rw [hL] at hall
  refine no_second_path hk huaw hall (j := i) (by omega) ?_
  have hτi : cat (i - 0) (fun t => 0 + t)
      (cat (k - j) (fun t => j + t) (cat (Str.d0 + (Str.tt + u₀) * Str.ell) τr
        (fun t => 2 * k + 5 + t))) i = j := by
    rw [cat_ge (by omega), cat_lt (by omega)]
    omega
  rw [hτi, zw_a hjk, zw_a (show i < k by omega)]
  simp only [ne_eq, Ltr.a.injEq]
  omega

/-- **Lemma 5.6(a) (Narrow surgeries, `lem:narrow`)** for a chord on the tail side.
If `(i,j)` is a chord with `2k+6 ≤ i < j ≤ n` whose length is divisible by `ℓ`, then the
skip `W[0,k] R⟨m+λ⟩ W[2k+5,i] W[j,n]` is a second accepting path. -/
theorem narrow_tail_skip (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {i j : ℕ} (h2i : 2 * k + 6 ≤ i) (hij : i < j) (hjn : j ≤ 3 * k + 7)
    (heq : c i = c j) (hdvd : Str.ell ∣ (j - i)) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : j - i = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hlenR : Str.d0 + (Str.tt + u₀) * Str.ell = k + 5 + (j - i) := by
    have h1 := Str.d0_add
    rw [Nat.add_mul]
    omega
  have r1 : Seg k c (c (2 * k + 5)) (c i) (i - (2 * k + 5)) (fun t => 2 * k + 5 + t) :=
    segW c (by omega) (by omega)
  rw [heq] at r1
  have r2 : Seg k c (c j) (c (3 * k + 7)) (3 * k + 7 - j) (fun t => j + t) :=
    segW c (by omega) (by omega)
  exact c_edge_moves hk huaw Str (Str.tt + u₀) _ (seg_cat r1 r2) (by omega)
    (by rw [cat_lt (show (0 : ℕ) < i - (2 * k + 5) by omega)]) (by omega) (by omega)

/-- **Lemma 5.6(b) (Narrow surgeries, `lem:narrow`)** for a chord on the prefix side:
the `σ`-fold insertion `W[0,i] (W[i,j])^{σ+1} W[j,n]` with the run shortened by `σλ`. -/
theorem narrow_prefix_insert (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {i j σ : ℕ} (hij : i < j) (hjk : j < k) (heq : c i = c j)
    (hσ : 1 ≤ σ) (hdvd : Str.ell ∣ σ * (j - i)) (hle : σ * (j - i) ≤ Str.tt * Str.ell) :
    False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : σ * (j - i) = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hσpos : 0 < σ * (j - i) := Nat.mul_pos (by omega) (by omega)
  have hrun : Str.d0 + (Str.tt - u₀) * Str.ell + σ * (j - i) = k + 5 := by
    have h1 := Str.d0_add
    have h2 : u₀ * Str.ell ≤ Str.tt * Str.ell := by omega
    rw [Nat.sub_mul]
    omega
  obtain ⟨τr, hτr⟩ := Str.runSeg hk (Str.tt - u₀)
  have s1 : Seg k c (c 0) (c i) i (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ i by omega) (by omega)
    simpa using h
  have hloop : Seg k c (c i) (c i) (j - i) (fun t => i + t) := by
    have h := segW (k := k) c (show i ≤ j by omega) (by omega)
    rw [← heq] at h; exact h
  have sl := seg_repit hloop (σ + 1)
  have s2 : Seg k c (c j) (c k) (k - j) (fun t => j + t) := segW c (by omega) (by omega)
  rw [← heq] at s2
  have s4 : Seg k c (c (2 * k + 5)) (c (3 * k + 7)) (k + 2) (fun t => 2 * k + 5 + t) := by
    have h := segW (k := k) c (show 2 * k + 5 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (2 * k + 5) = k + 2 by omega] at h; exact h
  have hall := seg_cat s1 (seg_cat sl (seg_cat s2 (seg_cat hτr s4)))
  have hL : i + ((σ + 1) * (j - i) +
      (k - j + (Str.d0 + (Str.tt - u₀) * Str.ell + (k + 2)))) = 3 * k + 7 := by
    have : (σ + 1) * (j - i) = σ * (j - i) + (j - i) := by ring
    omega
  rw [hL] at hall
  refine no_second_path hk huaw hall (j := j) (by omega) ?_
  have hlt : j - i < (σ + 1) * (j - i) := by
    have : (σ + 1) * (j - i) = σ * (j - i) + (j - i) := by ring
    omega
  have hτj : cat i (fun t => 0 + t)
      (cat ((σ + 1) * (j - i)) (repit (σ + 1) (j - i) (fun t => i + t))
        (cat (k - j) (fun t => j + t)
          (cat (Str.d0 + (Str.tt - u₀) * Str.ell) τr (fun t => 2 * k + 5 + t)))) j = i := by
    rw [cat_ge (by omega), show j - i = j - i from rfl, cat_lt hlt, repit_at_period,
      repit_zero hσ (show 1 ≤ j - i by omega)]
    omega
  rw [hτj, zw_a hjk, zw_a (show i < k by omega)]
  simp only [ne_eq, Ltr.a.injEq]
  omega

/-- **Lemma 5.6(b) (Narrow surgeries, `lem:narrow`)** for a chord on the tail side. -/
theorem narrow_tail_insert (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {i j σ : ℕ} (h2i : 2 * k + 6 ≤ i) (hij : i < j)
    (hjn : j ≤ 3 * k + 7) (heq : c i = c j) (hσ : 1 ≤ σ)
    (hdvd : Str.ell ∣ σ * (j - i)) (hle : σ * (j - i) ≤ Str.tt * Str.ell) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : σ * (j - i) = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hσpos : 0 < σ * (j - i) := Nat.mul_pos (by omega) (by omega)
  have hrun : Str.d0 + (Str.tt - u₀) * Str.ell + σ * (j - i) = k + 5 := by
    have h1 := Str.d0_add
    have h2 : u₀ * Str.ell ≤ Str.tt * Str.ell := by omega
    rw [Nat.sub_mul]
    omega
  have r1 : Seg k c (c (2 * k + 5)) (c i) (i - (2 * k + 5)) (fun t => 2 * k + 5 + t) :=
    segW c (by omega) (by omega)
  have hloop : Seg k c (c i) (c i) (j - i) (fun t => i + t) := by
    have h := segW (k := k) c (show i ≤ j by omega) (by omega)
    rw [← heq] at h; exact h
  have sl := seg_repit hloop (σ + 1)
  have r2 : Seg k c (c j) (c (3 * k + 7)) (3 * k + 7 - j) (fun t => j + t) :=
    segW c (by omega) (by omega)
  rw [← heq] at r2
  have hexp : (σ + 1) * (j - i) = σ * (j - i) + (j - i) := by ring
  exact c_edge_moves hk huaw Str (Str.tt - u₀) _ (seg_cat r1 (seg_cat sl r2)) (by omega)
    (by rw [cat_lt (show (0 : ℕ) < i - (2 * k + 5) by omega)]) (by omega) (by omega)

/-- **Lemma 5.7(ii) (Wide chords, `lem:wide`)**: two wide chords `(j_a,j'_a)`,
`(j_b,j'_b)` with `j_a < j_b` and `j'_a > j'_b` give the *fold* path
`W[0,k] R⟨m-D⟩ e_{2k+5} W[2k+6,2k+6+j'_a] W[j_a,j_b] W[2k+6+j'_b,n]`, where
`D = (j'_a-j'_b)+(j_b-j_a)`. -/
theorem wide_chord_fold (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {ja jb ja' jb' : ℕ} (hab : ja < jb) (hbk : jb < k)
    (hja' : ja' ≤ k + 1) (hb'a' : jb' < ja')
    (heqa : c (2 * k + 6 + ja') = c ja) (heqb : c jb = c (2 * k + 6 + jb'))
    (hdvd : Str.ell ∣ ((ja' - jb') + (jb - ja)))
    (hle : (ja' - jb') + (jb - ja) ≤ Str.tt * Str.ell) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : (ja' - jb') + (jb - ja) = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hDpos : 0 < (ja' - jb') + (jb - ja) := by omega
  have hrun : Str.d0 + (Str.tt - u₀) * Str.ell + ((ja' - jb') + (jb - ja)) = k + 5 := by
    have h1 := Str.d0_add
    have h2 : u₀ * Str.ell ≤ Str.tt * Str.ell := by omega
    rw [Nat.sub_mul]
    omega
  have q1 : Seg k c (c (2 * k + 5)) (c (2 * k + 6 + ja')) (2 * k + 6 + ja' - (2 * k + 5))
      (fun t => 2 * k + 5 + t) := segW c (by omega) (by omega)
  rw [heqa] at q1
  have q2 : Seg k c (c ja) (c jb) (jb - ja) (fun t => ja + t) := segW c (by omega) (by omega)
  rw [heqb] at q2
  have q3 : Seg k c (c (2 * k + 6 + jb')) (c (3 * k + 7)) (3 * k + 7 - (2 * k + 6 + jb'))
      (fun t => 2 * k + 6 + jb' + t) := segW c (by omega) (by omega)
  exact c_edge_moves hk huaw Str (Str.tt - u₀) _ (seg_cat q1 (seg_cat q2 q3)) (by omega)
    (by rw [cat_lt (show (0 : ℕ) < 2 * k + 6 + ja' - (2 * k + 5) by omega)])
    (by omega) (by omega)

/-- **Corollary 5.8 (`cor:foldloop`)**, case `j < i < j'`: a wide chord `(j,j')` whose
shift is divisible by `ℓ` and which straddles an aligned index `i`. -/
theorem foldloop_lt (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {i j j' : ℕ} (hji : j < i) (hij' : i < j') (hj'k : j' ≤ k + 1)
    (hik : i < k) (halign : c i = c (2 * k + 6 + i)) (hwide : c j = c (2 * k + 6 + j'))
    (hdvd : Str.ell ∣ (j' - j)) (hle : j' - j ≤ Str.tt * Str.ell) : False := by
  refine wide_chord_fold hk huaw Str (ja := j) (jb := i) (ja' := j') (jb' := i)
    (by omega) hik hj'k (by omega) hwide.symm halign ?_ ?_
  · rwa [show j' - i + (i - j) = j' - j by omega]
  · rw [show j' - i + (i - j) = j' - j by omega]; exact hle

/-- **Corollary 5.8 (`cor:foldloop`)**, case `j' < i < j`. -/
theorem foldloop_gt (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {i j j' : ℕ} (hj'i : j' < i) (hij : i < j) (hjk : j < k)
    (halign : c i = c (2 * k + 6 + i)) (hwide : c j = c (2 * k + 6 + j'))
    (hdvd : Str.ell ∣ (j - j')) (hle : j - j' ≤ Str.tt * Str.ell) : False := by
  refine wide_chord_fold hk huaw Str (ja := i) (jb := j) (ja' := i) (jb' := j')
    (by omega) hjk (by omega) (by omega) halign.symm hwide ?_ ?_
  · rwa [show i - j' + (j - i) = j - j' by omega]
  · rw [show i - j' + (j - i) = j - j' by omega]; exact hle

/-- **Lemma 5.9 (Lassos, `lem:lasso`)** for `g_j = u_1`: the path
`W[0,i] W[2k+6+i,3k+6] W[j,n]` with the run replaced by `R⟨m-λ⟩`, `λ = k-j`. -/
theorem lasso_u1 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {i j : ℕ} (hji : j < i) (hik : i < k)
    (halign : c i = c (2 * k + 6 + i)) (hu : c j = c (3 * k + 6))
    (hdvd : Str.ell ∣ (k - j)) (hle : k - j ≤ Str.tt * Str.ell) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : k - j = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hrun : Str.d0 + (Str.tt - u₀) * Str.ell + (k - j) = k + 5 := by
    have h1 := Str.d0_add
    have h2 : u₀ * Str.ell ≤ Str.tt * Str.ell := by omega
    rw [Nat.sub_mul]
    omega
  obtain ⟨τr, hτr⟩ := Str.runSeg hk (Str.tt - u₀)
  have p1 : Seg k c (c 0) (c i) i (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ i by omega) (by omega)
    simpa using h
  rw [halign] at p1
  have p2 : Seg k c (c (2 * k + 6 + i)) (c (3 * k + 6)) (3 * k + 6 - (2 * k + 6 + i))
      (fun t => 2 * k + 6 + i + t) := segW c (by omega) (by omega)
  rw [← hu] at p2
  have p3 : Seg k c (c j) (c k) (k - j) (fun t => j + t) := segW c (by omega) (by omega)
  have p4 : Seg k c (c (2 * k + 5)) (c (3 * k + 7)) (k + 2) (fun t => 2 * k + 5 + t) := by
    have h := segW (k := k) c (show 2 * k + 5 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (2 * k + 5) = k + 2 by omega] at h; exact h
  have hall := seg_cat p1 (seg_cat p2 (seg_cat p3 (seg_cat hτr p4)))
  have hL : i + (3 * k + 6 - (2 * k + 6 + i) +
      (k - j + (Str.d0 + (Str.tt - u₀) * Str.ell + (k + 2)))) = 3 * k + 7 := by omega
  rw [hL] at hall
  refine no_second_path hk huaw hall (j := k) (by omega) ?_
  have hτk : cat i (fun t => 0 + t)
      (cat (3 * k + 6 - (2 * k + 6 + i)) (fun t => 2 * k + 6 + i + t)
        (cat (k - j) (fun t => j + t)
          (cat (Str.d0 + (Str.tt - u₀) * Str.ell) τr (fun t => 2 * k + 5 + t)))) k = j := by
    rw [cat_ge (by omega), cat_ge (by omega), cat_lt (by omega)]
    omega
  rw [hτk, zw_a (show j < k by omega), zw_b (le_refl k) (by omega)]
  simp

/-- **Lemma 5.9 (Lassos, `lem:lasso`)** for `g_j = u_2`: the path
`W[0,i] W[2k+6+i,n] W[j,n]` with the run replaced by `R⟨m-λ⟩`, `λ = k+1-j`. -/
theorem lasso_u2 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {i j : ℕ} (hji : j < i) (hik : i < k)
    (halign : c i = c (2 * k + 6 + i)) (hu : c j = c (3 * k + 7))
    (hdvd : Str.ell ∣ (k + 1 - j)) (hle : k + 1 - j ≤ Str.tt * Str.ell) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : k + 1 - j = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hrun : Str.d0 + (Str.tt - u₀) * Str.ell + (k + 1 - j) = k + 5 := by
    have h1 := Str.d0_add
    have h2 : u₀ * Str.ell ≤ Str.tt * Str.ell := by omega
    rw [Nat.sub_mul]
    omega
  obtain ⟨τr, hτr⟩ := Str.runSeg hk (Str.tt - u₀)
  have p1 : Seg k c (c 0) (c i) i (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ i by omega) (by omega)
    simpa using h
  rw [halign] at p1
  have p2 : Seg k c (c (2 * k + 6 + i)) (c (3 * k + 7)) (3 * k + 7 - (2 * k + 6 + i))
      (fun t => 2 * k + 6 + i + t) := segW c (by omega) (by omega)
  rw [← hu] at p2
  have p3 : Seg k c (c j) (c k) (k - j) (fun t => j + t) := segW c (by omega) (by omega)
  have p4 : Seg k c (c (2 * k + 5)) (c (3 * k + 7)) (k + 2) (fun t => 2 * k + 5 + t) := by
    have h := segW (k := k) c (show 2 * k + 5 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (2 * k + 5) = k + 2 by omega] at h; exact h
  have hall := seg_cat p1 (seg_cat p2 (seg_cat p3 (seg_cat hτr p4)))
  have hL : i + (3 * k + 7 - (2 * k + 6 + i) +
      (k - j + (Str.d0 + (Str.tt - u₀) * Str.ell + (k + 2)))) = 3 * k + 7 := by omega
  rw [hL] at hall
  refine no_second_path hk huaw hall (j := k + 1) (by omega) ?_
  have hτk : cat i (fun t => 0 + t)
      (cat (3 * k + 7 - (2 * k + 6 + i)) (fun t => 2 * k + 6 + i + t)
        (cat (k - j) (fun t => j + t)
          (cat (Str.d0 + (Str.tt - u₀) * Str.ell) τr (fun t => 2 * k + 5 + t)))) (k + 1) = j := by
    rw [cat_ge (by omega), cat_ge (by omega), cat_lt (by omega)]
    omega
  rw [hτk, zw_a (show j < k by omega), zw_b (by omega) (by omega)]
  simp

/-- **Lemma 5.6(c),(d) (Narrow surgeries, `lem:narrow`)**, prefix side.  Given a chord
`(a₁,a₂)` and a second chord `{x,y}`, both with all endpoints on the prefix side and
`a₁ < x`, the path `W[0,a₂] W[a₁,x] W[y,n]` (with the run inside the last segment
replaced by `R⟨d₀+uℓ⟩`) is a walk of the walk graph from `c₀` to `c_n`; if its length is
`n` it is a second accepting path.  Taking `(x,y) = (b₁,b₂)` gives the surgery `π₂`/`π₃`
of part (c), and `(x,y) = (b₂,b₁)` the double insertion of part (d). -/
theorem narrow_prefix_pair (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ x y u : ℕ} (h1 : a₁ < x) (h2 : a₁ < a₂) (h3 : a₂ < k)
    (hx : x ≤ k) (hy : y ≤ k) (ea : c a₁ = c a₂) (eb : c x = c y)
    (hlen : a₂ + ((x - a₁) + ((k - y) + ((Str.d0 + u * Str.ell) + (k + 2))))
      = 3 * k + 7) : False := by
  obtain ⟨τr, hτr⟩ := Str.runSeg hk u
  have s0 : Seg k c (c 0) (c a₂) a₂ (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ a₂ by omega) (by omega)
    simpa using h
  rw [← ea] at s0
  have s1 : Seg k c (c a₁) (c x) (x - a₁) (fun t => a₁ + t) := segW c (by omega) (by omega)
  rw [eb] at s1
  have s2 : Seg k c (c y) (c k) (k - y) (fun t => y + t) := segW c (by omega) (by omega)
  have s4 : Seg k c (c (2 * k + 5)) (c (3 * k + 7)) (k + 2) (fun t => 2 * k + 5 + t) := by
    have h := segW (k := k) c (show 2 * k + 5 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (2 * k + 5) = k + 2 by omega] at h; exact h
  have hall := seg_cat s0 (seg_cat s1 (seg_cat s2 (seg_cat hτr s4)))
  rw [hlen] at hall
  refine no_second_path hk huaw hall (j := a₂) (by omega) ?_
  have hτ : cat a₂ (fun t => 0 + t)
      (cat (x - a₁) (fun t => a₁ + t)
        (cat (k - y) (fun t => y + t)
          (cat (Str.d0 + u * Str.ell) τr (fun t => 2 * k + 5 + t)))) a₂ = a₁ := by
    rw [cat_ge (by omega), Nat.sub_self, cat_lt (by omega)]
    omega
  rw [hτ, zw_a (show a₁ < k by omega), zw_a h3]
  simp only [ne_eq, Ltr.a.injEq]
  omega

/-- **Lemma 5.6(c),(d) (Narrow surgeries, `lem:narrow`)**, tail side: the path
`W[0,k] R⟨d₀+uℓ⟩ W[2k+5,a₂] W[a₁,x] W[y,n]`. -/
theorem narrow_tail_pair (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ x y u : ℕ} (h2i : 2 * k + 6 ≤ a₁) (ha : a₁ < a₂)
    (ha2 : a₂ ≤ 3 * k + 7) (hax : a₁ ≤ x) (hx : x ≤ 3 * k + 7) (hy : y ≤ 3 * k + 7)
    (ea : c a₁ = c a₂) (eb : c x = c y)
    (hlen : k + (Str.d0 + u * Str.ell) +
      ((a₂ - (2 * k + 5)) + ((x - a₁) + (3 * k + 7 - y))) = 3 * k + 7)
    (hne : Str.d0 + u * Str.ell ≠ k + 5) : False := by
  have q1 : Seg k c (c (2 * k + 5)) (c a₂) (a₂ - (2 * k + 5)) (fun t => 2 * k + 5 + t) :=
    segW c (by omega) (by omega)
  rw [← ea] at q1
  have q2 : Seg k c (c a₁) (c x) (x - a₁) (fun t => a₁ + t) := segW c (by omega) (by omega)
  rw [eb] at q2
  have q3 : Seg k c (c y) (c (3 * k + 7)) (3 * k + 7 - y) (fun t => y + t) :=
    segW c (by omega) (by omega)
  exact c_edge_moves hk huaw Str u _ (seg_cat q1 (seg_cat q2 q3)) (by omega)
    (by rw [cat_lt (show (0 : ℕ) < a₂ - (2 * k + 5) by omega)]) (by omega) hne

/-- **Lemma 5.6(c),(d) (Narrow surgeries, `lem:narrow`)** for a prefix chord `(a₁,a₂)`
together with a tail chord `{x,y}`: the path `W[0,a₂] W[a₁,x] W[y,n]`, whose middle
segment contains the run. -/
theorem narrow_mixed_pair (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ x y u : ℕ} (ha : a₁ < a₂) (ha2 : a₂ < k)
    (hx : 2 * k + 6 ≤ x) (hx2 : x ≤ 3 * k + 7) (hy : y ≤ 3 * k + 7)
    (ea : c a₁ = c a₂) (eb : c x = c y)
    (hlen : a₂ + ((k - a₁) + ((Str.d0 + u * Str.ell) +
      ((x - (2 * k + 5)) + (3 * k + 7 - y)))) = 3 * k + 7) : False := by
  obtain ⟨τr, hτr⟩ := Str.runSeg hk u
  have s0 : Seg k c (c 0) (c a₂) a₂ (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ a₂ by omega) (by omega)
    simpa using h
  rw [← ea] at s0
  have s1 : Seg k c (c a₁) (c k) (k - a₁) (fun t => a₁ + t) := segW c (by omega) (by omega)
  have s2 : Seg k c (c (2 * k + 5)) (c x) (x - (2 * k + 5)) (fun t => 2 * k + 5 + t) :=
    segW c (by omega) (by omega)
  rw [eb] at s2
  have s3 : Seg k c (c y) (c (3 * k + 7)) (3 * k + 7 - y) (fun t => y + t) :=
    segW c (by omega) (by omega)
  have hall := seg_cat s0 (seg_cat s1 (seg_cat hτr (seg_cat s2 s3)))
  rw [hlen] at hall
  refine no_second_path hk huaw hall (j := a₂) (by omega) ?_
  have hτ : cat a₂ (fun t => 0 + t)
      (cat (k - a₁) (fun t => a₁ + t)
        (cat (Str.d0 + u * Str.ell) τr
          (cat (x - (2 * k + 5)) (fun t => 2 * k + 5 + t) (fun t => y + t)))) a₂ = a₁ := by
    rw [cat_ge (by omega), Nat.sub_self, cat_lt (by omega)]
    omega
  rw [hτ, zw_a (show a₁ < k by omega), zw_a ha2]
  simp only [ne_eq, Ltr.a.injEq]
  omega

/-- **Lemma 6.1 (Double passage, `lem:dichotomy`)**: if `d₀ ≤ 2` and `ℓ ∣ 4-2d₀`, then
the path that goes through the run twice, using the aligned index `i` to return from the
tail to `g_k`, is a second accepting path of length `n`. -/
theorem double_passage (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {i : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (hd0 : Str.d0 ≤ 2) (hdvd : Str.ell ∣ (4 - 2 * Str.d0)) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : 4 - 2 * Str.d0 = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  obtain ⟨τr, hτr⟩ := Str.runSeg hk u₀
  have s1 : Seg k c (c (2 * k + 5)) (c (2 * k + 6 + i)) (2 * k + 6 + i - (2 * k + 5))
      (fun t => 2 * k + 5 + t) := segW c (by omega) (by omega)
  rw [← halign] at s1
  have s2 : Seg k c (c i) (c k) (k - i) (fun t => i + t) := segW c (by omega) (by omega)
  have s3 : Seg k c (c (2 * k + 5)) (c (3 * k + 7)) (k + 2) (fun t => 2 * k + 5 + t) := by
    have h := segW (k := k) c (show 2 * k + 5 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (2 * k + 5) = k + 2 by omega] at h; exact h
  have hz : Str.d0 + 0 * Str.ell = Str.d0 := by ring
  exact c_edge_moves hk huaw Str 0 _ (seg_cat s1 (seg_cat s2 (seg_cat hτr s3))) (by omega)
    (by rw [cat_lt (show (0 : ℕ) < 2 * k + 6 + i - (2 * k + 5) by omega)])
    (by omega) (by omega)

/-- **Lemma 5.3(i) (`lem:gamma`)**, assembled from Step 1: for `k ≥ 18`, a uniquely
accepting walk for `z_k` with at most `k+5` states carries a stretch `S = [k+α, 2k+5-ω]`
on which the walk follows a simple cycle `γ` of length `ℓ ≤ 4`, containing at least one
full turn. -/
theorem exists_Stretch [DecidableEq S] (hk : 18 ≤ k)
    (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) :
    ∃ Str : Stretch k c, Str.ell ≤ 4 ∧ 4 ≤ Str.tt := by
  obtain ⟨ell, t₁, tr, h1, h2, h3, h4, h5, hmin⟩ := exists_stretch_min hk huaw hcard
  have hdm : (tr - t₁) / ell * ell + (tr - t₁) % ell = tr - t₁ := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have htt4 : 4 ≤ (tr - t₁) / ell := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  exact ⟨⟨ell, t₁, tr, (tr - t₁) / ell, (tr - t₁) % ell, h1, h2, h3, by omega, by omega, h5⟩,
    ell_le_four hk huaw hcard h1 h2 h3 h4 h5 hmin, htt4⟩

end

end AneVsAn
