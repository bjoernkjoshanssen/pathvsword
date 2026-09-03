import RequestProject.Defs
import RequestProject.UpperExact
import RequestProject.UpperUnique
import RequestProject.Lower

/-!
# Theorem 1.2 of `anevsanseparationv4.tex`

**Main Theorem (`thm:main`).**  For every `k ≥ 3` with `k ≡ 0 (mod 3)`, let
`z_k = a_1 a_2 ⋯ a_k b^{k+5} c a_1 a_2 ⋯ a_{k-1} d e`
(of length `n = 3k+7`, over the alphabet `Σ_k = {a_1,…,a_k,b,c,d,e}` of `k+4`
letters).  Then `A_{Ne}(z_k) ≤ k+5 < k+6 = A_N(z_k)`.

Here `A_{Ne}` and `A_N` are the exact and unique nondeterministic automatic
complexities of Definition 1.1 (`def:complexities`), and `z_k` is the word `zw k`
of length `wlen k = 3k+7`.
-/

namespace AneVsAn

set_option autoImplicit false

/-- **Theorem 1.2 (Main Theorem, `thm:main`)** of `anevsanseparationv4.tex`:
for every `k ≥ 3` with `k ≡ 0 (mod 3)`,
`A_{Ne}(z_k) ≤ k+5 < k+6 = A_N(z_k)`. -/
theorem main_theorem {k : ℕ} (hk : 3 ≤ k) (hk3 : k % 3 = 0) :
    ANe (wlen k) (zw k) ≤ k + 5 ∧ k + 5 < k + 6 ∧ AN (wlen k) (zw k) = k + 6 :=
  ⟨ANe_upper hk, by omega, le_antisymm (AN_upper hk) (AN_lower hk hk3)⟩

/-- **Theorem 1.2 (`thm:main`)**, stated as the strict separation
`A_{Ne}(z_k) < A_N(z_k)`. -/
theorem ANe_lt_AN {k : ℕ} (hk : 3 ≤ k) (hk3 : k % 3 = 0) :
    ANe (wlen k) (zw k) < AN (wlen k) (zw k) := by
  obtain ⟨h1, h2, h3⟩ := main_theorem hk hk3
  omega

end AneVsAn
