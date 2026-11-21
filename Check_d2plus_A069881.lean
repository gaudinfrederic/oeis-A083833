import A069881

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_d2plus_A069881 - ancres de la LISTE (membres / non-membres)

Verbatim OEIS : « Numbers n such that n and 2n+1 are both
palindromes ». La fiche est une ENUMERATION (offset 1 : les
termes eux-memes), pas une fonction « smallest k » : la clause
a corriger est donc l'ancrage des valeurs listees - membres
certifies `IsMember` et non-membres certifies `¬ IsMember` -
que la classification structurelle du module (theoremes
`A069881_even`, `A069881_overflow`) ne livre pas.

`IsMember p : ∃ m m', IsPal p m ∧ IsPal (2*p+1) m'` reprend le
predicat exact du module (`A069881.IsPal`, deux longueurs
libres : le cas `m' = m + 1` des repdigits `55...5` est couvert
par les ancres 55, 555, 5555).

- membres : p ∈ {1, 2, 3, 4, 5, 55, 151, 161, 171, 181, 191,
  252, 262, 555, 5555, 15051, 15151} - conformes a la section
  DATA (1,2,3,4,5,55,151,161,171,181,191,252,262,272,...,555,
  5555,15051,15151,...) ;
- non-membres : p ∈ {6,...,15, 16, 49, 56, 57, 100, 150, 152}
  (pour 16 et 49 le defaut est cote `p` : 2p+1 = 33, 99 sont
  bien palindromes).

Aucune completude d'enumeration n'est revendiquee : ce sont des
ancres finies, la classification reste celle du module.
-/

namespace CheckD2plusA069881

/-- Appartenance a la fiche : `p` palindrome ET `2p+1` palindrome
(longueurs libres pour couvrir le debordement `m' = m+1`). -/
def IsMember (p : ℕ) : Prop :=
  ∃ m m' : ℕ, A069881.IsPal p m ∧ A069881.IsPal (2 * p + 1) m'

/-- La longueur d'un palindrome est unique : `10^(m-1) ≤ p < 10^m`
force `m = L`. -/
theorem len_eq {p m L : ℕ} (h : A069881.IsPal p m)
    (hlo : 10 ^ (L - 1) ≤ p) (hhi : p < 10 ^ L) : m = L := by
  have hlo' := h.lo
  have hhi' := h.hi
  have h1 : m - 1 < L := by
    by_contra hc
    push_neg at hc
    have : 10 ^ L ≤ 10 ^ (m - 1) := pow_le_pow_right' (by norm_num) hc
    omega
  have h2 : L - 1 < m := by
    by_contra hc
    push_neg at hc
    have : 10 ^ m ≤ 10 ^ (L - 1) := pow_le_pow_right' (by norm_num) hc
    omega
  omega

-- ------------------------------------------------------------------
-- Ancres MEMBRES (termes de la fiche)
-- ------------------------------------------------------------------

theorem mem_1 : IsMember 1 :=
  ⟨1, 1, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_2 : IsMember 2 :=
  ⟨1, 1, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_3 : IsMember 3 :=
  ⟨1, 1, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_4 : IsMember 4 :=
  ⟨1, 1, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

/-- `5 -> 11` : les deux palindromes, longueurs `1` et `2`. -/
theorem mem_5 : IsMember 5 :=
  ⟨1, 2, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

/-- `55 -> 111` : debordement `m' = m + 1` (cas repdigit). -/
theorem mem_55 : IsMember 55 :=
  ⟨2, 3, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_151 : IsMember 151 :=
  ⟨3, 3, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_161 : IsMember 161 :=
  ⟨3, 3, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_171 : IsMember 171 :=
  ⟨3, 3, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_181 : IsMember 181 :=
  ⟨3, 3, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_191 : IsMember 191 :=
  ⟨3, 3, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_252 : IsMember 252 :=
  ⟨3, 3, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_262 : IsMember 262 :=
  ⟨3, 3, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

/-- `555 -> 1111` : debordement `m' = m + 1`. -/
theorem mem_555 : IsMember 555 :=
  ⟨3, 4, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

/-- `5555 -> 11111` : debordement `m' = m + 1`. -/
theorem mem_5555 : IsMember 5555 :=
  ⟨4, 5, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_15051 : IsMember 15051 :=
  ⟨5, 5, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

theorem mem_15151 : IsMember 15151 :=
  ⟨5, 5, ⟨by decide, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, by norm_num⟩⟩

-- ------------------------------------------------------------------
-- Ancres NON-MEMBRES : `2p+1` non palindrome (unites ≠ tete)
-- ------------------------------------------------------------------

theorem notmem_6 : ¬ IsMember 6 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 2 := len_eq (L := 2) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_7 : ¬ IsMember 7 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 2 := len_eq (L := 2) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_8 : ¬ IsMember 8 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 2 := len_eq (L := 2) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_9 : ¬ IsMember 9 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 2 := len_eq (L := 2) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_10 : ¬ IsMember 10 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 2 := len_eq (L := 2) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_11 : ¬ IsMember 11 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 2 := len_eq (L := 2) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_12 : ¬ IsMember 12 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 2 := len_eq (L := 2) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_13 : ¬ IsMember 13 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 2 := len_eq (L := 2) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_14 : ¬ IsMember 14 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 2 := len_eq (L := 2) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_15 : ¬ IsMember 15 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 2 := len_eq (L := 2) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

/-- `16 -> 33` : l'image est palindrome, mais `16` ne l'est pas. -/
theorem notmem_16 : ¬ IsMember 16 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m = 2 := len_eq (L := 2) h1 (by norm_num) (by norm_num)
  have hs := h1.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m)
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

/-- `49 -> 99` : l'image est palindrome, mais `49` ne l'est pas. -/
theorem notmem_49 : ¬ IsMember 49 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m = 2 := len_eq (L := 2) h1 (by norm_num) (by norm_num)
  have hs := h1.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m)
  rw [hm, show 2 - 1 - 0 = 1 by norm_num] at hs
  exact absurd hs (by decide)

/-- `56 -> 113` : chiffre des unites `3` ≠ chiffre de tete `1`. -/
theorem notmem_56 : ¬ IsMember 56 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 3 := len_eq (L := 3) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 3 - 1 - 0 = 2 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_57 : ¬ IsMember 57 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 3 := len_eq (L := 3) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 3 - 1 - 0 = 2 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_100 : ¬ IsMember 100 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 3 := len_eq (L := 3) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 3 - 1 - 0 = 2 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_150 : ¬ IsMember 150 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 3 := len_eq (L := 3) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 3 - 1 - 0 = 2 by norm_num] at hs
  exact absurd hs (by decide)

theorem notmem_152 : ¬ IsMember 152 := by
  rintro ⟨m, m', h1, h2⟩
  have hm : m' = 3 := len_eq (L := 3) h2 (by norm_num) (by norm_num)
  have hs := h2.sym 0 (by rw [hm]; norm_num : (0:ℕ) < m')
  rw [hm, show 3 - 1 - 0 = 2 by norm_num] at hs
  exact absurd hs (by decide)

end CheckD2plusA069881

#print axioms CheckD2plusA069881.mem_55
#print axioms CheckD2plusA069881.notmem_16
#print axioms CheckD2plusA069881.len_eq
