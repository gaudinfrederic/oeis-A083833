import A083833
import A083837
import Spec_A083837

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVacuite_A083837 - non-vacuité et ancrage

Contrôles d'honnêteté pour le paquet A083837 :

* N3.1 satisfiabilité : des `k` voisins ont des témoins - `a(11) = 55`
  (`11·55+1 = 606` palindrome) et `a(5) = 1` (`5·1+1 = 6`) - la famille
  n'est pas vide, l'obstruction discrimine réellement.
* N3.2 ancrage `decide` : conventions `dgt`/`revW`/`escapesIn` sur
  valeurs litigieuses (inversion de chiffres, overflow de longueur).
* N3.3 ablation : les petits cas exclus à la main (m = 1, 2) ne sont
  effectivement pas palindromiques.
* N3.4 le zéro-ensemble affiché compte exactement 21 indices.
-/

open A083833
open A083837

namespace CheckAntiVacA083837

-- N3.1 : témoins voisins (k = 5, 11 non nuls dans la fiche)
theorem sat_wit_11 : ∃ p m m', IsPal p m ∧ IsPal (11 * p + 1) m' :=
  ⟨55, 2, 3, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

theorem sat_wit_5 : ∃ p m m', IsPal p m ∧ IsPal (5 * p + 1) m' :=
  ⟨1, 1, 1, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

-- N3.2 : ancrage des conventions
example : dgt 606 0 = 6 := by decide
example : dgt 606 2 = 6 := by decide
example : revW 1 7 = 7 := by decide
example : revW 2 19 = 91 := by decide
example : revW 3 654 = 456 := by decide
example : revW 2 5 = 50 := by decide

-- N3.2 bis : `escapesIn` discrimine - pour `k = 11` (qui a des témoins),
-- presque tous les préfixes échappent au certificat ; pour un `k`
-- certifié, la liste est vide.
example : escapesIn 11 1 2 (List.range' 1 9) = [1, 2, 3, 4, 5, 6, 7, 8] := by decide
example : escapesIn 12 1 2 (List.range' 1 9) = [] := by decide
example : escapesIn 48 3 2 (List.range' 190 10) = [] := by decide
example : escapesIn 79 3 2 (List.range' 650 10) = [] := by decide

-- N3.3 : les petits palindromes-candidats exclus à la main
example : dgt 35 0 ≠ dgt 35 1 := by decide  -- k=17, m=1 : 17·2+1 = 35
example : dgt 24 0 ≠ dgt 24 1 := by decide  -- k=23, m=1 : 23·1+1 = 24
example : dgt 445 0 ≠ dgt 445 2 := by decide  -- k=74, m=1 : 74·6+1 = 445
example : dgt 667 0 ≠ dgt 667 2 := by decide  -- k=74, m=1 : 74·9+1 = 667
example : dgt 516 0 ≠ dgt 516 2 := by decide  -- k=103, m=1 : 103·5+1 = 516
example : dgt 475 0 ≠ dgt 475 2 := by decide  -- k=79, m=1 : 79·6+1 = 475
example : dgt 49 0 ≠ dgt 49 1 := by decide  -- k=48, m=1 : 48·1+1 = 49
example : dgt 19 0 ≠ dgt 19 1 := by decide  -- k=48, m=2 : p = 19
example : dgt 65 0 ≠ dgt 65 1 := by decide  -- k=79, m=2 : p = 65

-- N3.4 : cardinal du zéro-ensemble
example : A083837zeros.length = 21 := by decide

end CheckAntiVacA083837
