import A083833
import A083837

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A083837 - énoncé record des 21 zéros affichés

Le `Spec` de la mission A083837 : chaque zéro `a(k) = 0` affiché dans
la fiche OEIS (borne de recherche `10^15`, commentaire Chandler 2003)
est en réalité une inexistence universelle - il n'existe aucun
palindrome `p` avec `k·p+1` palindrome.

* `A083837zeros` : les 21 indices nuls de la fiche (k = 1..104).
* `SpecA083837` : la conjonction des 21 énoncés d'inexistence.
-/

open A083833

/-- Zéros affichés de la fiche A083837 (k = 1..104). -/
def A083837zeros : List ℕ :=
  [12, 17, 23, 31, 37, 41, 42, 48, 51, 53,
   61, 64, 71, 74, 79, 81, 86, 91, 96, 101, 103]

/-- Énoncé record : pour chaque `k` du zéro-ensemble affiché, il
n'existe aucun palindrome `p` avec `k·p+1` palindrome. -/
abbrev SpecA083837 : Prop :=
  ∀ k, k ∈ A083837zeros →
    ¬ ∃ p m m', IsPal p m ∧ IsPal (k * p + 1) m'
