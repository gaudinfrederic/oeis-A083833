import A083833
import A083838
import Spec_A083837

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A083838 - énoncé record des zéros de la suite image

`A083838(k) = k·A083837(k)+1` vaut `0` exactement là où A083837 vaut
`0` : l'image nulle signifie qu'aucun couple `(p, q)` de palindromes ne
vérifie `q = k·p+1`. Même zéro-ensemble `A083837zeros` (21 indices) ;
la b-file publiée (66 termes) n'en montre que les 12 premiers.
-/

open A083833

/-- Énoncé record : pour chaque `k` du zéro-ensemble, il n'existe aucun
couple `(p, q)` de palindromes avec `q = k·p+1` - l'image `A083838(k)`
est `0` universellement. -/
abbrev SpecA083838 : Prop :=
  ∀ k, k ∈ A083837zeros →
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = k * p + 1
