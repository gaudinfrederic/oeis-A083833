import Spec_A083829
import A083829

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A083829 : fermeture Spec↔preuve (Option B)

Le Spec (`Spec_A083829.lean`) ne contient aucune preuve ; ce
fichier vérifie que les théorèmes compilés satisfont EXACTEMENT
les quatre énoncés de la spec, dans l'ordre de la conjonction
(P1, P2, P3, P4). Les théorèmes vivent dans le namespace
`A083829` du module homonyme.
-/

/-- Les preuves compilées satisfont les énoncés record P1-P4. -/
theorem proven_A083829 : SpecA083829 :=
  ⟨A083829.A083829_even, A083829.A083829_prefix,
    A083829.A083829_digits, A083829.A083829_seven⟩

#print axioms proven_A083829
