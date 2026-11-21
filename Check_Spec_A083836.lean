import Spec_A083836
import A083835

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A083836 : fermeture Spec↔preuve (Option B)

Le Spec (`Spec_A083836.lean`) ne contient aucune preuve ; ce
fichier vérifie que les théorèmes compilés satisfont EXACTEMENT
les deux énoncés de la spec, dans l'ordre de la conjonction
(alphabet `A083836_digits`, forme paire `A083836_form`). Les
théorèmes vivent dans le namespace `A083835` du module homonyme
(théorèmes compagnons de la suite image A083836).
-/

/-- Les preuves compilées satisfont les énoncés record. -/
theorem proven_A083836 : SpecA083836 :=
  ⟨A083835.A083836_digits, A083835.A083836_form⟩

#print axioms proven_A083836
