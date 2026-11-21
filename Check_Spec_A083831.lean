import Spec_A083831
import A083831

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A083831 : fermeture Spec↔preuve (Option B)

Le Spec (`Spec_A083831.lean`) ne contient aucune preuve ; ce
fichier vérifie que les théorèmes compilés satisfont EXACTEMENT
les deux énoncés de la spec, dans l'ordre de la conjonction
(E `A083831_even`, D `A083831_digits`). Les théorèmes vivent
dans le namespace `A083831` du module homonyme.
-/

/-- Les preuves compilées satisfont les énoncés record E-D. -/
theorem proven_A083831 : SpecA083831 :=
  ⟨A083831.A083831_even, A083831.A083831_digits⟩

#print axioms proven_A083831
