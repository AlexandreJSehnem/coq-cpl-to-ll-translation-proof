From CPL Require Export b_soundness.
From NanoYalla Require Import macrollcut.

Import LLNotations.

Variable trAtom : Atom.

Definition translate_atom (a:PropVars) := trAtom.

Fixpoint cpl_to_ll (a: PropF) : formula :=
match a with
  | Var A => wn (oc (var (translate_atom A)))
  | Disj A B => parr (cpl_to_ll A) (cpl_to_ll B)
  | Impl A Bot => wn (dual (cpl_to_ll A))
  | Bot => bot
  | Conj A B => cpl_to_ll ( Neg ( Disj (Neg A) (Neg B)))
end.

