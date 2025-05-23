-- simpler impossible
namespace Regex
inductive Regex where
  | ε
  | char (c : Char)
  | altrn (rx₁ rx₂ : Regex)
  | conct (rx₁ rx₂ : Regex)
  | klosr (rx : Regex)
deriving Repr, Inhabited

-- (Inicially) i'll treat regex as booleans
-- preds.
open Regex in
def fitsIn (str : String) (rx : Regex) : Bool :=
  match rx with
  | ε => str == ""
  | char c => str == c.toString
  | altrn rx₁ rx₂ => fitsIn str rx₁ || fitsIn str rx₂
  | conct rx₁ rx₂ => sorry -- complicado
  | klosr rx => sorry      -- complicado
end Regex

